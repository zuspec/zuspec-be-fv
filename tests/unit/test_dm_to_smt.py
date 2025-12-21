"""
Tests for Data Model to SMT translation.
"""
import pytest
import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')
sys.path.insert(0, 'packages/zuspec-be-fv/tests/unit')

import zuspec.dataclasses as zdc
from zuspec.be.fv.translator import DataModelTranslator, SMTProblem
from conftest import get_struct_type


@pytest.fixture
def translator():
    """Create a DataModelTranslator instance."""
    return DataModelTranslator()


def test_smt_problem_basic():
    """Test basic SMTProblem functionality."""
    problem = SMTProblem()
    
    assert len(problem.variables) == 0
    assert len(problem.constraints) == 0
    assert len(problem.field_info) == 0


def test_smt_problem_add_variable():
    """Test adding variables to SMTProblem."""
    import z3
    problem = SMTProblem()
    
    var = z3.BitVec('test', 32)
    info = {'type': 'int', 'width': 32}
    
    problem.add_variable('test', var, info)
    
    assert 'test' in problem.variables
    assert problem.variables['test'] == var
    assert problem.field_info['test'] == info


def test_smt_problem_add_constraint():
    """Test adding constraints to SMTProblem."""
    import z3
    problem = SMTProblem()
    
    var = z3.BitVec('x', 32)
    constraint = var > 0
    
    problem.add_constraint(constraint)
    
    assert len(problem.constraints) == 1
    assert problem.constraints[0] == constraint


def test_translate_simple_struct(translator):
    """Test translating a simple struct with one field."""
    
    @zdc.dataclass
    class SimpleStruct(zdc.Struct):
        value: zdc.uint32_t = zdc.field(bounds=(0, 100))
    
    # Get data model
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(SimpleStruct)
    struct_type = get_struct_type(context, SimpleStruct)
    
    # Translate
    problem = translator.translate_struct(struct_type)
    
    # Check variable created
    assert 'value' in problem.variables
    assert 'value' in problem.field_info
    assert problem.field_info['value']['width'] == 32
    
    # Check bounds constraint added
    assert len(problem.constraints) == 1


def test_translate_struct_with_multiple_fields(translator):
    """Test translating struct with multiple bounded fields."""
    
    @zdc.dataclass
    class MultiFieldStruct(zdc.Struct):
        addr: zdc.uint32_t = zdc.field(bounds=(0, 0xFFFF))
        size: zdc.uint8_t = zdc.field(bounds=(1, 128))
        count: zdc.uint16_t = zdc.field(bounds=(1, 1024))
    
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(MultiFieldStruct)
    struct_type = get_struct_type(context, MultiFieldStruct)
    
    problem = translator.translate_struct(struct_type)
    
    # Check all variables created
    assert 'addr' in problem.variables
    assert 'size' in problem.variables
    assert 'count' in problem.variables
    
    # Check field info
    assert problem.field_info['addr']['width'] == 32
    assert problem.field_info['size']['width'] == 8
    assert problem.field_info['count']['width'] == 16
    
    # Should have 3 constraints (one per bounded field)
    assert len(problem.constraints) == 3


def test_translate_struct_no_bounds(translator):
    """Test translating struct with fields but no bounds."""
    
    @zdc.dataclass
    class NoBoundsStruct(zdc.Struct):
        value: zdc.uint32_t
    
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(NoBoundsStruct)
    struct_type = get_struct_type(context, NoBoundsStruct)
    
    problem = translator.translate_struct(struct_type)
    
    # Variable should exist
    assert 'value' in problem.variables
    
    # No constraints (no bounds specified)
    assert len(problem.constraints) == 0


def test_extract_field_bounds(translator):
    """Test extracting bounds metadata from struct."""
    
    @zdc.dataclass
    class BoundedStruct(zdc.Struct):
        low: zdc.uint8_t = zdc.field(bounds=(0, 50))
        high: zdc.uint8_t = zdc.field(bounds=(51, 100))
        unbounded: zdc.uint32_t
    
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(BoundedStruct)
    struct_type = get_struct_type(context, BoundedStruct)
    
    bounds = translator.extract_field_bounds(struct_type, BoundedStruct)
    
    assert 'low' in bounds
    assert bounds['low'] == (0, 50)
    assert 'high' in bounds
    assert bounds['high'] == (51, 100)
    assert 'unbounded' not in bounds


def test_translate_signed_field(translator):
    """Test translating signed integer field."""
    
    @zdc.dataclass
    class SignedStruct(zdc.Struct):
        offset: zdc.int32_t = zdc.field(bounds=(-100, 100))
    
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(SignedStruct)
    struct_type = get_struct_type(context, SignedStruct)
    
    problem = translator.translate_struct(struct_type)
    
    assert 'offset' in problem.variables
    assert problem.field_info['offset']['signed'] is True
    assert len(problem.constraints) == 1


def test_translate_with_verification(translator):
    """Test that translated constraints can be checked with Z3."""
    import z3
    
    @zdc.dataclass
    class VerifiableStruct(zdc.Struct):
        x: zdc.uint8_t = zdc.field(bounds=(10, 20))
        y: zdc.uint8_t = zdc.field(bounds=(30, 40))
    
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(VerifiableStruct)
    struct_type = get_struct_type(context, VerifiableStruct)
    
    problem = translator.translate_struct(struct_type)
    
    # Create solver and add constraints
    solver = z3.Solver()
    for constraint in problem.constraints:
        solver.add(constraint)
    
    # Should be satisfiable
    assert solver.check() == z3.sat
    
    # Get model
    model = solver.model()
    x_val = model[problem.variables['x']].as_long()
    y_val = model[problem.variables['y']].as_long()
    
    # Values should be in bounds
    assert 10 <= x_val <= 20
    assert 30 <= y_val <= 40

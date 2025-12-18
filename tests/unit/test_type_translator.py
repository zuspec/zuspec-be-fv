"""
Tests for type translator.
"""
import z3
from zuspec.be.fv.translator import TypeTranslator


def test_translate_int_type():
    """Test translation of integer types to BitVec."""
    translator = TypeTranslator()
    
    var = translator.translate_int_type('x', 32, signed=False)
    
    assert isinstance(var, z3.BitVecRef)
    assert var.size() == 32
    assert str(var) == 'x'


def test_translate_bool_type():
    """Test translation of boolean type."""
    translator = TypeTranslator()
    
    var = translator.translate_bool_type('flag')
    
    assert isinstance(var, z3.BoolRef)
    assert str(var) == 'flag'


def test_translate_array_type():
    """Test translation of array/memory types."""
    translator = TypeTranslator()
    
    mem = translator.translate_array_type('mem', addr_width=32, data_width=8)
    
    assert isinstance(mem, z3.ArrayRef)


def test_create_bounds_constraint_unsigned():
    """Test creating bounds constraints for unsigned values."""
    translator = TypeTranslator()
    
    var = z3.BitVec('x', 32)
    constraint = translator.create_bounds_constraint(var, 0, 100, is_signed=False)
    
    # Verify constraint is satisfiable within bounds
    solver = z3.Solver()
    solver.add(constraint)
    solver.add(var == 50)
    assert solver.check() == z3.sat
    
    # Verify constraint is violated outside bounds
    solver.reset()
    solver.add(constraint)
    solver.add(var == 150)
    assert solver.check() == z3.unsat


def test_create_bounds_constraint_signed():
    """Test creating bounds constraints for signed values."""
    translator = TypeTranslator()
    
    var = z3.Int('x')
    constraint = translator.create_bounds_constraint(var, -10, 10, is_signed=True)
    
    solver = z3.Solver()
    solver.add(constraint)
    solver.add(var == 5)
    assert solver.check() == z3.sat
    
    solver.reset()
    solver.add(constraint)
    solver.add(var == -5)
    assert solver.check() == z3.sat
    
    solver.reset()
    solver.add(constraint)
    solver.add(var == 20)
    assert solver.check() == z3.unsat


def test_get_bit_width_for_type():
    """Test extracting bit widths from type names."""
    translator = TypeTranslator()
    
    assert translator.get_bit_width_for_type('uint8_t') == 8
    assert translator.get_bit_width_for_type('uint16_t') == 16
    assert translator.get_bit_width_for_type('uint32_t') == 32
    assert translator.get_bit_width_for_type('uint64_t') == 64
    assert translator.get_bit_width_for_type('int8_t') == 8
    assert translator.get_bit_width_for_type('int32_t') == 32
    assert translator.get_bit_width_for_type('bool') == 1
    assert translator.get_bit_width_for_type('unknown') is None


def test_is_signed_type():
    """Test detection of signed types."""
    translator = TypeTranslator()
    
    assert translator.is_signed_type('int8_t') is True
    assert translator.is_signed_type('int32_t') is True
    assert translator.is_signed_type('uint8_t') is False
    assert translator.is_signed_type('uint32_t') is False
    assert translator.is_signed_type('bool') is False


def test_multiple_variables():
    """Test creating multiple variables with different types."""
    translator = TypeTranslator()
    
    x = translator.translate_int_type('x', 32)
    y = translator.translate_int_type('y', 16)
    flag = translator.translate_bool_type('flag')
    
    assert x.size() == 32
    assert y.size() == 16
    assert isinstance(flag, z3.BoolRef)
    
    # Verify they're independent
    solver = z3.Solver()
    solver.add(translator.create_bounds_constraint(x, 0, 100))
    solver.add(translator.create_bounds_constraint(y, 0, 50))
    solver.add(flag)
    
    assert solver.check() == z3.sat
    model = solver.model()
    assert 0 <= model[x].as_long() <= 100
    assert 0 <= model[y].as_long() <= 50
    assert model[flag]

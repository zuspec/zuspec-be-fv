"""
Tests for BoundsAnalyzer.
"""
import pytest
import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')
sys.path.insert(0, 'packages/zuspec-be-fv/tests/unit')

import zuspec.dataclasses as zdc
from zuspec.be.fv.analysis import BoundsAnalyzer
from zuspec.be.fv.solver import SolverResult
from conftest import get_struct_type


@pytest.fixture
def analyzer():
    """Create a BoundsAnalyzer instance."""
    return BoundsAnalyzer()


def test_check_memory_access_safe(analyzer):
    """Test checking a safe memory access."""
    
    @zdc.dataclass
    class SafeAccess(zdc.Struct):
        base: zdc.uint32_t = zdc.field(bounds=(0, 0x1000))
        size: zdc.uint32_t = zdc.field(bounds=(1, 0x100))
    
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(SafeAccess)
    struct_type = get_struct_type(context, SafeAccess)
    
    # Check that base + size <= 0x2000 (should be safe given constraints)
    result = analyzer.check_memory_access('base', 'size', 0x2000, struct_type)
    
    # Property holds - no violation possible
    assert result.holds is True
    assert result.result == SolverResult.UNSAT
    assert result.solver_name == "z3"


def test_check_memory_access_violation(analyzer):
    """Test detecting a memory bounds violation."""
    
    @zdc.dataclass
    class UnsafeAccess(zdc.Struct):
        base: zdc.uint32_t = zdc.field(bounds=(0, 0xFFFF))
        size: zdc.uint32_t = zdc.field(bounds=(1, 0x1000))
    
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(UnsafeAccess)
    struct_type = get_struct_type(context, UnsafeAccess)
    
    # Check that base + size <= 0x1000 (violation possible)
    result = analyzer.check_memory_access('base', 'size', 0x1000, struct_type)
    
    # Violation found
    assert result.holds is False
    assert result.result == SolverResult.SAT
    assert result.counterexample is not None
    
    # Counterexample should show values that violate bounds
    cex = result.counterexample
    assert 'base' in cex
    assert 'size' in cex
    
    # Verify counterexample actually violates
    base_val = cex['base']
    size_val = cex['size']
    assert base_val + size_val > 0x1000


def test_check_memory_access_tight_bounds(analyzer):
    """Test memory access with tight bounds."""
    
    @zdc.dataclass
    class TightBounds(zdc.Struct):
        base: zdc.uint16_t = zdc.field(bounds=(0, 100))
        size: zdc.uint8_t = zdc.field(bounds=(1, 10))
    
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(TightBounds)
    struct_type = get_struct_type(context, TightBounds)
    
    # Check base + size <= 150 (should be safe: max is 100 + 10 = 110)
    result = analyzer.check_memory_access('base', 'size', 150, struct_type)
    
    assert result.holds is True
    assert result.result == SolverResult.UNSAT


def test_check_no_overflow_safe(analyzer):
    """Test overflow check when no overflow possible."""
    
    @zdc.dataclass
    class NoOverflow(zdc.Struct):
        a: zdc.uint8_t = zdc.field(bounds=(0, 100))
        b: zdc.uint8_t = zdc.field(bounds=(0, 100))
    
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(NoOverflow)
    struct_type = get_struct_type(context, NoOverflow)
    
    # Check a + b for overflow (max is 200, fits in uint8 range after consideration)
    # Actually, uint8 max is 255, so 100 + 100 = 200 is safe
    result = analyzer.check_no_overflow('a', 'b', struct_type)
    
    # Should report no overflow possible
    assert result.holds is True
    assert result.result == SolverResult.UNSAT


def test_check_no_overflow_possible(analyzer):
    """Test overflow check when overflow is possible."""
    
    @zdc.dataclass
    class CanOverflow(zdc.Struct):
        a: zdc.uint8_t = zdc.field(bounds=(200, 250))
        b: zdc.uint8_t = zdc.field(bounds=(50, 100))
    
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(CanOverflow)
    struct_type = get_struct_type(context, CanOverflow)
    
    # Check a + b for overflow (max is 250 + 100 = 350 > 255)
    result = analyzer.check_no_overflow('a', 'b', struct_type)
    
    # Overflow is possible
    assert result.holds is False
    assert result.result == SolverResult.SAT
    assert result.counterexample is not None


def test_check_non_overlapping_safe(analyzer):
    """Test non-overlapping regions check when regions don't overlap."""
    
    @zdc.dataclass
    class NonOverlapping(zdc.Struct):
        src_base: zdc.uint32_t = zdc.field(bounds=(0, 0x1000))
        src_size: zdc.uint32_t = zdc.field(bounds=(1, 0x100))
        dst_base: zdc.uint32_t = zdc.field(bounds=(0x2000, 0x3000))
        dst_size: zdc.uint32_t = zdc.field(bounds=(1, 0x100))
    
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(NonOverlapping)
    struct_type = get_struct_type(context, NonOverlapping)
    
    # Check if regions can overlap
    result = analyzer.check_non_overlapping('src_base', 'src_size', 
                                           'dst_base', 'dst_size', 
                                           struct_type)
    
    # No overlap possible (regions are far apart)
    assert result.holds is True
    assert result.result == SolverResult.UNSAT


def test_check_non_overlapping_can_overlap(analyzer):
    """Test non-overlapping check when overlap is possible."""
    
    @zdc.dataclass
    class CanOverlap(zdc.Struct):
        src_base: zdc.uint32_t = zdc.field(bounds=(0, 0x1000))
        src_size: zdc.uint32_t = zdc.field(bounds=(1, 0x100))
        dst_base: zdc.uint32_t = zdc.field(bounds=(0, 0x1000))
        dst_size: zdc.uint32_t = zdc.field(bounds=(1, 0x100))
    
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(CanOverlap)
    struct_type = get_struct_type(context, CanOverlap)
    
    # Check if regions can overlap
    result = analyzer.check_non_overlapping('src_base', 'src_size',
                                           'dst_base', 'dst_size',
                                           struct_type)
    
    # Overlap is possible
    assert result.holds is False
    assert result.result == SolverResult.SAT
    assert result.counterexample is not None


def test_analyzer_field_not_found(analyzer):
    """Test error handling when field doesn't exist."""
    
    @zdc.dataclass
    class SimpleStruct(zdc.Struct):
        value: zdc.uint32_t = zdc.field(bounds=(0, 100))
    
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(SimpleStruct)
    struct_type = get_struct_type(context, SimpleStruct)
    
    # Try to check with non-existent field
    with pytest.raises(ValueError, match="not found"):
        analyzer.check_memory_access('nonexistent', 'value', 1000, struct_type)


def test_analyzer_timing_info(analyzer):
    """Test that timing information is recorded."""
    
    @zdc.dataclass
    class TimingTest(zdc.Struct):
        base: zdc.uint32_t = zdc.field(bounds=(0, 1000))
        size: zdc.uint32_t = zdc.field(bounds=(1, 100))
    
    factory = zdc.data_model_factory.DataModelFactory()
    context = factory.build(TimingTest)
    struct_type = get_struct_type(context, TimingTest)
    
    result = analyzer.check_memory_access('base', 'size', 2000, struct_type)
    
    # Should have timing information
    assert result.solver_time_ms >= 0
    assert result.solver_name == "z3"

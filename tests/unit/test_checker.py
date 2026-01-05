"""
Tests for high-level checker API.
"""
import pytest
import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')

import zuspec.dataclasses as zdc
from zuspec.be.fv import (
    check_bounds,
    check_no_overflow,
    find_bounds_violation,
)
from zuspec.be.fv.solver import SolverResult


def test_check_bounds_simple():
    """Test check_bounds with a simple struct."""
    
    @zdc.dataclass
    class SimpleConfig(zdc.Struct):
        value: zdc.uint32_t = zdc.field(bounds=(0, 100))
    
    result = check_bounds(SimpleConfig)
    
    # Should be satisfiable (valid configurations exist)
    assert result.holds is True
    assert result.solver_name == "z3"


def test_check_bounds_multiple_fields():
    """Test check_bounds with multiple bounded fields."""
    
    @zdc.dataclass
    class MultiConfig(zdc.Struct):
        addr: zdc.uint32_t = zdc.field(bounds=(0, 0xFFFF))
        size: zdc.uint8_t = zdc.field(bounds=(1, 128))
        count: zdc.uint16_t = zdc.field(bounds=(1, 1024))
    
    result = check_bounds(MultiConfig)
    
    assert result.holds is True
    assert result.counterexample is not None  # Contains a valid example


def test_check_bounds_contradictory():
    """Test check_bounds with contradictory bounds."""
    
    @zdc.dataclass
    class BadConfig(zdc.Struct):
        value: zdc.uint8_t = zdc.field(bounds=(100, 50))  # min > max
    
    result = check_bounds(BadConfig)
    
    # Should be unsatisfiable
    assert result.holds is False
    assert result.result == SolverResult.UNSAT


def test_check_bounds_with_memory_bounds():
    """Test check_bounds with memory bounds checking."""
    
    @zdc.dataclass
    class DmaConfig(zdc.Struct):
        src: zdc.uint32_t = zdc.field(bounds=(0, 0xFFFF))
        size: zdc.uint8_t = zdc.field(bounds=(1, 128))
    
    # Check with memory bounds: src + size <= 0x10000
    result = check_bounds(DmaConfig, memory_bounds={"src": 0x10000})
    
    # Should be satisfiable (configurations exist that satisfy)
    assert result.holds is True


def test_check_bounds_no_bounds():
    """Test check_bounds with struct having no bounds."""
    
    @zdc.dataclass
    class NoBounds(zdc.Struct):
        value: zdc.uint32_t
    
    result = check_bounds(NoBounds)
    
    # Should be satisfiable (no constraints)
    assert result.holds is True


def test_find_bounds_violation_safe():
    """Test find_bounds_violation when access is safe."""
    
    @zdc.dataclass
    class SafeConfig(zdc.Struct):
        base: zdc.uint32_t = zdc.field(bounds=(0, 0x1000))
        size: zdc.uint8_t = zdc.field(bounds=(1, 0x100))
    
    # Check base + size against 0x2000 (should be safe)
    result = find_bounds_violation(SafeConfig, 'base', 'size', 0x2000)
    
    assert result.holds is True  # No violation possible
    assert result.result == SolverResult.UNSAT


def test_find_bounds_violation_unsafe():
    """Test find_bounds_violation when violation is possible."""
    
    @zdc.dataclass
    class UnsafeConfig(zdc.Struct):
        base: zdc.uint32_t = zdc.field(bounds=(0, 0xFFFF))
        size: zdc.uint16_t = zdc.field(bounds=(1, 0x1000))
    
    # Check base + size against 0x1000 (violation possible)
    result = find_bounds_violation(UnsafeConfig, 'base', 'size', 0x1000)
    
    assert result.holds is False  # Violation found
    assert result.result == SolverResult.SAT
    assert result.counterexample is not None
    
    # Verify the counterexample
    cex = result.counterexample
    assert 'base' in cex
    assert 'size' in cex


def test_check_no_overflow_safe():
    """Test check_no_overflow when no overflow possible."""
    
    @zdc.dataclass
    class SafeArith(zdc.Struct):
        a: zdc.uint8_t = zdc.field(bounds=(0, 100))
        b: zdc.uint8_t = zdc.field(bounds=(0, 100))
    
    result = check_no_overflow(SafeArith, ['a', 'b'])
    
    # No overflow possible (max 200 fits in uint8 extended range)
    assert result.holds is True


def test_check_no_overflow_possible():
    """Test check_no_overflow when overflow is possible."""
    
    @zdc.dataclass
    class OverflowArith(zdc.Struct):
        a: zdc.uint8_t = zdc.field(bounds=(200, 250))
        b: zdc.uint8_t = zdc.field(bounds=(50, 100))
    
    result = check_no_overflow(OverflowArith, ['a', 'b'])
    
    # Overflow possible (max 350 > 255)
    assert result.holds is False
    assert result.counterexample is not None


def test_dma_bounds_example():
    """Test DMA bounds checking example from documentation."""
    
    @zdc.dataclass
    class DmaConfig(zdc.Struct):
        src: zdc.uint32_t = zdc.field(bounds=(0, 0xFFFF))
        dst: zdc.uint32_t = zdc.field(bounds=(0, 0xFFFF))
        xfer_sz: zdc.uint8_t = zdc.field(bounds=(1, 128))
        xfer_tot: zdc.uint16_t = zdc.field(bounds=(1, 1024))
    
    # Check basic field bounds
    result = check_bounds(DmaConfig)
    assert result.holds is True
    
    # Check src memory bounds
    result = find_bounds_violation(DmaConfig, 'src', 'xfer_sz', 0x10000)
    
    # With these bounds, violation is possible:
    # src can be 0xFFFF and xfer_sz can be 128, sum > 0x10000
    assert result.holds is False
    assert result.counterexample is not None


def test_tight_bounds_example():
    """Test with very tight bounds that should be safe."""
    
    @zdc.dataclass
    class TightConfig(zdc.Struct):
        addr: zdc.uint16_t = zdc.field(bounds=(0, 1000))
        len: zdc.uint8_t = zdc.field(bounds=(1, 50))
    
    # Check addr + len <= 1100 (max is 1050, should be safe)
    result = find_bounds_violation(TightConfig, 'addr', 'len', 1100)
    
    assert result.holds is True  # Safe
    assert result.result == SolverResult.UNSAT


def test_checker_error_handling():
    """Test error handling in checker functions."""
    
    @zdc.dataclass
    class TestStruct(zdc.Struct):
        value: zdc.uint32_t = zdc.field(bounds=(0, 100))
    
    # Test with non-existent field
    with pytest.raises(ValueError):
        find_bounds_violation(TestStruct, 'nonexistent', 'value', 1000)
    
    # Test check_no_overflow with wrong number of fields
    with pytest.raises(ValueError, match="two fields"):
        check_no_overflow(TestStruct, ['value'])


def test_result_has_timing():
    """Test that results include timing information."""
    
    @zdc.dataclass
    class TimingStruct(zdc.Struct):
        value: zdc.uint32_t = zdc.field(bounds=(0, 100))
    
    result = check_bounds(TimingStruct)
    
    assert result.solver_time_ms >= 0
    assert isinstance(result.solver_time_ms, float)


def test_result_string_representation():
    """Test VerificationResult string representation."""
    
    @zdc.dataclass
    class ResultStruct(zdc.Struct):
        value: zdc.uint32_t = zdc.field(bounds=(0, 100))
    
    result = check_bounds(ResultStruct)
    
    # Should have a string representation
    result_str = str(result)
    assert len(result_str) > 0
    assert "z3" in result_str.lower() or "property" in result_str.lower()

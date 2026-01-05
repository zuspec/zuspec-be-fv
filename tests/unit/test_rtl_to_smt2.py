"""
Tests for RTL to SMT2 translation.
"""

import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')
sys.path.insert(0, 'packages/zuspec-be-fv/src')

import pytest
from zuspec.dataclasses import ir
from zuspec.be.fv.rtl import RTLToSMT2Translator, SMT2Module, SMT2Signal


def test_smt2_module_creation():
    """Test basic SMT2Module creation."""
    module = SMT2Module(name="test_module")
    
    assert module.name == "test_module"
    assert module.state_sort == "test_module_s"
    assert len(module.inputs) == 0
    assert len(module.outputs) == 0
    assert len(module.registers) == 0


def test_smt2_signal_creation():
    """Test SMT2Signal creation."""
    sig = SMT2Signal(
        name="clk",
        smt_name="clk#1",
        datatype=ir.DataTypeInt(bits=1, signed=False),
        direction=ir.SignalDirection.INPUT,
        width=1,
        is_signed=False
    )
    
    assert sig.name == "clk"
    assert sig.smt_name == "clk#1"
    assert sig.width == 1
    assert not sig.is_signed
    assert sig.direction == ir.SignalDirection.INPUT


def test_smt2_module_add_signals():
    """Test adding signals to module."""
    module = SMT2Module(name="counter")
    
    clk_sig = SMT2Signal(
        name="clk",
        smt_name="clk#1",
        datatype=ir.DataTypeInt(bits=1, signed=False),
        direction=ir.SignalDirection.INPUT,
        width=1,
        is_signed=False
    )
    
    count_sig = SMT2Signal(
        name="count",
        smt_name="count#2",
        datatype=ir.DataTypeInt(bits=8, signed=False),
        direction=ir.SignalDirection.OUTPUT,
        width=8,
        is_signed=False
    )
    
    module.add_input(clk_sig)
    module.add_output(count_sig)
    
    assert len(module.inputs) == 1
    assert "clk" in module.inputs
    assert len(module.outputs) == 1
    assert "count" in module.outputs


def test_translator_creation():
    """Test RTLToSMT2Translator creation."""
    translator = RTLToSMT2Translator()
    
    assert translator is not None
    assert translator.expr_translator is not None
    assert translator.stmt_translator is not None


def test_translate_empty_component():
    """Test translating an empty component."""
    translator = RTLToSMT2Translator()
    
    # Create minimal component
    comp = ir.DataTypeComponent(
        name="empty_component",
        super=None,
        fields=[],
        functions=[],
        sync_processes=[],
        comb_processes=[]
    )
    
    module = translator.translate_component(comp)
    
    assert module.name == "empty_component"
    assert module.state_sort == "empty_component_s"


def test_translate_component_with_input():
    """Test translating component with input signal."""
    translator = RTLToSMT2Translator()
    
    # Create component with input field
    clk_field = ir.Field(
        name="clk",
        datatype=ir.DataTypeInt(bits=1, signed=False),
        direction=ir.SignalDirection.INPUT
    )
    
    comp = ir.DataTypeComponent(
        name="simple",
        super=None,
        fields=[clk_field],
        functions=[],
        sync_processes=[],
        comb_processes=[]
    )
    
    module = translator.translate_component(comp)
    
    assert len(module.inputs) == 1
    assert "clk" in module.inputs
    assert module.inputs["clk"].width == 1


def test_translate_component_with_output():
    """Test translating component with output signal."""
    translator = RTLToSMT2Translator()
    
    # Create component with output field
    out_field = ir.Field(
        name="result",
        datatype=ir.DataTypeInt(bits=8, signed=False),
        direction=ir.SignalDirection.OUTPUT
    )
    
    comp = ir.DataTypeComponent(
        name="simple",
        super=None,
        fields=[out_field],
        functions=[],
        sync_processes=[],
        comb_processes=[]
    )
    
    module = translator.translate_component(comp)
    
    assert len(module.outputs) == 1
    assert "result" in module.outputs
    assert module.outputs["result"].width == 8


def test_generate_smt2_empty():
    """Test generating SMT2 text from empty module."""
    translator = RTLToSMT2Translator()
    
    module = SMT2Module(name="test")
    smt2_text = translator.generate_smt2(module)
    
    assert "; zuspec-smt2-module test" in smt2_text
    assert "(declare-sort |test_s| 0)" in smt2_text
    assert "(declare-fun |test_is| (|test_s|) Bool)" in smt2_text
    assert "test_a" in smt2_text  # Assertion predicate
    assert "test_u" in smt2_text  # Assumption predicate
    assert "test_c" in smt2_text  # Coverage predicate
    assert "test_i" in smt2_text  # Initial predicate
    assert "test_h" in smt2_text  # Hierarchy predicate
    assert "test_t" in smt2_text  # Transition predicate


def test_generate_smt2_with_input():
    """Test generating SMT2 with input signal."""
    translator = RTLToSMT2Translator()
    
    module = SMT2Module(name="test")
    clk_sig = SMT2Signal(
        name="clk",
        smt_name="clk_1",
        datatype=ir.DataTypeInt(bits=1, signed=False),
        direction=ir.SignalDirection.INPUT,
        width=1,
        is_signed=False
    )
    module.add_input(clk_sig)
    
    smt2_text = translator.generate_smt2(module)
    
    assert "(declare-fun |test#clk_1|" in smt2_text
    assert "; zuspec-smt2-input clk 1" in smt2_text


def test_generate_smt2_with_bitvector():
    """Test generating SMT2 with bitvector signal."""
    translator = RTLToSMT2Translator()
    
    module = SMT2Module(name="test")
    data_sig = SMT2Signal(
        name="data",
        smt_name="data_1",
        datatype=ir.DataTypeInt(bits=32, signed=False),
        direction=ir.SignalDirection.INPUT,
        width=32,
        is_signed=False
    )
    module.add_input(data_sig)
    
    smt2_text = translator.generate_smt2(module)
    
    assert "(_ BitVec 32)" in smt2_text
    assert "; zuspec-smt2-input data 32" in smt2_text


def test_get_type_info():
    """Test type info extraction."""
    translator = RTLToSMT2Translator()
    
    # Test integer type
    int_type = ir.DataTypeInt(bits=16, signed=True)
    width, is_signed = translator._get_type_info(int_type)
    assert width == 16
    assert is_signed
    
    # Test unsigned
    uint_type = ir.DataTypeInt(bits=8, signed=False)
    width, is_signed = translator._get_type_info(uint_type)
    assert width == 8
    assert not is_signed
    
    # Test default width
    default_type = ir.DataTypeInt(bits=-1, signed=False)
    width, is_signed = translator._get_type_info(default_type)
    assert width == 32  # Default width


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

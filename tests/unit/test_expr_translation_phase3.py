"""
Tests for Phase 3: Expression Translation with Context.

Tests comprehensive expression translation including:
- Type inference
- Width extension
- Signed/unsigned operations
- Field references
- Constant handling
"""

import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')
sys.path.insert(0, 'packages/zuspec-be-fv/src')

import pytest
from zuspec.dataclasses import ir
from zuspec.be.fv.rtl import (
    TranslationContext, ExprToSMT2Translator, SMT2Module, SMT2Signal
)


@pytest.fixture
def simple_component():
    """Create a simple component for testing."""
    clk_field = ir.Field(
        name="clk",
        datatype=ir.DataTypeInt(bits=1, signed=False),
        direction=ir.SignalDirection.INPUT
    )
    
    count_field = ir.Field(
        name="count",
        datatype=ir.DataTypeInt(bits=8, signed=False),
        direction=ir.SignalDirection.OUTPUT
    )
    
    increment_field = ir.Field(
        name="increment",
        datatype=ir.DataTypeInt(bits=4, signed=False),
        direction=ir.SignalDirection.INPUT
    )
    
    comp = ir.DataTypeComponent(
        name="TestCounter",
        super=None,
        fields=[clk_field, count_field, increment_field],
        functions=[],
        sync_processes=[],
        comb_processes=[]
    )
    
    return comp


@pytest.fixture
def context(simple_component):
    """Create translation context."""
    module = SMT2Module(name="TestCounter")
    
    ctx = TranslationContext(
        component=simple_component,
        module=module,
        field_map={
            0: "clk_1",
            1: "count_2",
            2: "increment_3"
        }
    )
    
    return ctx


def test_translation_context_creation(simple_component):
    """Test creating translation context."""
    module = SMT2Module(name="Test")
    ctx = TranslationContext(
        component=simple_component,
        module=module
    )
    
    assert ctx.component == simple_component
    assert ctx.module == module
    assert ctx.state_var == "state"


def test_context_get_field_smt_name(context):
    """Test getting SMT name for field."""
    assert context.get_field_smt_name(0) == "clk_1"
    assert context.get_field_smt_name(1) == "count_2"
    assert context.get_field_smt_name(2) == "increment_3"
    
    with pytest.raises(ValueError):
        context.get_field_smt_name(99)


def test_context_infer_constant_type(context):
    """Test type inference for constants."""
    # Boolean
    bool_expr = ir.ExprConstant(value=True)
    bool_type = context.infer_type(bool_expr)
    assert isinstance(bool_type, ir.DataTypeInt)
    assert bool_type.bits == 1
    assert not bool_type.signed
    
    # Positive integer
    int_expr = ir.ExprConstant(value=10)
    int_type = context.infer_type(int_expr)
    assert isinstance(int_type, ir.DataTypeInt)
    assert int_type.bits == 4  # 10 requires 4 bits
    
    # Negative integer
    neg_expr = ir.ExprConstant(value=-5)
    neg_type = context.infer_type(neg_expr)
    assert isinstance(neg_type, ir.DataTypeInt)
    assert neg_type.signed


def test_context_infer_field_type(context):
    """Test type inference for field references."""
    # Reference to count field (8-bit unsigned)
    field_ref = ir.ExprRefField(
        base=ir.TypeExprRefSelf(),
        index=1
    )
    
    field_type = context.infer_type(field_ref)
    assert isinstance(field_type, ir.DataTypeInt)
    assert field_type.bits == 8
    assert not field_type.signed


def test_context_get_bit_width(context):
    """Test getting bit width from expressions."""
    # 8-bit field
    field_ref = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)
    assert context.get_bit_width(field_ref) == 8
    
    # 4-bit field
    inc_ref = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=2)
    assert context.get_bit_width(inc_ref) == 4
    
    # Constant
    const = ir.ExprConstant(value=255)
    assert context.get_bit_width(const) == 8  # 255 requires 8 bits


def test_context_is_signed_type(context):
    """Test checking if type is signed."""
    # Unsigned field
    field_ref = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)
    assert not context.is_signed_type(field_ref)
    
    # Negative constant (inferred as signed)
    neg_const = ir.ExprConstant(value=-1)
    assert context.is_signed_type(neg_const)


def test_expr_translator_constant_bool(context):
    """Test translating boolean constants."""
    translator = ExprToSMT2Translator()
    
    true_expr = ir.ExprConstant(value=True)
    assert translator.translate(true_expr, context) == "true"
    
    false_expr = ir.ExprConstant(value=False)
    assert translator.translate(false_expr, context) == "false"


def test_expr_translator_constant_int(context):
    """Test translating integer constants."""
    translator = ExprToSMT2Translator()
    
    # Small positive constant
    expr = ir.ExprConstant(value=10)
    result = translator.translate(expr, context)
    assert result.startswith("#b")
    assert result == "#b1010"  # 10 in binary, 4 bits
    
    # Zero
    zero_expr = ir.ExprConstant(value=0)
    result = translator.translate(zero_expr, context)
    assert result == "#b0"


def test_expr_translator_field_reference(context):
    """Test translating field references."""
    translator = ExprToSMT2Translator()
    
    # Reference to count field
    field_ref = ir.ExprRefField(
        base=ir.TypeExprRefSelf(),
        index=1
    )
    
    result = translator.translate(field_ref, context)
    assert result == "(|TestCounter#count_2| state)"


def test_expr_translator_binary_add_same_width(context):
    """Test binary addition with same width operands."""
    translator = ExprToSMT2Translator()
    
    # count (8-bit) + 1 (will be 8-bit)
    lhs = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)
    rhs = ir.ExprConstant(value=1)
    expr = ir.ExprBin(lhs=lhs, op=ir.BinOp.Add, rhs=rhs)
    
    result = translator.translate(expr, context)
    assert "bvadd" in result
    assert "(|TestCounter#count_2| state)" in result


def test_expr_translator_binary_add_different_width(context):
    """Test binary addition with different width operands."""
    translator = ExprToSMT2Translator()
    
    # count (8-bit) + increment (4-bit)
    lhs = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)  # count, 8-bit
    rhs = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=2)  # increment, 4-bit
    expr = ir.ExprBin(lhs=lhs, op=ir.BinOp.Add, rhs=rhs)
    
    result = translator.translate(expr, context)
    assert "bvadd" in result
    assert "zero_extend" in result  # 4-bit should be extended to 8-bit


def test_expr_translator_comparison_unsigned(context):
    """Test unsigned comparison."""
    translator = ExprToSMT2Translator()
    
    # count < 255
    lhs = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)
    rhs = ir.ExprConstant(value=255)
    expr = ir.ExprBin(lhs=lhs, op=ir.BinOp.Lt, rhs=rhs)
    
    result = translator.translate(expr, context)
    assert "bvult" in result  # Unsigned less than


def test_expr_translator_comparison_signed():
    """Test signed comparison."""
    # Create component with signed field
    signed_field = ir.Field(
        name="signed_val",
        datatype=ir.DataTypeInt(bits=8, signed=True),
        direction=ir.SignalDirection.OUTPUT
    )
    
    comp = ir.DataTypeComponent(
        name="Test",
        super=None,
        fields=[signed_field],
        functions=[],
        sync_processes=[],
        comb_processes=[]
    )
    
    module = SMT2Module(name="Test")
    ctx = TranslationContext(
        component=comp,
        module=module,
        field_map={0: "signed_val_1"}
    )
    
    translator = ExprToSMT2Translator()
    
    # signed_val < 0
    lhs = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=0)
    rhs = ir.ExprConstant(value=0)
    expr = ir.ExprBin(lhs=lhs, op=ir.BinOp.Lt, rhs=rhs)
    
    result = translator.translate(expr, ctx)
    assert "bvslt" in result  # Signed less than


def test_expr_translator_bitwise_and(context):
    """Test bitwise AND operation."""
    translator = ExprToSMT2Translator()
    
    # count & 0x0F
    lhs = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)
    rhs = ir.ExprConstant(value=0x0F)
    expr = ir.ExprBin(lhs=lhs, op=ir.BinOp.BitAnd, rhs=rhs)
    
    result = translator.translate(expr, context)
    assert "bvand" in result


def test_expr_translator_shift_left(context):
    """Test left shift operation."""
    translator = ExprToSMT2Translator()
    
    # count << 2
    lhs = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)
    rhs = ir.ExprConstant(value=2)
    expr = ir.ExprBin(lhs=lhs, op=ir.BinOp.LShift, rhs=rhs)
    
    result = translator.translate(expr, context)
    assert "bvshl" in result


def test_expr_translator_unary_not(context):
    """Test unary NOT operation."""
    translator = ExprToSMT2Translator()
    
    # ~count
    operand = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)
    expr = ir.ExprUnary(op=ir.UnaryOp.Invert, operand=operand)
    
    result = translator.translate(expr, context)
    assert "bvnot" in result


def test_expr_translator_unary_negate(context):
    """Test unary negation."""
    translator = ExprToSMT2Translator()
    
    # -count
    operand = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)
    expr = ir.ExprUnary(op=ir.UnaryOp.USub, operand=operand)
    
    result = translator.translate(expr, context)
    assert "bvneg" in result


def test_expr_translator_compare_simple(context):
    """Test simple comparison expression."""
    translator = ExprToSMT2Translator()
    
    # count == 255
    left = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)
    comparator = ir.ExprConstant(value=255)
    expr = ir.ExprCompare(
        left=left,
        ops=[ir.CmpOp.Eq],
        comparators=[comparator]
    )
    
    result = translator.translate(expr, context)
    assert "=" in result


def test_expr_translator_compare_chained(context):
    """Test chained comparison."""
    translator = ExprToSMT2Translator()
    
    # 0 <= count <= 255
    left = ir.ExprConstant(value=0)
    count = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)
    right = ir.ExprConstant(value=255)
    
    expr = ir.ExprCompare(
        left=left,
        ops=[ir.CmpOp.LtE, ir.CmpOp.LtE],
        comparators=[count, right]
    )
    
    result = translator.translate(expr, context)
    assert "and" in result
    assert result.count("bvule") == 2  # Two comparisons


def test_expr_translator_boolean_and(context):
    """Test boolean AND."""
    translator = ExprToSMT2Translator()
    
    # (count > 0) and (count < 255)
    cond1 = ir.ExprBin(
        lhs=ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1),
        op=ir.BinOp.Gt,
        rhs=ir.ExprConstant(value=0)
    )
    cond2 = ir.ExprBin(
        lhs=ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1),
        op=ir.BinOp.Lt,
        rhs=ir.ExprConstant(value=255)
    )
    
    expr = ir.ExprBool(
        op=ir.BoolOp.And,
        values=[cond1, cond2]
    )
    
    result = translator.translate(expr, context)
    assert "and" in result
    assert "bvugt" in result
    assert "bvult" in result


def test_expr_translator_complex_expression(context):
    """Test complex nested expression."""
    translator = ExprToSMT2Translator()
    
    # (count + increment) < 255
    add_expr = ir.ExprBin(
        lhs=ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1),  # count
        op=ir.BinOp.Add,
        rhs=ir.ExprRefField(base=ir.TypeExprRefSelf(), index=2)   # increment
    )
    
    cmp_expr = ir.ExprBin(
        lhs=add_expr,
        op=ir.BinOp.Lt,
        rhs=ir.ExprConstant(value=255)
    )
    
    result = translator.translate(cmp_expr, context)
    assert "bvadd" in result
    assert "bvult" in result
    assert "zero_extend" in result  # increment extended from 4 to 8 bits


def test_expr_translator_division_unsigned(context):
    """Test unsigned division."""
    translator = ExprToSMT2Translator()
    
    # count / 2
    lhs = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)
    rhs = ir.ExprConstant(value=2)
    expr = ir.ExprBin(lhs=lhs, op=ir.BinOp.Div, rhs=rhs)
    
    result = translator.translate(expr, context)
    assert "bvudiv" in result  # Unsigned division


def test_expr_translator_modulo_unsigned(context):
    """Test unsigned modulo."""
    translator = ExprToSMT2Translator()
    
    # count % 10
    lhs = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)
    rhs = ir.ExprConstant(value=10)
    expr = ir.ExprBin(lhs=lhs, op=ir.BinOp.Mod, rhs=rhs)
    
    result = translator.translate(expr, context)
    assert "bvurem" in result  # Unsigned remainder


def test_context_local_variables(context):
    """Test local variable tracking."""
    context.add_local_var("temp", "#b00000101")
    
    assert context.get_local_var("temp") == "#b00000101"
    assert context.get_local_var("nonexistent") is None


def test_expr_translator_local_var_reference(context):
    """Test translating local variable reference."""
    translator = ExprToSMT2Translator()
    
    # Add local variable
    context.add_local_var("temp", "#b00001010")
    
    # Reference it
    expr = ir.ExprRefLocal(name="temp")
    result = translator.translate(expr, context)
    
    assert result == "#b00001010"


def test_expr_translator_local_var_uninitialized(context):
    """Test that using uninitialized local variable raises error."""
    translator = ExprToSMT2Translator()
    
    expr = ir.ExprRefLocal(name="undefined")
    
    with pytest.raises(ValueError, match="used before assignment"):
        translator.translate(expr, context)


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

"""Tests for Phase 4: Statement translation.

Covers:
- Field assignments -> transitions
- Local variables
- If/else -> ITE
"""

import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')
sys.path.insert(0, 'packages/zuspec-be-fv/src')

import pytest
from zuspec.dataclasses import ir
from zuspec.be.fv.rtl import TranslationContext, ExprToSMT2Translator, StmtToSMT2Translator, SMT2Module


@pytest.fixture
def comp_and_ctx():
    rst = ir.Field(
        name="rst",
        datatype=ir.DataTypeInt(bits=1, signed=False),
        direction=ir.SignalDirection.INPUT,
    )
    count = ir.Field(
        name="count",
        datatype=ir.DataTypeInt(bits=8, signed=False),
        direction=ir.SignalDirection.OUTPUT,
    )

    comp = ir.DataTypeComponent(
        name="Test",
        super=None,
        fields=[rst, count],
        functions=[],
        sync_processes=[],
        comb_processes=[],
    )

    module = SMT2Module(name="Test")
    ctx = TranslationContext(component=comp, module=module, field_map={0: "rst_1", 1: "count_2"})
    return comp, ctx


def test_assign_field_width_extension(comp_and_ctx):
    _, ctx = comp_and_ctx
    et = ExprToSMT2Translator()
    st = StmtToSMT2Translator(et)

    stmt = ir.StmtAssign(
        targets=[ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)],
        value=ir.ExprConstant(value=1),
    )

    trans = st.translate_sync_body([stmt], ctx)
    assert len(trans) == 1
    assert trans[0].register_name == "count_2"
    assert "zero_extend" in trans[0].next_value_expr or trans[0].next_value_expr.startswith("#b")


def test_local_variable_assignment_and_use(comp_and_ctx):
    _, ctx = comp_and_ctx
    et = ExprToSMT2Translator()
    st = StmtToSMT2Translator(et)

    stmts = [
        ir.StmtAssign(targets=[ir.ExprRefLocal(name="tmp")], value=ir.ExprConstant(value=5)),
        ir.StmtAssign(
            targets=[ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)],
            value=ir.ExprRefLocal(name="tmp"),
        ),
    ]

    trans = st.translate_sync_body(stmts, ctx)
    assert len(trans) == 1
    assert trans[0].register_name == "count_2"


def test_if_else_to_ite(comp_and_ctx):
    _, ctx = comp_and_ctx
    et = ExprToSMT2Translator()
    st = StmtToSMT2Translator(et)

    rst_ref = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=0)
    count_ref = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)

    if_stmt = ir.StmtIf(
        test=rst_ref,
        body=[ir.StmtAssign(targets=[count_ref], value=ir.ExprConstant(value=0))],
        orelse=[
            ir.StmtAssign(
                targets=[count_ref],
                value=ir.ExprBin(lhs=count_ref, op=ir.BinOp.Add, rhs=ir.ExprConstant(value=1)),
            )
        ],
    )

    trans = st.translate_sync_body([if_stmt], ctx)
    assert len(trans) == 1
    assert "ite" in trans[0].next_value_expr
    assert "bvadd" in trans[0].next_value_expr

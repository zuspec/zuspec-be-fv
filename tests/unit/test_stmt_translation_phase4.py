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
from zuspec.dataclasses import dm
from zuspec.be.fv.rtl import TranslationContext, ExprToSMT2Translator, StmtToSMT2Translator, SMT2Module


@pytest.fixture
def comp_and_ctx():
    rst = dm.Field(
        name="rst",
        datatype=dm.DataTypeInt(bits=1, signed=False),
        direction=dm.SignalDirection.INPUT,
    )
    count = dm.Field(
        name="count",
        datatype=dm.DataTypeInt(bits=8, signed=False),
        direction=dm.SignalDirection.OUTPUT,
    )

    comp = dm.DataTypeComponent(
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

    stmt = dm.StmtAssign(
        targets=[dm.ExprRefField(base=dm.TypeExprRefSelf(), index=1)],
        value=dm.ExprConstant(value=1),
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
        dm.StmtAssign(targets=[dm.ExprRefLocal(name="tmp")], value=dm.ExprConstant(value=5)),
        dm.StmtAssign(
            targets=[dm.ExprRefField(base=dm.TypeExprRefSelf(), index=1)],
            value=dm.ExprRefLocal(name="tmp"),
        ),
    ]

    trans = st.translate_sync_body(stmts, ctx)
    assert len(trans) == 1
    assert trans[0].register_name == "count_2"


def test_if_else_to_ite(comp_and_ctx):
    _, ctx = comp_and_ctx
    et = ExprToSMT2Translator()
    st = StmtToSMT2Translator(et)

    rst_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=0)
    count_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=1)

    if_stmt = dm.StmtIf(
        test=rst_ref,
        body=[dm.StmtAssign(targets=[count_ref], value=dm.ExprConstant(value=0))],
        orelse=[
            dm.StmtAssign(
                targets=[count_ref],
                value=dm.ExprBin(lhs=count_ref, op=dm.BinOp.Add, rhs=dm.ExprConstant(value=1)),
            )
        ],
    )

    trans = st.translate_sync_body([if_stmt], ctx)
    assert len(trans) == 1
    assert "ite" in trans[0].next_value_expr
    assert "bvadd" in trans[0].next_value_expr

"""Tests for Phase 6: formal property extraction.

Covers assert/assume/cover extraction (including if-guards) and invariant support.
"""

import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')
sys.path.insert(0, 'packages/zuspec-be-fv/src')

from zuspec.dataclasses import dm
from zuspec.be.fv.rtl import RTLToSMT2Translator


def test_extract_assert_assume_cover_and_invariant():
    clk = dm.Field(name="clk", datatype=dm.DataTypeInt(bits=1, signed=False), direction=dm.SignalDirection.INPUT)
    rst = dm.Field(name="rst", datatype=dm.DataTypeInt(bits=1, signed=False), direction=dm.SignalDirection.INPUT)
    count = dm.Field(name="count", datatype=dm.DataTypeInt(bits=8, signed=False), direction=dm.SignalDirection.OUTPUT,
                     initial_value=dm.ExprConstant(value=0))

    rst_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=1)
    count_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=2)

    update = dm.Function(
        name="update",
        args=None,
        body=[
            dm.StmtAssume(test=dm.ExprBin(lhs=count_ref, op=dm.BinOp.LtE, rhs=dm.ExprConstant(value=255))),
            dm.StmtIf(
                test=rst_ref,
                body=[dm.StmtAssert(test=dm.ExprBin(lhs=count_ref, op=dm.BinOp.Eq, rhs=dm.ExprConstant(value=0)))],
                orelse=[],
            ),
            dm.StmtCover(test=dm.ExprBin(lhs=count_ref, op=dm.BinOp.Eq, rhs=dm.ExprConstant(value=10))),
            dm.StmtAssign(targets=[count_ref], value=dm.ExprConstant(value=1)),
        ],
        process_kind=dm.ProcessKind.SYNC,
        sensitivity_list=[],
    )

    inv = dm.Function(
        name="inv",
        args=None,
        body=[dm.StmtReturn(value=dm.ExprBin(lhs=count_ref, op=dm.BinOp.LtE, rhs=dm.ExprConstant(value=255)))],
        is_invariant=True,
    )

    comp = dm.DataTypeComponent(
        name="P",
        super=None,
        fields=[clk, rst, count],
        functions=[inv],
        sync_processes=[update],
        comb_processes=[],
    )

    t = RTLToSMT2Translator()
    m = t.translate_component(comp)
    smt2 = t.generate_smt2(m)

    # predicates exist
    assert "|P_a|" in smt2
    assert "|P_u|" in smt2
    assert "|P_c|" in smt2
    assert "|P_i|" in smt2

    # guarded assert should appear as an implication
    assert "=>" in smt2

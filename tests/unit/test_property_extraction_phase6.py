"""Tests for Phase 6: formal property extraction.

Covers assert/assume/cover extraction (including if-guards) and invariant support.
"""

import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')
sys.path.insert(0, 'packages/zuspec-be-fv/src')

from zuspec.dataclasses import ir
from zuspec.be.fv.rtl import RTLToSMT2Translator


def test_extract_assert_assume_cover_and_invariant():
    clk = ir.Field(name="clk", datatype=ir.DataTypeInt(bits=1, signed=False), direction=ir.SignalDirection.INPUT)
    rst = ir.Field(name="rst", datatype=ir.DataTypeInt(bits=1, signed=False), direction=ir.SignalDirection.INPUT)
    count = ir.Field(name="count", datatype=ir.DataTypeInt(bits=8, signed=False), direction=ir.SignalDirection.OUTPUT,
                     initial_value=ir.ExprConstant(value=0))

    rst_ref = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)
    count_ref = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=2)

    update = ir.Function(
        name="update",
        args=None,
        body=[
            ir.StmtAssume(test=ir.ExprBin(lhs=count_ref, op=ir.BinOp.LtE, rhs=ir.ExprConstant(value=255))),
            ir.StmtIf(
                test=rst_ref,
                body=[ir.StmtAssert(test=ir.ExprBin(lhs=count_ref, op=ir.BinOp.Eq, rhs=ir.ExprConstant(value=0)))],
                orelse=[],
            ),
            ir.StmtCover(test=ir.ExprBin(lhs=count_ref, op=ir.BinOp.Eq, rhs=ir.ExprConstant(value=10))),
            ir.StmtAssign(targets=[count_ref], value=ir.ExprConstant(value=1)),
        ],
        process_kind=ir.ProcessKind.SYNC,
        sensitivity_list=[],
    )

    inv = ir.Function(
        name="inv",
        args=None,
        body=[ir.StmtReturn(value=ir.ExprBin(lhs=count_ref, op=ir.BinOp.LtE, rhs=ir.ExprConstant(value=255)))],
        is_invariant=True,
    )

    comp = ir.DataTypeComponent(
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

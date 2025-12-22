"""Integration tests for Phase 4: sync process translation in RTLToSMT2Translator."""

import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')
sys.path.insert(0, 'packages/zuspec-be-fv/src')

from zuspec.dataclasses import ir
from zuspec.be.fv.rtl import RTLToSMT2Translator


def test_translate_sync_process_adds_transition_and_register():
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

    count_ref = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=1)
    rst_ref = ir.ExprRefField(base=ir.TypeExprRefSelf(), index=0)

    update = ir.Function(
        name="update",
        args=None,
        body=[
            ir.StmtIf(
                test=rst_ref,
                body=[ir.StmtAssign(targets=[count_ref], value=ir.ExprConstant(value=0))],
                orelse=[ir.StmtAssign(targets=[count_ref], value=ir.ExprConstant(value=1))],
            )
        ],
        process_kind=ir.ProcessKind.SYNC,
        sensitivity_list=[],
    )

    comp = ir.DataTypeComponent(
        name="C",
        super=None,
        fields=[rst, count],
        functions=[],
        sync_processes=[update],
        comb_processes=[],
    )

    t = RTLToSMT2Translator()
    m = t.translate_component(comp)

    assert "count" in m.registers
    assert len(m.transitions) == 1

    smt2 = t.generate_smt2(m)
    assert "(define-fun |C_t|" in smt2
    assert "ite" in smt2

"""Integration tests for Phase 4: sync process translation in RTLToSMT2Translator."""

import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')
sys.path.insert(0, 'packages/zuspec-be-fv/src')

from zuspec.dataclasses import dm
from zuspec.be.fv.rtl import RTLToSMT2Translator


def test_translate_sync_process_adds_transition_and_register():
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

    count_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=1)
    rst_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=0)

    update = dm.Function(
        name="update",
        args=None,
        body=[
            dm.StmtIf(
                test=rst_ref,
                body=[dm.StmtAssign(targets=[count_ref], value=dm.ExprConstant(value=0))],
                orelse=[dm.StmtAssign(targets=[count_ref], value=dm.ExprConstant(value=1))],
            )
        ],
        process_kind=dm.ProcessKind.SYNC,
        sensitivity_list=[],
    )

    comp = dm.DataTypeComponent(
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

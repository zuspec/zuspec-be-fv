"""Tests for Phase 5: combinational process translation.

Focus:
- @comb assignment to field becomes a signal `define-fun`
- Defined-signal dependency ordering
"""

import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')
sys.path.insert(0, 'packages/zuspec-be-fv/src')

from zuspec.dataclasses import dm
from zuspec.be.fv.rtl import RTLToSMT2Translator


def test_comb_assign_defines_output_signal():
    a = dm.Field(name="a", datatype=dm.DataTypeInt(bits=8, signed=False), direction=dm.SignalDirection.INPUT)
    b = dm.Field(name="b", datatype=dm.DataTypeInt(bits=8, signed=False), direction=dm.SignalDirection.INPUT)
    s = dm.Field(name="sum", datatype=dm.DataTypeInt(bits=8, signed=False), direction=dm.SignalDirection.OUTPUT)

    sum_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=2)
    a_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=0)
    b_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=1)

    comb = dm.Function(
        name="compute",
        args=None,
        body=[dm.StmtAssign(targets=[sum_ref], value=dm.ExprBin(lhs=a_ref, op=dm.BinOp.Add, rhs=b_ref))],
        process_kind=dm.ProcessKind.COMB,
        sensitivity_list=[],
    )

    comp = dm.DataTypeComponent(
        name="Adder",
        super=None,
        fields=[a, b, s],
        functions=[],
        sync_processes=[],
        comb_processes=[comb],
    )

    t = RTLToSMT2Translator()
    m = t.translate_component(comp)

    smt_name = m.outputs["sum"].smt_name
    out = t.generate_smt2(m)

    assert f"(define-fun |Adder#{smt_name}|" in out
    assert f"(declare-fun |Adder#{smt_name}|" not in out


def test_comb_defined_signal_dependency_ordering():
    a = dm.Field(name="a", datatype=dm.DataTypeInt(bits=8, signed=False), direction=dm.SignalDirection.INPUT)
    w = dm.Field(name="w", datatype=dm.DataTypeInt(bits=8, signed=False), direction=None)
    y = dm.Field(name="y", datatype=dm.DataTypeInt(bits=8, signed=False), direction=dm.SignalDirection.OUTPUT)

    w_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=1)
    y_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=2)
    a_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=0)

    comb_w = dm.Function(
        name="comb_w",
        args=None,
        body=[dm.StmtAssign(targets=[w_ref], value=dm.ExprBin(lhs=a_ref, op=dm.BinOp.Add, rhs=dm.ExprConstant(value=1)))],
        process_kind=dm.ProcessKind.COMB,
        sensitivity_list=[],
    )

    comb_y = dm.Function(
        name="comb_y",
        args=None,
        body=[dm.StmtAssign(targets=[y_ref], value=dm.ExprBin(lhs=w_ref, op=dm.BinOp.Add, rhs=dm.ExprConstant(value=1)))],
        process_kind=dm.ProcessKind.COMB,
        sensitivity_list=[],
    )

    comp = dm.DataTypeComponent(
        name="Dep",
        super=None,
        fields=[a, w, y],
        functions=[],
        sync_processes=[],
        comb_processes=[comb_w, comb_y],
    )

    t = RTLToSMT2Translator()
    m = t.translate_component(comp)

    w_smt = m.wires["w"].smt_name
    y_smt = m.outputs["y"].smt_name

    out = t.generate_smt2(m)

    w_pos = out.find(f"(define-fun |Dep#{w_smt}|")
    y_pos = out.find(f"(define-fun |Dep#{y_smt}|")

    assert w_pos != -1
    assert y_pos != -1
    assert w_pos < y_pos


def test_comb_definition_cycle_detected():
    a = dm.Field(name="a", datatype=dm.DataTypeInt(bits=8, signed=False), direction=dm.SignalDirection.INPUT)
    w1 = dm.Field(name="w1", datatype=dm.DataTypeInt(bits=8, signed=False), direction=None)
    w2 = dm.Field(name="w2", datatype=dm.DataTypeInt(bits=8, signed=False), direction=None)

    a_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=0)
    w1_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=1)
    w2_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=2)

    comb_w1 = dm.Function(
        name="comb_w1",
        args=None,
        body=[dm.StmtAssign(targets=[w1_ref], value=dm.ExprBin(lhs=w2_ref, op=dm.BinOp.Add, rhs=a_ref))],
        process_kind=dm.ProcessKind.COMB,
        sensitivity_list=[],
    )

    comb_w2 = dm.Function(
        name="comb_w2",
        args=None,
        body=[dm.StmtAssign(targets=[w2_ref], value=dm.ExprBin(lhs=w1_ref, op=dm.BinOp.Add, rhs=a_ref))],
        process_kind=dm.ProcessKind.COMB,
        sensitivity_list=[],
    )

    comp = dm.DataTypeComponent(
        name="Cycle",
        super=None,
        fields=[a, w1, w2],
        functions=[],
        sync_processes=[],
        comb_processes=[comb_w1, comb_w2],
    )

    t = RTLToSMT2Translator()
    m = t.translate_component(comp)

    try:
        t.generate_smt2(m)
        assert False, "Expected combinational cycle to be detected"
    except ValueError as e:
        assert "cycle" in str(e).lower()


def test_comb_and_sync_drive_same_signal_error():
    rst = dm.Field(name="rst", datatype=dm.DataTypeInt(bits=1, signed=False), direction=dm.SignalDirection.INPUT)
    y = dm.Field(name="y", datatype=dm.DataTypeInt(bits=8, signed=False), direction=dm.SignalDirection.OUTPUT)

    rst_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=0)
    y_ref = dm.ExprRefField(base=dm.TypeExprRefSelf(), index=1)

    comb = dm.Function(
        name="comb",
        args=None,
        body=[dm.StmtAssign(targets=[y_ref], value=dm.ExprConstant(value=1))],
        process_kind=dm.ProcessKind.COMB,
        sensitivity_list=[],
    )

    sync = dm.Function(
        name="sync",
        args=None,
        body=[dm.StmtIf(test=rst_ref, body=[dm.StmtAssign(targets=[y_ref], value=dm.ExprConstant(value=0))], orelse=[])],
        process_kind=dm.ProcessKind.SYNC,
        sensitivity_list=[],
    )

    comp = dm.DataTypeComponent(
        name="Mix",
        super=None,
        fields=[rst, y],
        functions=[],
        sync_processes=[sync],
        comb_processes=[comb],
    )

    t = RTLToSMT2Translator()

    try:
        t.translate_component(comp)
        assert False, "Expected comb+sync drive conflict to be detected"
    except ValueError as e:
        assert "comb" in str(e).lower() and "sync" in str(e).lower()

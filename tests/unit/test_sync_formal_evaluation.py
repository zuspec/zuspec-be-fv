"""Solver-backed evaluation tests for sync processes with assert/cover.

These tests exercise Phase 7 (BMC / k-induction) end-to-end *if* an external SMT
solver is available. Set $ZUSPEC_SMT_SOLVER to pick a specific solver.
"""

import pytest
import zuspec.dataclasses as zdc

from zuspec.dataclasses.data_model_factory import DataModelFactory
from zuspec.be.fv.rtl import RTLToSMT2Translator
from zuspec.be.fv.verification import pick_solver, verify_bmc, prove_k_induction, verify_cover


def _require_solver() -> str:
    spec = pick_solver()
    if spec is None:
        pytest.skip("No external SMT solver found (set $ZUSPEC_SMT_SOLVER)")
    return spec.name


def test_bmc_finds_assert_violation():
    solver = _require_solver()

    @zdc.dataclass
    class BadProp(zdc.Component):
        clk: zdc.bit = zdc.input()
        count: zdc.bit8 = zdc.output()

        @zdc.sync(clock=lambda s: s.clk)
        def _proc(self):
            self.count = self.count + 1
            # Violable because count is unconstrained in the initial state
            assert self.count != 0

    factory = DataModelFactory()
    ctx = factory.build(BadProp)
    comp = ctx.type_m[BadProp.__qualname__]

    tr = RTLToSMT2Translator()
    m = tr.translate_component(comp)

    r = verify_bmc(m, depth=0, solver=solver, translator=tr, want_trace=False)

    # SAT => property violation exists
    assert r.holds is False


def test_k_induction_proves_tautological_assertion():
    solver = _require_solver()

    @zdc.dataclass
    class GoodProp(zdc.Component):
        clk: zdc.bit = zdc.input()
        count: zdc.bit8 = zdc.output()

        @zdc.sync(clock=lambda s: s.clk)
        def _proc(self):
            self.count = self.count + 1
            # Tautology (should be inductive even with partial transition semantics)
            assert self.count == self.count

    factory = DataModelFactory()
    ctx = factory.build(GoodProp)
    comp = ctx.type_m[GoodProp.__qualname__]

    tr = RTLToSMT2Translator()
    m = tr.translate_component(comp)

    r = prove_k_induction(m, k=1, solver=solver, translator=tr)
    assert r.holds is True


def test_cover_reachable_within_bound():
    solver = _require_solver()

    @zdc.dataclass
    class CoverProp(zdc.Component):
        clk: zdc.bit = zdc.input()
        count: zdc.bit8 = zdc.output()

        @zdc.sync(clock=lambda s: s.clk)
        def _proc(self):
            self.count = self.count + 1
            zdc.cover(self.count == 3)

    factory = DataModelFactory()
    ctx = factory.build(CoverProp)
    comp = ctx.type_m[CoverProp.__qualname__]

    tr = RTLToSMT2Translator()
    m = tr.translate_component(comp)

    r = verify_cover(m, depth=0, solver=solver, translator=tr)
    # Since state_0 is unconstrained, cover is reachable at depth 0
    assert r.holds is True

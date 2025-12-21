"""Tests for SMT2 translation of synchronous (@zdc.sync) logic with formal props.

These tests are intended to validate the be-fv RTL->SMT2 flow can extract:
- synchronous transition relations
- assert statements (as properties)
- cover goals

Note: These tests do not require any solver.
"""

import zuspec.dataclasses as zdc

from zuspec.dataclasses.data_model_factory import DataModelFactory
from zuspec.be.fv.rtl import RTLToSMT2Translator


def test_sync_process_with_assert_and_cover_translates():
    @zdc.dataclass
    class CounterWithFormal(zdc.Component):
        clk: zdc.bit = zdc.input()
        reset: zdc.bit = zdc.input()
        count: zdc.bit8 = zdc.output()

        @zdc.sync(clock=lambda s: s.clk, reset=lambda s: s.reset)
        def _proc(self):
            if self.reset:
                self.count = 0
            else:
                self.count = self.count + 1

            # Formal properties/coverage
            assert self.count != 0
            zdc.cover(self.count == 3)

    factory = DataModelFactory()
    ctx = factory.build(CounterWithFormal)
    comp = ctx.type_m[CounterWithFormal.__qualname__]

    tr = RTLToSMT2Translator()
    m = tr.translate_component(comp)

    # Sync process must produce transition constraints
    assert len(m.transitions) > 0

    # Assert/cover must be extracted
    assert len(m.assertions) > 0
    assert len(m.coverage_goals) > 0

    smt2 = tr.generate_smt2(m)

    # Assert is "count != 0" => translated using "distinct" and a zero constant.
    # Note: constants are inferred with minimal width (0 => #b0), then extended as needed.
    assert "distinct" in smt2
    assert "#b0" in smt2

    # Cover is "count == 3" => minimal constant is #b11 (then extended as needed)
    assert "#b11" in smt2


def test_conditional_assert_guarded_in_smt2():
    @zdc.dataclass
    class GuardedAssert(zdc.Component):
        clk: zdc.bit = zdc.input()
        en: zdc.bit = zdc.input()
        count: zdc.bit8 = zdc.output()

        @zdc.sync(clock=lambda s: s.clk)
        def _proc(self):
            if self.en:
                self.count = self.count + 1
                assert self.count != 7

    factory = DataModelFactory()
    ctx = factory.build(GuardedAssert)
    comp = ctx.type_m[GuardedAssert.__qualname__]

    tr = RTLToSMT2Translator()
    m = tr.translate_component(comp)
    smt2 = tr.generate_smt2(m)

    # Guarded asserts are emitted as (=> guard assertion)
    assert "=>" in smt2

    # 7 is inferred with minimal width => #b111 (then extended as needed)
    assert "#b111" in smt2

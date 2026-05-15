# Copyright 2019-2026 Matthew Ballance and contributors
# SPDX-License-Identifier: Apache-2.0
"""Unit tests for CounterFormalPass.

All tests run without a solver — they only verify property extraction,
BMC depth computation, and SVA string generation.
"""
import sys
import os

# Ensure zuspec packages are on path
_here = os.path.dirname(__file__)
_root = os.path.abspath(os.path.join(_here, "..", "..", "..", ".."))
sys.path.insert(0, os.path.join(_root, "packages", "zuspec-dataclasses", "src"))
sys.path.insert(0, os.path.join(_root, "packages", "zuspec-be-fv", "src"))

import pytest
import zuspec.dataclasses as zdc
from zuspec.dataclasses.modulo_counter import ModuloCounter
from zuspec.dataclasses.watchdog_counter import WatchdogCounter
from zuspec.dataclasses.counter import Counter
from zuspec.be.fv.passes import CounterFormalPass, CounterProperty


# ---------------------------------------------------------------------------
# Test components — must be module-level for DataModelFactory inspect.getsource
# ---------------------------------------------------------------------------

@zdc.dataclass
class BlinkerMod8(zdc.Component):
    led: zdc.u1 = zdc.field(default=0)
    cnt: ModuloCounter = zdc.inst(ModuloCounter, kwargs={'PERIOD': 8})

    @zdc.proc
    async def _run(self):
        while True:
            await self.cnt.wait_next()
            self.led = 1 - self.led


@zdc.dataclass
class WatchdogComp(zdc.Component):
    out: zdc.u1 = zdc.field(default=0)
    wdog: WatchdogCounter = zdc.inst(WatchdogCounter, kwargs={'TIMEOUT': 12})

    @zdc.proc
    async def _run(self):
        while True:
            await self.wdog.wait_next()
            self.out = 1 - self.out


@zdc.dataclass
class WaitForComp(zdc.Component):
    """Component with wait_for() calls for depth testing."""
    out: zdc.u1 = zdc.field(default=0)
    cnt: ModuloCounter = zdc.inst(ModuloCounter, kwargs={'PERIOD': 10})

    @zdc.proc
    async def _run(self):
        while True:
            await self.cnt.wait_for(4)
            self.out = 1 - self.out


@zdc.dataclass
class DualWaitForComp(zdc.Component):
    """Two wait_for calls in the same proc path."""
    out: zdc.u1 = zdc.field(default=0)
    cnt: ModuloCounter = zdc.inst(ModuloCounter, kwargs={'PERIOD': 16})

    @zdc.proc
    async def _run(self):
        while True:
            await self.cnt.wait_for(2)
            await self.cnt.wait_for(6)
            self.out = 1 - self.out


@zdc.dataclass
class DualCounterComp(zdc.Component):
    """Two independent counter sub-fields."""
    led: zdc.u1 = zdc.field(default=0)
    fast: ModuloCounter = zdc.inst(ModuloCounter, kwargs={'PERIOD': 4})
    slow: ModuloCounter = zdc.inst(ModuloCounter, kwargs={'PERIOD': 32})

    @zdc.proc
    async def _run(self):
        while True:
            await self.fast.wait_next()
            await self.slow.wait_next()
            self.led = 1 - self.led


@zdc.dataclass
class NoCounterComp(zdc.Component):
    """Component with no Counter sub-fields."""
    count: zdc.u8 = zdc.field(default=0)

    @zdc.proc
    async def _run(self):
        while True:
            self.count = self.count + 1
            await zdc.tick()


# ---------------------------------------------------------------------------
# BlinkerMod8 — ModuloCounter(PERIOD=8)
# ---------------------------------------------------------------------------

class TestModuloCounterProperties:
    @pytest.fixture(scope="class")
    def pass_(self):
        return CounterFormalPass(BlinkerMod8)

    def test_recognizes_counter(self, pass_):
        assert "cnt" in pass_.counter_names()

    def test_two_properties_per_counter(self, pass_):
        props = pass_.all_properties()
        assert len(props) == 2

    def test_range_invariant_present(self, pass_):
        ri = [p for p in pass_.all_properties() if p.kind == "range_invariant"]
        assert len(ri) == 1
        p = ri[0]
        assert p.counter_name == "cnt"
        assert p.modulus == 8
        assert p.width >= 3  # needs at least 3 bits for 0..7

    def test_monotone_progress_present(self, pass_):
        mp = [p for p in pass_.all_properties() if p.kind == "monotone_progress"]
        assert len(mp) == 1
        p = mp[0]
        assert p.counter_name == "cnt"
        assert p.modulus == 8

    def test_no_wait_for_calls(self, pass_):
        assert pass_.wait_for_depths() == []

    def test_min_depth_zero_without_wait_for(self, pass_):
        assert pass_.min_required_depth() == 0

    def test_range_invariant_sva_contains_modulus(self, pass_):
        # PERIOD=8 requires 3 bits (2^3=8=modulus): range invariant is tautological
        ri = pass_.range_invariant_properties()[0]
        sva = ri.to_sva()
        assert "tautological" in sva  # power-of-two: always in range

    def test_monotone_progress_sva_contains_rollover(self, pass_):
        mp = pass_.monotone_progress_properties()[0]
        sva = mp.to_sva()
        # SVA should handle rollover case (past == modulus-1 → 0)
        assert "7" in sva  # modulus - 1 = 7
        assert "== 0" in sva


# ---------------------------------------------------------------------------
# WatchdogCounter(TIMEOUT=12)
# ---------------------------------------------------------------------------

class TestWatchdogCounterProperties:
    @pytest.fixture(scope="class")
    def pass_(self):
        return CounterFormalPass(WatchdogComp)

    def test_recognizes_watchdog(self, pass_):
        assert "wdog" in pass_.counter_names()

    def test_modulus_12(self, pass_):
        ri = pass_.range_invariant_properties()
        assert ri[0].modulus == 12

    def test_range_invariant_sva(self, pass_):
        sva = pass_.range_invariant_properties()[0].to_sva()
        assert "12" in sva


# ---------------------------------------------------------------------------
# wait_for depth computation
# ---------------------------------------------------------------------------

class TestWaitForDepth:
    @pytest.fixture(scope="class")
    def pass_(self):
        return CounterFormalPass(WaitForComp)

    def test_wait_for_detected(self, pass_):
        depths = pass_.wait_for_depths()
        assert len(depths) == 1

    def test_wait_for_target_correct(self, pass_):
        cname, target, depth = pass_.wait_for_depths()[0]
        assert cname == "cnt"
        assert target == 4
        # depth = 4 % 10 = 4
        assert depth == 4

    def test_min_required_depth(self, pass_):
        assert pass_.min_required_depth() == 4


class TestDualWaitForDepth:
    @pytest.fixture(scope="class")
    def pass_(self):
        return CounterFormalPass(DualWaitForComp)

    def test_two_wait_for_calls(self, pass_):
        depths = pass_.wait_for_depths()
        assert len(depths) == 2

    def test_depths_correct(self, pass_):
        depths = {target: depth for _, target, depth in pass_.wait_for_depths()}
        # wait_for(2): delta = 2 % 16 = 2
        assert depths[2] == 2
        # wait_for(6): delta = 6 % 16 = 6
        assert depths[6] == 6

    def test_min_required_depth_is_max(self, pass_):
        assert pass_.min_required_depth() == 6


# ---------------------------------------------------------------------------
# Dual counter component
# ---------------------------------------------------------------------------

class TestDualCounterComponent:
    @pytest.fixture(scope="class")
    def pass_(self):
        return CounterFormalPass(DualCounterComp)

    def test_two_counters_recognized(self, pass_):
        names = pass_.counter_names()
        assert "fast" in names
        assert "slow" in names

    def test_four_properties(self, pass_):
        assert len(pass_.all_properties()) == 4

    def test_fast_counter_period_4(self, pass_):
        fast_ri = [p for p in pass_.range_invariant_properties()
                   if p.counter_name == "fast"]
        assert len(fast_ri) == 1
        assert fast_ri[0].modulus == 4

    def test_slow_counter_period_32(self, pass_):
        slow_ri = [p for p in pass_.range_invariant_properties()
                   if p.counter_name == "slow"]
        assert len(slow_ri) == 1
        assert slow_ri[0].modulus == 32


# ---------------------------------------------------------------------------
# Component with no counter fields
# ---------------------------------------------------------------------------

class TestNoCounterComponent:
    @pytest.fixture(scope="class")
    def pass_(self):
        return CounterFormalPass(NoCounterComp)

    def test_no_counters(self, pass_):
        assert pass_.counter_names() == []

    def test_no_properties(self, pass_):
        assert pass_.all_properties() == []

    def test_min_depth_zero(self, pass_):
        assert pass_.min_required_depth() == 0


# ---------------------------------------------------------------------------
# Property data class
# ---------------------------------------------------------------------------

class TestCounterPropertyDataclass:
    def test_is_dataclass(self):
        import dataclasses
        assert dataclasses.is_dataclass(CounterProperty)

    def test_fields(self):
        import dataclasses
        field_names = {f.name for f in dataclasses.fields(CounterProperty)}
        assert "counter_name" in field_names
        assert "kind" in field_names
        assert "modulus" in field_names
        assert "width" in field_names

    def test_to_sva_range(self):
        # Use modulus=10, width=4 — not a power of two, so invariant is non-trivial
        p = CounterProperty(
            counter_name="cnt",
            kind="range_invariant",
            modulus=10,
            width=4,
            description="test",
        )
        sva = p.to_sva()
        assert "cnt" in sva
        assert "10" in sva

    def test_to_sva_monotone_rollover(self):
        p = CounterProperty(
            counter_name="cnt",
            kind="monotone_progress",
            modulus=8,
            width=3,
            description="test",
        )
        sva = p.to_sva()
        # Should include rollover boundary (modulus - 1 = 7)
        assert "7" in sva
        assert "$past(cnt)" in sva

    def test_to_sva_power_of_two_range_is_comment(self):
        p = CounterProperty(
            counter_name="cnt",
            kind="range_invariant",
            modulus=16,
            width=4,  # 2^4 = 16, tautological
            description="test",
        )
        sva = p.to_sva()
        assert "tautological" in sva

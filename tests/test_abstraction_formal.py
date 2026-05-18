"""Phase 2 tests — AbstractionFormalPass interface-dispatch formal pass.

Covers:
* assert / assume mode property collection from Counter fields
* WatchdogCounter property collection
* min_required_depth() aggregation
* Empty result for components with no abstraction fields
* Multiple counter fields: depth is max
"""
from __future__ import annotations

import pytest
import zuspec.dataclasses as zdc
from zuspec.dataclasses.watchdog_counter import WatchdogCounter
from zuspec.be.fv.passes.abstraction_formal import AbstractionFormalPass


# ---------------------------------------------------------------------------
# Fixtures — simple components with counter fields
# ---------------------------------------------------------------------------

@zdc.dataclass
class _OneCounter(zdc.Component):
    cnt: zdc.Counter = zdc.inst(zdc.Counter, kwargs={"WIDTH": 4})


@zdc.dataclass
class _NoCounter(zdc.Component):
    value: zdc.u32 = zdc.field(default=0)


@zdc.dataclass
class _TwoCounters(zdc.Component):
    fast: zdc.Counter = zdc.inst(zdc.Counter, kwargs={"WIDTH": 4})    # period=16
    slow: zdc.Counter = zdc.inst(zdc.Counter, kwargs={"WIDTH": 8})   # period=256


@zdc.dataclass
class _ModuloComp(zdc.Component):
    baud: zdc.ModuloCounter = zdc.inst(zdc.ModuloCounter, kwargs={"PERIOD": 868})


@zdc.dataclass
class _WatchdogComp(zdc.Component):
    wdog: WatchdogCounter = zdc.inst(WatchdogCounter, kwargs={"TIMEOUT": 12})


# ---------------------------------------------------------------------------
# Assert mode
# ---------------------------------------------------------------------------

def test_counter_assert_properties_collected():
    fv = AbstractionFormalPass(_OneCounter, mode="assert")
    props = fv.all_properties()
    assert len(props) >= 2  # at least range_invariant comment + monotone_progress


def test_counter_assert_properties_contain_assert_keyword():
    fv = AbstractionFormalPass(_OneCounter, mode="assert")
    props = fv.all_properties()
    combined = " ".join(props)
    # Should have assert property or at least one tautological comment
    assert "assert property" in combined or "tautological" in combined


def test_counter_assert_monotone_progress_present():
    fv = AbstractionFormalPass(_OneCounter, mode="assert")
    props = fv.all_properties()
    combined = " ".join(props)
    assert "$past" in combined


# ---------------------------------------------------------------------------
# Assume mode
# ---------------------------------------------------------------------------

def test_counter_assume_properties_collected():
    fv = AbstractionFormalPass(_OneCounter, mode="assume")
    props = fv.all_properties()
    assert len(props) >= 1


def test_counter_assume_properties_contain_assume_keyword():
    fv = AbstractionFormalPass(_OneCounter, mode="assume")
    props = fv.all_properties()
    combined = " ".join(props)
    assert "assume" in combined
    assert "assert property" not in combined


# ---------------------------------------------------------------------------
# BMC depth
# ---------------------------------------------------------------------------

def test_bmc_depth_from_counter():
    fv = AbstractionFormalPass(_OneCounter, mode="assert")
    # WIDTH=4 → period=16
    assert fv.min_required_depth() == 16


def test_bmc_depth_modulo_counter():
    fv = AbstractionFormalPass(_ModuloComp, mode="assert")
    assert fv.min_required_depth() == 868


def test_bmc_depth_two_counters_is_max():
    fv = AbstractionFormalPass(_TwoCounters, mode="assert")
    # fast period=16, slow period=256 → max=256
    assert fv.min_required_depth() == 256


# ---------------------------------------------------------------------------
# Empty result
# ---------------------------------------------------------------------------

def test_no_counter_returns_empty_properties():
    fv = AbstractionFormalPass(_NoCounter, mode="assert")
    assert fv.all_properties() == []


def test_no_counter_returns_zero_depth():
    fv = AbstractionFormalPass(_NoCounter, mode="assert")
    assert fv.min_required_depth() == 0


# ---------------------------------------------------------------------------
# Invalid mode
# ---------------------------------------------------------------------------

def test_invalid_mode_raises_value_error():
    with pytest.raises(ValueError, match="mode must be"):
        AbstractionFormalPass(_OneCounter, mode="bad_mode")


# ---------------------------------------------------------------------------
# Multiple counters — all properties collected
# ---------------------------------------------------------------------------

def test_two_counters_properties_include_both():
    fv = AbstractionFormalPass(_TwoCounters, mode="assert")
    props = fv.all_properties()
    combined = " ".join(props)
    # Both counter field names should appear
    assert "fast" in combined
    assert "slow" in combined


# ---------------------------------------------------------------------------
# WatchdogCounter
# ---------------------------------------------------------------------------

def test_watchdog_counter_properties_collected():
    fv = AbstractionFormalPass(_WatchdogComp, mode="assert")
    props = fv.all_properties()
    assert len(props) >= 1


def test_watchdog_counter_bmc_depth():
    fv = AbstractionFormalPass(_WatchdogComp, mode="assert")
    # TIMEOUT=12 → period=12
    assert fv.min_required_depth() == 12


def test_watchdog_counter_properties_contain_wdog_name():
    fv = AbstractionFormalPass(_WatchdogComp, mode="assert")
    combined = " ".join(fv.all_properties())
    assert "wdog" in combined


def test_watchdog_counter_assume_mode():
    fv = AbstractionFormalPass(_WatchdogComp, mode="assume")
    props = fv.all_properties()
    combined = " ".join(props)
    assert "assume" in combined

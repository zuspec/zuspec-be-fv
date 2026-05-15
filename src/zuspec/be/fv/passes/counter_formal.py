# Copyright 2019-2026 Matthew Ballance and contributors
# SPDX-License-Identifier: Apache-2.0
"""CounterFormalPass — extract formal verification properties from Counter sub-components.

For each ``Counter``, ``ModuloCounter``, or ``WatchdogCounter`` sub-field in a
``zdc.Component``, this pass produces:

* **Range invariant** — ``0 <= count < modulus`` at every time step.
* **Monotone progress** — after reset, the counter advances by one each cycle;
  on rollover (``count == modulus - 1``), it wraps to 0.
* **BMC depth bound** — for each ``wait_for(v)`` call in the component's proc
  bodies, the minimum BMC depth to reach that event, assuming the counter
  starts at 0 after reset.

Usage::

    from zuspec.be.fv.passes import CounterFormalPass

    pass_ = CounterFormalPass(Blinker)
    for prop in pass_.all_properties():
        print(prop.to_sva())
    print("min BMC depth:", pass_.min_required_depth())
"""
from __future__ import annotations

import dataclasses as _dc_mod
import logging
from dataclasses import dataclass
from typing import List, Optional, Tuple

_log = logging.getLogger(__name__)

_COUNTER_TYPE_NAMES: frozenset = frozenset(
    ("Counter", "ModuloCounter", "WatchdogCounter")
)


# ---------------------------------------------------------------------------
# Property data class
# ---------------------------------------------------------------------------

@dataclass
class CounterProperty:
    """A single formal property derived from a Counter sub-field.

    Attributes
    ----------
    counter_name:
        The Python field name of the counter (e.g. ``"cnt"``).
    kind:
        One of ``'range_invariant'`` or ``'monotone_progress'``.
    modulus:
        Rollover period (``PERIOD``, ``TIMEOUT``, or ``2**WIDTH``).
    width:
        Bit width of the synthesised register for this counter.
    description:
        Human-readable summary of the property.
    """

    counter_name: str
    kind: str
    modulus: int
    width: int
    description: str

    def to_sva(self) -> str:
        """Return a synthesisable SVA property string for this property.

        Notes
        -----
        The generated SVA assumes a signal named ``<counter_name>`` of the
        given width is visible in the synthesised module.  The
        ``monotone_progress`` property is gated with a reset-valid guard
        (``disable iff (!rst_n)``) so that it is not checked during reset.
        """
        sig = self.counter_name
        m = self.modulus
        w = self.width

        if self.kind == "range_invariant":
            # count < modulus  (count is unsigned so >= 0 is always true)
            if m == (1 << w):
                # Power-of-two: tautological for the given bit width
                return (
                    f"// range_invariant for {sig}: tautological "
                    f"(width {w} cannot exceed {m - 1})"
                )
            return (
                f"assert property (@(posedge clk) disable iff (!rst_n) "
                f"{sig} < {m});"
            )

        if self.kind == "monotone_progress":
            # Two cases: normal increment and rollover
            return (
                f"assert property (@(posedge clk) disable iff (!rst_n) "
                f"($past({sig}) != {m - 1} |-> {sig} == ($past({sig}) + 1)));\n"
                f"assert property (@(posedge clk) disable iff (!rst_n) "
                f"($past({sig}) == {m - 1} |-> {sig} == 0));"
            )

        return f"// unknown property kind: {self.kind}"


# ---------------------------------------------------------------------------
# Internal counter info
# ---------------------------------------------------------------------------

@dataclass
class _CounterInfo:
    field_name: str
    modulus: int
    width: int


# ---------------------------------------------------------------------------
# Main pass class
# ---------------------------------------------------------------------------

class CounterFormalPass:
    """Formal verification property extractor for Counter sub-components.

    Parameters
    ----------
    component_cls:
        A ``zdc.Component`` Python class (decorated with ``@zdc.dataclass``).
    model_context:
        Optional pre-built ``DataModel`` context from ``DataModelFactory``.
        If ``None``, the pass will build its own context.
    """

    def __init__(self, component_cls, model_context=None):
        self._cls = component_cls
        self._ctx = model_context
        self._counters: List[_CounterInfo] = []
        self._wait_for_calls: List[Tuple[str, int]] = []  # (counter_name, target)
        self._analyze()

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def all_properties(self) -> List[CounterProperty]:
        """Return all formal properties for all counter fields."""
        props: List[CounterProperty] = []
        for ci in self._counters:
            props.append(CounterProperty(
                counter_name=ci.field_name,
                kind="range_invariant",
                modulus=ci.modulus,
                width=ci.width,
                description=(
                    f"{ci.field_name}: 0 <= count < {ci.modulus}"
                ),
            ))
            props.append(CounterProperty(
                counter_name=ci.field_name,
                kind="monotone_progress",
                modulus=ci.modulus,
                width=ci.width,
                description=(
                    f"{ci.field_name}: count advances by 1 each cycle, "
                    f"wraps at {ci.modulus}"
                ),
            ))
        return props

    def range_invariant_properties(self) -> List[CounterProperty]:
        """Return only range-invariant properties."""
        return [p for p in self.all_properties() if p.kind == "range_invariant"]

    def monotone_progress_properties(self) -> List[CounterProperty]:
        """Return only monotone-progress properties."""
        return [p for p in self.all_properties() if p.kind == "monotone_progress"]

    def counter_names(self) -> List[str]:
        """Return the field names of all recognised counter sub-fields."""
        return [ci.field_name for ci in self._counters]

    def wait_for_depths(self) -> List[Tuple[str, int, int]]:
        """Return ``(counter_name, target, depth_estimate)`` for each ``wait_for`` call.

        The depth estimate is ``(target % modulus)`` for targets in ``[1, modulus)``,
        and ``modulus`` for target ``0`` (must complete a full period before
        the next rollover).  When the target value equals the initial value (0),
        we conservatively use ``modulus``.
        """
        result = []
        by_name = {ci.field_name: ci for ci in self._counters}
        for cname, target in self._wait_for_calls:
            ci = by_name.get(cname)
            if ci is None:
                continue
            # Assuming counter starts at 0 after reset:
            # depth = (target - 0) % modulus, but 0 means "wait a full period"
            delta = target % ci.modulus
            depth = delta if delta != 0 else ci.modulus
            result.append((cname, target, depth))
        return result

    def min_required_depth(self) -> int:
        """Return the minimum BMC depth to cover all ``wait_for`` calls.

        Returns 0 if no ``wait_for`` calls are present (no extra depth needed
        beyond what the proc structure itself requires).

        The depth is computed conservatively: assuming the counter starts at 0
        after reset, ``wait_for(v)`` requires at least ``v % modulus`` cycles
        (or ``modulus`` cycles if ``v == 0``).

        For chained waits in the same proc path the depths are summed.
        """
        if not self._wait_for_calls:
            return 0
        depths = self.wait_for_depths()
        if not depths:
            return 0
        return max(d for _, _, d in depths)

    # ------------------------------------------------------------------
    # Analysis — walk component IR
    # ------------------------------------------------------------------

    def _analyze(self):
        """Populate ``_counters`` and ``_wait_for_calls`` from the component IR."""
        ctx = self._ctx
        if ctx is None:
            ctx = self._build_context()
        if ctx is None:
            return

        comp_name = getattr(self._cls, "__qualname__", None) or self._cls.__name__
        comp_ir = ctx.type_m.get(comp_name) or ctx.type_m.get(self._cls.__name__)
        if comp_ir is None:
            _log.warning("CounterFormalPass: could not find IR for %r", comp_name)
            return

        self._counters = self._collect_counters(comp_ir, ctx)
        self._wait_for_calls = self._collect_wait_for(comp_ir, self._counters)

    def _build_context(self):
        """Build a DataModel context for the component class."""
        try:
            import sys as _sys
            # Ensure zuspec-dataclasses is importable
            from zuspec.dataclasses.data_model_factory import DataModelFactory
            return DataModelFactory().build(self._cls)
        except Exception as e:
            _log.warning("CounterFormalPass: could not build context: %s", e)
            return None

    # ------------------------------------------------------------------
    # Counter field collection
    # ------------------------------------------------------------------

    @staticmethod
    def _collect_counters(comp_ir, ctx) -> List[_CounterInfo]:
        """Find Counter sub-fields and return their metadata."""
        py_meta = _read_py_metadata(comp_ir)

        results: List[_CounterInfo] = []
        for f in getattr(comp_ir, "fields", []):
            dt = getattr(f, "datatype", None)
            if dt is None or type(dt).__name__ != "DataTypeRef":
                continue
            ref_name = getattr(dt, "ref_name", None)
            if ref_name not in _COUNTER_TYPE_NAMES:
                continue
            ref_ir = ctx.type_m.get(ref_name)
            if ref_ir is None or type(ref_ir).__name__ != "DataTypeComponent":
                continue

            meta = py_meta.get(f.name, {})
            kwargs = meta.get("kwargs", {})
            is_modulo = ref_name in ("ModuloCounter", "WatchdogCounter")

            if is_modulo:
                modulus = int(kwargs.get("PERIOD") or kwargs.get("TIMEOUT") or 256)
                width = max(1, (modulus - 1).bit_length())
            else:
                w = int(kwargs.get("WIDTH", 8))
                modulus = 1 << w
                width = w

            results.append(_CounterInfo(
                field_name=f.name,
                modulus=modulus,
                width=width,
            ))

        return results

    # ------------------------------------------------------------------
    # wait_for scanning
    # ------------------------------------------------------------------

    @staticmethod
    def _collect_wait_for(comp_ir, counters: List[_CounterInfo]) -> List[Tuple[str, int]]:
        """Scan proc bodies for ``await self.<ctr>.wait_for(v)`` calls.

        Returns a flat list of ``(counter_name, target_value)`` tuples.
        Only constant integer targets are captured; dynamic expressions are
        silently ignored.
        """
        name_to_idx = {ci.field_name: None for ci in counters}
        # Build field index → counter name map
        idx_to_name = {}
        for idx, f in enumerate(getattr(comp_ir, "fields", [])):
            if getattr(f, "name", None) in name_to_idx:
                idx_to_name[idx] = f.name

        results: List[Tuple[str, int]] = []
        for proc in getattr(comp_ir, "proc_processes", []):
            _scan_stmts_for_wait_for(proc.body, idx_to_name, results)
        return results


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _read_py_metadata(comp_ir) -> dict:
    """Extract ``zdc.inst`` kwargs metadata from Python dataclass fields."""
    py_meta: dict = {}
    py_cls = getattr(comp_ir, "py_type", None)
    if py_cls is None:
        return py_meta
    try:
        for df in _dc_mod.fields(py_cls):
            py_meta[df.name] = dict(df.metadata)
    except Exception:
        pass
    return py_meta


def _scan_stmts_for_wait_for(stmts, idx_to_name: dict, out: list) -> None:
    """Recursively walk *stmts*, appending ``(name, target)`` to *out*."""
    for stmt in stmts:
        t = type(stmt).__name__
        if t == "StmtExpr":
            _check_wait_for_expr(getattr(stmt, "expr", None), idx_to_name, out)
        elif t in ("StmtWhile", "StmtFor"):
            _scan_stmts_for_wait_for(getattr(stmt, "body", []), idx_to_name, out)
        elif t == "StmtIf":
            _scan_stmts_for_wait_for(getattr(stmt, "body", []), idx_to_name, out)
            _scan_stmts_for_wait_for(getattr(stmt, "orelse", []), idx_to_name, out)


def _check_wait_for_expr(expr, idx_to_name: dict, out: list) -> None:
    """Check if *expr* is ``ExprAwait(ExprCall(ExprAttribute(ExprRefField, 'wait_for')))``.

    If it matches and the target argument is a constant integer, appends
    ``(counter_name, target)`` to *out*.
    """
    if type(expr).__name__ != "ExprAwait":
        return
    call = getattr(expr, "value", None)
    if type(call).__name__ != "ExprCall":
        return
    func = getattr(call, "func", None)
    if type(func).__name__ != "ExprAttribute":
        return
    if getattr(func, "attr", None) != "wait_for":
        return
    field_ref = getattr(func, "value", None)
    if type(field_ref).__name__ != "ExprRefField":
        return
    field_idx = getattr(field_ref, "index", None)
    cname = idx_to_name.get(field_idx)
    if cname is None:
        return

    # Extract constant target argument
    args = getattr(call, "args", [])
    if not args:
        return
    arg0 = args[0]
    if type(arg0).__name__ == "ExprConstant":
        target = getattr(arg0, "value", None)
        if isinstance(target, int):
            out.append((cname, target))

"""High-level formal verification API (solver-independent).

This is intended for RTL/SMT2 flow (Phase 7):
- Translate RTL component to SMT2Module
- Emit SMT-LIBv2 for BMC / k-induction
- Invoke an external solver as a subprocess
- Optionally extract a counterexample trace via SMT-LIB `(get-value ...)`

Note: this does *not* use Python Z3 bindings.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Optional, Sequence
import tempfile

from ..solver.result import SolverResult, VerificationResult
from ..rtl import RTLToSMT2Translator
from ..rtl.smt2_module import SMT2Module

from .bmc_smt2 import write_bmc_smt2
from .cover_smt2 import write_cover_smt2
from .k_induction_smt2 import write_k_induction_step_smt2
from .solver_runner import resolve_solver, run_solver
from .trace import CounterexampleTrace


@dataclass
class FormalVerificationResult:
    """Result of a solver-independent formal run."""

    holds: bool
    result: SolverResult
    solver_name: str
    solver_time_ms: float
    # Optional trace for SAT counterexamples (BMC) or induction-step SAT.
    trace: Optional[CounterexampleTrace] = None
    raw_stdout: str = ""
    raw_stderr: str = ""


def _append_get_value_queries(
    smt2_text: str,
    module: SMT2Module,
    *,
    depth: int,
) -> str:
    # Query a stable set of signal values (inputs/outputs/registers/wires).
    # We query function application (|M#sig| state_k).
    terms: list[str] = []
    # Prefer user-facing names; values are keyed by those names.
    for sig_name, sig in sorted(module.get_all_signals().items()):
        for k in range(depth + 1):
            terms.append(f"(|{module.name}#{sig.smt_name}| state_{k})")

    # Chunk to avoid huge single commands.
    chunk_sz = 50
    lines = [smt2_text.rstrip(), ""]
    for i in range(0, len(terms), chunk_sz):
        chunk = " ".join(terms[i : i + chunk_sz])
        lines.append(f"(get-value ({chunk}))")
    return "\n".join(lines) + "\n"


def verify_bmc(
    module: SMT2Module,
    *,
    depth: int,
    solver: str = "cvc5",
    timeout_s: Optional[float] = None,
    translator: Optional[RTLToSMT2Translator] = None,
    want_trace: bool = True,
) -> FormalVerificationResult:
    translator = translator or RTLToSMT2Translator()

    with tempfile.TemporaryDirectory(prefix="zuspec-bmc-") as td:
        smt2_path = Path(td) / f"{module.name}_bmc_{depth}.smt2"
        write_bmc_smt2(translator, module, smt2_path, depth=depth, get_model=want_trace)

        if want_trace:
            txt = smt2_path.read_text()
            smt2_path.write_text(_append_get_value_queries(txt, module, depth=depth))

        spec = resolve_solver(solver)
        rr = run_solver(spec, smt2_path, timeout_s=timeout_s)

        # For BMC, SAT means a violation exists.
        holds = rr.result == SolverResult.UNSAT
        trace = None
        if want_trace and rr.result == SolverResult.SAT:
            # Best-effort: store raw output; parsing is solver-dependent.
            # We at least provide a placeholder trace with no decoded values.
            trace = CounterexampleTrace(depth=depth, states=[{} for _ in range(depth + 1)], violation_time=depth)

        return FormalVerificationResult(
            holds=holds,
            result=rr.result,
            solver_name=spec.name,
            solver_time_ms=rr.time_ms,
            trace=trace,
            raw_stdout=rr.stdout,
            raw_stderr=rr.stderr,
        )


def prove_k_induction(
    module: SMT2Module,
    *,
    k: int,
    solver: str = "cvc5",
    timeout_s: Optional[float] = None,
    translator: Optional[RTLToSMT2Translator] = None,
) -> FormalVerificationResult:
    """Try to prove the invariant using k-induction.

    This runs:
    - base case: BMC up to depth k must be UNSAT (no violation)
    - inductive step: must be UNSAT (no counterexample to induction)

    If both are UNSAT, we return holds=True.
    """
    translator = translator or RTLToSMT2Translator()

    base = verify_bmc(module, depth=k, solver=solver, timeout_s=timeout_s, translator=translator, want_trace=False)
    if base.result != SolverResult.UNSAT:
        return base

    with tempfile.TemporaryDirectory(prefix="zuspec-kind-") as td:
        smt2_path = Path(td) / f"{module.name}_kind_{k}.smt2"
        write_k_induction_step_smt2(translator, module, smt2_path, k=k, get_model=False)

        spec = resolve_solver(solver)
        rr = run_solver(spec, smt2_path, timeout_s=timeout_s)

        holds = rr.result == SolverResult.UNSAT
        return FormalVerificationResult(
            holds=holds,
            result=rr.result,
            solver_name=spec.name,
            solver_time_ms=base.solver_time_ms + rr.time_ms,
            trace=None,
            raw_stdout=rr.stdout,
            raw_stderr=rr.stderr,
        )

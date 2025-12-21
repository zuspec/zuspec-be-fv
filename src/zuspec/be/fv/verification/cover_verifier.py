"""High-level cover checking API (solver-independent)."""

from __future__ import annotations

from pathlib import Path
from typing import Optional
import tempfile

from ..solver.result import SolverResult
from ..rtl import RTLToSMT2Translator
from ..rtl.smt2_module import SMT2Module

from .cover_smt2 import write_cover_smt2
from .solver_runner import resolve_solver, run_solver
from .verifier import FormalVerificationResult


def verify_cover(
    module: SMT2Module,
    *,
    depth: int,
    solver: str = "cvc5",
    timeout_s: Optional[float] = None,
    translator: Optional[RTLToSMT2Translator] = None,
) -> FormalVerificationResult:
    """Check whether a cover goal is reachable within the bound.

    SAT means reachable, UNSAT means not reachable within bound.
    """
    translator = translator or RTLToSMT2Translator()

    with tempfile.TemporaryDirectory(prefix="zuspec-cover-") as td:
        smt2_path = Path(td) / f"{module.name}_cover_{depth}.smt2"
        write_cover_smt2(translator, module, smt2_path, depth=depth, get_model=False)

        spec = resolve_solver(solver)
        rr = run_solver(spec, smt2_path, timeout_s=timeout_s)

        holds = rr.result == SolverResult.SAT
        return FormalVerificationResult(
            holds=holds,
            result=rr.result,
            solver_name=spec.name,
            solver_time_ms=rr.time_ms,
            trace=None,
            raw_stdout=rr.stdout,
            raw_stderr=rr.stderr,
        )

"""Run SMT solvers as subprocesses over SMT-LIBv2 files.

Solvers are expected to accept the SMT2 file as a positional argument and print
one of: sat/unsat/unknown.
"""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Optional, Sequence, Tuple
import os
import shutil
import subprocess
import time

from ..solver.result import SolverResult


@dataclass(frozen=True)
class SolverSpec:
    """Describes how to invoke an external SMT solver."""

    name: str
    argv: Tuple[str, ...]


@dataclass(frozen=True)
class SolverRunResult:
    result: SolverResult
    stdout: str
    stderr: str
    returncode: int
    time_ms: float


_KNOWN_SOLVERS = {
    "z3": SolverSpec("z3", ("z3", "-smt2")),
    "cvc5": SolverSpec("cvc5", ("cvc5", "--lang", "smt2")),
    "cvc4": SolverSpec("cvc4", ("cvc4", "--lang", "smt2")),
    "yices": SolverSpec("yices", ("yices-smt2",)),
    "yices-smt2": SolverSpec("yices-smt2", ("yices-smt2",)),
    "boolector": SolverSpec("boolector", ("boolector", "--smt2")),
    "bitwuzla": SolverSpec("bitwuzla", ("bitwuzla", "--smt2")),
}


def resolve_solver(name_or_path: str) -> SolverSpec:
    """Resolve a solver name to an invocation spec."""
    if name_or_path in _KNOWN_SOLVERS:
        return _KNOWN_SOLVERS[name_or_path]

    p = Path(name_or_path)
    return SolverSpec(p.name or str(p), (str(p),))


def is_solver_available(name_or_path: str) -> bool:
    """Return True if the solver executable appears runnable on this system."""
    spec = resolve_solver(name_or_path)
    exe = spec.argv[0]

    # Explicit path
    if os.path.sep in exe or (os.path.altsep and os.path.altsep in exe):
        return os.path.exists(exe) and os.access(exe, os.X_OK)

    return shutil.which(exe) is not None


def pick_solver(preferred: Sequence[str] = ("cvc5", "z3", "yices-smt2")) -> Optional[SolverSpec]:
    """Pick the first available solver from a preference list.

    Users can override by setting $ZUSPEC_SMT_SOLVER.
    """
    env = os.environ.get("ZUSPEC_SMT_SOLVER")
    if env and is_solver_available(env):
        return resolve_solver(env)

    for n in preferred:
        if is_solver_available(n):
            return resolve_solver(n)

    return None


def _parse_solver_result(stdout: str) -> SolverResult:
    for line in stdout.splitlines():
        s = line.strip()
        if not s or s.startswith(";"):
            continue
        if s == "sat":
            return SolverResult.SAT
        if s == "unsat":
            return SolverResult.UNSAT
        if s == "unknown":
            return SolverResult.UNKNOWN
    return SolverResult.UNKNOWN


def run_solver(
    solver: SolverSpec,
    smt2_file: str | Path,
    *,
    timeout_s: Optional[float] = None,
    extra_args: Sequence[str] = (),
) -> SolverRunResult:
    """Run solver on an SMT2 file."""
    smt2_path = Path(smt2_file)
    argv = [*solver.argv, *extra_args, str(smt2_path)]

    t0 = time.time()
    p = subprocess.run(
        argv,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=timeout_s,
    )
    dt_ms = (time.time() - t0) * 1000.0

    res = _parse_solver_result(p.stdout)
    return SolverRunResult(
        result=res,
        stdout=p.stdout,
        stderr=p.stderr,
        returncode=p.returncode,
        time_ms=dt_ms,
    )

"""SMT-LIB based verification (solver-independent).

This package is intentionally solver-agnostic: it emits SMT-LIBv2 problems and
runs external solvers (z3/cvc5/yices/etc) as subprocesses.
"""

from .solver_runner import (
    SolverSpec,
    SolverRunResult,
    resolve_solver,
    run_solver,
    is_solver_available,
    pick_solver,
)
from .bmc_smt2 import generate_bmc_smt2, write_bmc_smt2
from .cover_smt2 import generate_cover_smt2, write_cover_smt2
from .k_induction_smt2 import generate_k_induction_step_smt2, write_k_induction_step_smt2
from .trace import CounterexampleTrace
from .verifier import FormalVerificationResult, verify_bmc, prove_k_induction
from .cover_verifier import verify_cover

__all__ = [
    "SolverSpec",
    "SolverRunResult",
    "resolve_solver",
    "run_solver",
    "is_solver_available",
    "pick_solver",
    "generate_bmc_smt2",
    "write_bmc_smt2",
    "generate_cover_smt2",
    "write_cover_smt2",
    "generate_k_induction_step_smt2",
    "write_k_induction_step_smt2",
    "CounterexampleTrace",
    "FormalVerificationResult",
    "verify_bmc",
    "prove_k_induction",
    "verify_cover",
]

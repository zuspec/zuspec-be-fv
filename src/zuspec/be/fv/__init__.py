"""Formal verification backend for Zuspec.

This package contains two layers:
- SMT-LIB generation (eg RTL -> SMT2) and solver-independent runners
- Optional Python-backed solvers (eg Z3 bindings) for dataclass-level checks

Importing `zuspec.be.fv` must *not* require the Python Z3 bindings.
"""

__version__ = "0.1.0"

# Always-available pieces (no solver dependency)
from . import rtl as rtl
from . import verification as verification

from .rtl import *  # noqa: F401,F403
from .solver.result import VerificationResult, SolverResult  # noqa: F401
from .verification import *  # noqa: F401,F403

# Optional (requires Python Z3 bindings)
try:
    from .solver import SolverBackend, Z3Solver  # noqa: F401
    from .translator import TypeTranslator, DataModelTranslator  # noqa: F401
    from .analysis import BoundsAnalyzer  # noqa: F401
    from .checker import (  # noqa: F401
        check_bounds,
        check_invariant,
        check_no_overflow,
        find_bounds_violation,
    )
except Exception:  # pragma: no cover
    SolverBackend = None  # type: ignore
    Z3Solver = None  # type: ignore
    TypeTranslator = None  # type: ignore
    DataModelTranslator = None  # type: ignore
    BoundsAnalyzer = None  # type: ignore
    check_bounds = None  # type: ignore
    check_invariant = None  # type: ignore
    check_no_overflow = None  # type: ignore
    find_bounds_violation = None  # type: ignore

__all__ = [
    # solver-independent
    "VerificationResult",
    "SolverResult",
    # rtl + verification exports
    *rtl.__all__,  # type: ignore[name-defined]
    *verification.__all__,  # type: ignore[name-defined]
    # optional
    "SolverBackend",
    "Z3Solver",
    "TypeTranslator",
    "DataModelTranslator",
    "BoundsAnalyzer",
    "check_bounds",
    "check_invariant",
    "check_no_overflow",
    "find_bounds_violation",
]

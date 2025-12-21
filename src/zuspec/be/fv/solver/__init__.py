"""Solver abstraction layer for formal verification.

Note: the Python Z3 bindings are optional. Importing this package should not
require Z3 unless you explicitly use the Z3 backend.
"""

from .base import SolverBackend
from .result import VerificationResult, SolverResult

try:
    from .z3_solver import Z3Solver  # type: ignore
except Exception:  # pragma: no cover
    Z3Solver = None  # type: ignore

__all__ = [
    "SolverBackend",
    "VerificationResult",
    "SolverResult",
    "Z3Solver",
]

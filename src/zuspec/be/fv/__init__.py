"""
Formal verification backend for Zuspec dataclasses.

This package provides tools for formally verifying properties of
Zuspec dataclass definitions using SMT solvers.
"""

__version__ = "0.1.0"

from .solver import (
    SolverBackend,
    VerificationResult,
    SolverResult,
    Z3Solver,
)
from .translator import TypeTranslator, DataModelTranslator
from .analysis import BoundsAnalyzer
from .checker import (
    check_bounds,
    check_invariant,
    check_no_overflow,
    find_bounds_violation,
)

__all__ = [
    "SolverBackend",
    "VerificationResult",
    "SolverResult",
    "Z3Solver",
    "TypeTranslator",
    "DataModelTranslator",
    "BoundsAnalyzer",
    "check_bounds",
    "check_invariant",
    "check_no_overflow",
    "find_bounds_violation",
]

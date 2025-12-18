"""
Solver abstraction layer for formal verification.

This module provides a pluggable interface for different SMT solvers.
"""

from .base import SolverBackend
from .result import VerificationResult, SolverResult
from .z3_solver import Z3Solver

__all__ = [
    "SolverBackend",
    "VerificationResult", 
    "SolverResult",
    "Z3Solver",
]

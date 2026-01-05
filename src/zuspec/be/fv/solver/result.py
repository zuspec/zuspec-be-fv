"""
Verification result types.
"""
from dataclasses import dataclass
from enum import Enum
from typing import Optional, Dict, Any


class SolverResult(Enum):
    """Result from SMT solver check."""
    SAT = "sat"
    UNSAT = "unsat"
    UNKNOWN = "unknown"


@dataclass
class VerificationResult:
    """Result of a verification check.
    
    Attributes:
        holds: True if the property holds (unsat), False if violated (sat)
        counterexample: Variable assignments if property is violated (sat case)
        solver_time_ms: Time taken by solver in milliseconds
        solver_name: Name of the solver backend used
        result: Raw solver result (SAT/UNSAT/UNKNOWN)
    """
    holds: bool
    counterexample: Optional[Dict[str, Any]] = None
    solver_time_ms: float = 0.0
    solver_name: str = "unknown"
    result: SolverResult = SolverResult.UNKNOWN
    
    def __str__(self) -> str:
        if self.holds:
            return f"Property holds ({self.solver_name}, {self.solver_time_ms:.2f}ms)"
        else:
            cex_str = ", ".join(f"{k}={v}" for k, v in (self.counterexample or {}).items())
            return f"Property violated: {cex_str} ({self.solver_name}, {self.solver_time_ms:.2f}ms)"

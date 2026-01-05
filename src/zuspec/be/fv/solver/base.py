"""
Abstract base interface for SMT solver backends.
"""
from typing import Protocol, Any, Optional, Dict
from .result import VerificationResult


class SolverBackend(Protocol):
    """Protocol defining the interface for SMT solver backends.
    
    This allows pluggable solver implementations (Z3, CVC5, Yices, etc.)
    while maintaining a consistent API.
    """
    
    def add_constraint(self, constraint: Any) -> None:
        """Add a constraint to the solver.
        
        Args:
            constraint: Solver-specific constraint object
        """
        ...
    
    def check_sat(self) -> VerificationResult:
        """Check satisfiability of added constraints.
        
        Returns:
            VerificationResult with sat/unsat status and optional model
        """
        ...
    
    def get_model(self) -> Optional[Dict[str, Any]]:
        """Get a model (variable assignments) for satisfiable constraints.
        
        Returns:
            Dictionary mapping variable names to values, or None if unsat
        """
        ...
    
    def push(self) -> None:
        """Push a new assertion scope (optional for simple solvers)."""
        ...
    
    def pop(self) -> None:
        """Pop the most recent assertion scope (optional for simple solvers)."""
        ...
    
    def reset(self) -> None:
        """Reset the solver state, clearing all constraints."""
        ...

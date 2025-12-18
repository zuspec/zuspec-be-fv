"""
Z3 SMT solver backend implementation.
"""
import time
from typing import Any, Optional, Dict
import z3

from .result import VerificationResult, SolverResult


class Z3Solver:
    """Z3 solver backend wrapper.
    
    Provides a clean interface to Z3 solver functionality.
    """
    
    def __init__(self):
        """Initialize Z3 solver instance."""
        self.solver = z3.Solver()
        self._variables: Dict[str, Any] = {}
    
    def add_constraint(self, constraint: Any) -> None:
        """Add a Z3 constraint to the solver.
        
        Args:
            constraint: Z3 boolean expression
        """
        self.solver.add(constraint)
    
    def check_sat(self) -> VerificationResult:
        """Check satisfiability of constraints.
        
        Returns:
            VerificationResult with status and optional counterexample
        """
        start_time = time.time()
        result = self.solver.check()
        elapsed_ms = (time.time() - start_time) * 1000
        
        if result == z3.sat:
            model = self.get_model()
            return VerificationResult(
                holds=False,
                counterexample=model,
                solver_time_ms=elapsed_ms,
                solver_name="z3",
                result=SolverResult.SAT
            )
        elif result == z3.unsat:
            return VerificationResult(
                holds=True,
                counterexample=None,
                solver_time_ms=elapsed_ms,
                solver_name="z3",
                result=SolverResult.UNSAT
            )
        else:
            return VerificationResult(
                holds=False,
                counterexample=None,
                solver_time_ms=elapsed_ms,
                solver_name="z3",
                result=SolverResult.UNKNOWN
            )
    
    def get_model(self) -> Optional[Dict[str, Any]]:
        """Extract model from Z3 solver.
        
        Returns:
            Dictionary mapping variable names to their values
        """
        if self.solver.check() != z3.sat:
            return None
        
        model = self.solver.model()
        result = {}
        
        for decl in model:
            name = decl.name()
            value = model[decl]
            
            # Convert Z3 values to Python types
            if z3.is_int_value(value):
                result[name] = value.as_long()
            elif z3.is_bv_value(value):
                result[name] = value.as_long()
            elif z3.is_true(value):
                result[name] = True
            elif z3.is_false(value):
                result[name] = False
            else:
                result[name] = str(value)
        
        return result
    
    def push(self) -> None:
        """Push a new assertion scope."""
        self.solver.push()
    
    def pop(self) -> None:
        """Pop the most recent assertion scope."""
        self.solver.pop()
    
    def reset(self) -> None:
        """Reset solver state."""
        self.solver.reset()
    
    def register_variable(self, name: str, var: Any) -> None:
        """Register a Z3 variable for later reference.
        
        Args:
            name: Variable name
            var: Z3 variable object
        """
        self._variables[name] = var
    
    def get_variable(self, name: str) -> Optional[Any]:
        """Get a registered Z3 variable.
        
        Args:
            name: Variable name
            
        Returns:
            Z3 variable object or None
        """
        return self._variables.get(name)

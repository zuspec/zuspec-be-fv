"""
Bounds checking analysis for memory accesses and arithmetic operations.
"""
from typing import Dict, Optional, Any
import sys
import time
sys.path.insert(0, 'packages/zuspec-dataclasses/src')

try:
    from zuspec.dataclasses import dm
except ImportError:
    dm = None

from ..solver.z3_solver import Z3Solver
from ..solver.result import VerificationResult, SolverResult
from ..translator.dm_to_smt import DataModelTranslator


class BoundsAnalyzer:
    """Analyzer for bounds checking on memory accesses and arithmetic.
    
    Provides analysis for:
    - Simple bounds: addr + size <= memory_bound
    - Overflow detection: addr + size doesn't overflow bit width
    - Non-overlapping regions: src_end <= dst_start OR dst_end <= src_start
    """
    
    def __init__(self, solver_backend: Optional[Any] = None):
        """Initialize bounds analyzer.
        
        Args:
            solver_backend: SMT solver backend (defaults to Z3Solver)
        """
        self.solver = solver_backend or Z3Solver()
        self.translator = DataModelTranslator()
    
    def check_memory_access(self, 
                          base: str, 
                          size: str, 
                          bound: int,
                          struct_type: Any) -> VerificationResult:
        """Check if memory access base + size stays within bounds.
        
        Args:
            base: Name of base address field
            size: Name of size field
            bound: Upper bound for memory region
            struct_type: DataTypeStruct containing the fields
            
        Returns:
            VerificationResult indicating if access is safe
        """
        start_time = time.time()
        
        # Reset solver for clean state
        self.solver.reset()
        
        # Translate struct to SMT problem
        problem = self.translator.translate_struct(struct_type)
        
        # Add all field constraints to solver
        for constraint in problem.constraints:
            self.solver.add_constraint(constraint)
        
        # Get the field variables
        if base not in problem.variables:
            raise ValueError(f"Field '{base}' not found in struct")
        if size not in problem.variables:
            raise ValueError(f"Field '{size}' not found in struct")
        
        base_var = problem.variables[base]
        size_var = problem.variables[size]
        
        # Ensure both variables have the same bit width for Z3 operations
        import z3
        base_width = base_var.size()
        size_width = size_var.size()
        
        if base_width > size_width:
            # Extend size to match base width
            size_var = z3.ZeroExt(base_width - size_width, size_var)
        elif size_width > base_width:
            # Extend base to match size width
            base_var = z3.ZeroExt(size_width - base_width, base_var)
        
        # Add the violation condition: base + size > bound
        # We check for violations (SAT = violation exists, UNSAT = safe)
        violation = base_var + size_var > bound
        self.solver.add_constraint(violation)
        
        # Check satisfiability and get raw Z3 result
        result = self.solver.check_sat()
        
        elapsed_ms = (time.time() - start_time) * 1000
        
        if result.result == SolverResult.SAT:
            # Violation found - get counterexample
            model = self.solver.get_model()
            return VerificationResult(
                holds=False,
                counterexample=model,
                solver_time_ms=elapsed_ms,
                solver_name="z3",
                result=SolverResult.SAT
            )
        elif result.result == SolverResult.UNSAT:
            # No violation possible - property holds
            return VerificationResult(
                holds=True,
                counterexample=None,
                solver_time_ms=elapsed_ms,
                solver_name="z3",
                result=SolverResult.UNSAT
            )
        else:
            # Unknown result
            return VerificationResult(
                holds=False,
                counterexample=None,
                solver_time_ms=elapsed_ms,
                solver_name="z3",
                result=SolverResult.UNKNOWN
            )
    
    def check_no_overflow(self,
                         field1: str,
                         field2: str,
                         struct_type: Any) -> VerificationResult:
        """Check that field1 + field2 doesn't overflow.
        
        Args:
            field1: Name of first field
            field2: Name of second field
            struct_type: DataTypeStruct containing the fields
            
        Returns:
            VerificationResult indicating if overflow is possible
        """
        start_time = time.time()
        
        # Reset solver for clean state
        self.solver.reset()
        
        # Translate struct to SMT problem
        problem = self.translator.translate_struct(struct_type)
        
        # Add all field constraints to solver
        for constraint in problem.constraints:
            self.solver.add_constraint(constraint)
        
        # Get the field variables and their info
        if field1 not in problem.variables:
            raise ValueError(f"Field '{field1}' not found in struct")
        if field2 not in problem.variables:
            raise ValueError(f"Field '{field2}' not found in struct")
        
        var1 = problem.variables[field1]
        var2 = problem.variables[field2]
        
        # Ensure both variables have the same bit width for Z3 operations
        import z3
        width1 = var1.size()
        width2 = var2.size()
        
        if width1 > width2:
            var2 = z3.ZeroExt(width1 - width2, var2)
            max_width = width1
        elif width2 > width1:
            var1 = z3.ZeroExt(width2 - width1, var1)
            max_width = width2
        else:
            max_width = width1
        
        # Check for overflow using Z3's builtin overflow detection
        # For unsigned addition, overflow occurs when the sum wraps around
        # This is detected when: (a + b) < a  OR  (a + b) < b
        sum_val = var1 + var2
        overflow = z3.Or(z3.ULT(sum_val, var1), z3.ULT(sum_val, var2))
        self.solver.add_constraint(overflow)
        
        result = self.solver.check_sat()
        elapsed_ms = (time.time() - start_time) * 1000
        
        if result.result == SolverResult.SAT:
            model = self.solver.get_model()
            return VerificationResult(
                holds=False,
                counterexample=model,
                solver_time_ms=elapsed_ms,
                solver_name="z3",
                result=SolverResult.SAT
            )
        elif result.result == SolverResult.UNSAT:
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
    
    def check_non_overlapping(self,
                            src_base: str,
                            src_size: str,
                            dst_base: str,
                            dst_size: str,
                            struct_type: Any) -> VerificationResult:
        """Check if two memory regions don't overlap.
        
        Checks: src_end <= dst_start OR dst_end <= src_start
        
        Args:
            src_base: Name of source base field
            src_size: Name of source size field
            dst_base: Name of destination base field
            dst_size: Name of destination size field
            struct_type: DataTypeStruct containing the fields
            
        Returns:
            VerificationResult indicating if regions can overlap
        """
        start_time = time.time()
        
        # Reset solver for clean state
        self.solver.reset()
        
        # Translate struct to SMT problem
        problem = self.translator.translate_struct(struct_type)
        
        # Add all field constraints to solver
        for constraint in problem.constraints:
            self.solver.add_constraint(constraint)
        
        # Get variables
        src_base_var = problem.variables[src_base]
        src_size_var = problem.variables[src_size]
        dst_base_var = problem.variables[dst_base]
        dst_size_var = problem.variables[dst_size]
        
        # Ensure matching bit widths for arithmetic operations
        import z3
        
        # Extend src_size to match src_base width
        src_base_width = src_base_var.size()
        src_size_width = src_size_var.size()
        if src_base_width > src_size_width:
            src_size_var = z3.ZeroExt(src_base_width - src_size_width, src_size_var)
        elif src_size_width > src_base_width:
            src_base_var = z3.ZeroExt(src_size_width - src_base_width, src_base_var)
        
        # Extend dst_size to match dst_base width
        dst_base_width = dst_base_var.size()
        dst_size_width = dst_size_var.size()
        if dst_base_width > dst_size_width:
            dst_size_var = z3.ZeroExt(dst_base_width - dst_size_width, dst_size_var)
        elif dst_size_width > dst_base_width:
            dst_base_var = z3.ZeroExt(dst_size_width - dst_base_width, dst_base_var)
        
        # Calculate end addresses
        src_end = src_base_var + src_size_var
        dst_end = dst_base_var + dst_size_var
        
        # Overlap condition (negation of non-overlap)
        # Overlap: NOT (src_end <= dst_base OR dst_end <= src_base)
        # Which is: src_end > dst_base AND dst_end > src_base
        overlap = z3.And(
            z3.UGT(src_end, dst_base_var),
            z3.UGT(dst_end, src_base_var)
        )
        self.solver.add_constraint(overlap)
        
        result = self.solver.check_sat()
        elapsed_ms = (time.time() - start_time) * 1000
        
        if result.result == SolverResult.SAT:
            model = self.solver.get_model()
            return VerificationResult(
                holds=False,  # Overlap possible
                counterexample=model,
                solver_time_ms=elapsed_ms,
                solver_name="z3",
                result=SolverResult.SAT
            )
        elif result.result == SolverResult.UNSAT:
            return VerificationResult(
                holds=True,  # No overlap possible
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

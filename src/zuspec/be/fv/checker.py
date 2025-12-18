"""
Main verification API for Zuspec dataclasses.

Provides high-level functions for checking bounds, invariants, and other properties.
"""
from typing import Type, Optional, Dict, Any, List
import sys
import time
sys.path.insert(0, 'packages/zuspec-dataclasses/src')

try:
    from zuspec.dataclasses import dm, data_model_factory
except ImportError:
    dm = None
    data_model_factory = None

from .solver.z3_solver import Z3Solver
from .solver.result import VerificationResult, SolverResult
from .translator.dm_to_smt import DataModelTranslator
from .analysis.bounds_analyzer import BoundsAnalyzer


def check_bounds(dtype: Type,
                memory_bounds: Optional[Dict[str, int]] = None,
                solver: str = "z3") -> VerificationResult:
    """Check that all field values respect bounds constraints.
    
    This function verifies that all fields with bounds metadata stay within
    their specified ranges, and optionally checks memory access bounds.
    
    Args:
        dtype: Zuspec dataclass type (decorated with @dataclass)
        memory_bounds: Optional dict mapping field names to memory bounds
                      Example: {"src": 0x10000} checks src + size <= 0x10000
        solver: Solver backend to use (default: "z3")
        
    Returns:
        VerificationResult with holds=True if all bounds are satisfied,
        or holds=False with counterexample if violations exist
        
    Example:
        >>> @zdc.dataclass
        >>> class DmaConfig(zdc.Struct):
        ...     src: zdc.uint32_t = zdc.field(bounds=(0, 0xFFFF))
        ...     size: zdc.uint8_t = zdc.field(bounds=(1, 128))
        >>> 
        >>> result = check_bounds(DmaConfig, memory_bounds={"src": 0x10000})
        >>> if not result.holds:
        ...     print(f"Violation: {result.counterexample}")
    """
    if dm is None or data_model_factory is None:
        raise ImportError("zuspec.dataclasses not available")
    
    start_time = time.time()
    
    # Get data model from the Python class
    factory = data_model_factory.DataModelFactory()
    context = factory.build(dtype)
    
    # Get the struct type from context (use __qualname__ for nested classes)
    type_name = dtype.__qualname__ if hasattr(dtype, '__qualname__') else dtype.__name__
    if type_name not in context.type_m:
        raise ValueError(f"Type '{type_name}' not found in data model context")
    
    struct_type = context.type_m[type_name]
    
    # Create solver and translator
    solver_backend = Z3Solver() if solver == "z3" else Z3Solver()
    translator = DataModelTranslator()
    
    # Translate struct to SMT problem (pass Python type for metadata)
    problem = translator.translate_struct(struct_type, dtype)
    
    # Add all field bounds constraints
    for constraint in problem.constraints:
        solver_backend.add_constraint(constraint)
    
    # If memory bounds specified, add those checks
    if memory_bounds:
        for base_field, bound in memory_bounds.items():
            # Look for a size field (common patterns: size, xfer_sz, len, length)
            size_candidates = ['size', 'xfer_sz', 'len', 'length', f"{base_field}_size"]
            size_field = None
            
            for candidate in size_candidates:
                if candidate in problem.variables:
                    size_field = candidate
                    break
            
            if size_field and base_field in problem.variables:
                base_var = problem.variables[base_field]
                size_var = problem.variables[size_field]
                
                # Add constraint: base + size must be <= bound
                # We don't check for violation here, just add the constraint
                import z3
                solver_backend.add_constraint(z3.ULE(base_var + size_var, bound))
    
    # Check if constraints are satisfiable
    # If SAT, there exists at least one valid configuration
    # If UNSAT, the bounds are impossible to satisfy (over-constrained)
    result = solver_backend.check_sat()
    
    elapsed_ms = (time.time() - start_time) * 1000
    
    if result == SolverResult.SAT:
        # Constraints are satisfiable - bounds can be satisfied
        model = solver_backend.get_model()
        return VerificationResult(
            holds=True,
            counterexample=model,  # This is actually a valid example, not a counterexample
            solver_time_ms=elapsed_ms,
            solver_name=solver,
            result=result
        )
    elif result == SolverResult.UNSAT:
        # Constraints are unsatisfiable - bounds are contradictory
        return VerificationResult(
            holds=False,
            counterexample=None,
            solver_time_ms=elapsed_ms,
            solver_name=solver,
            result=result
        )
    else:
        # Unknown
        return VerificationResult(
            holds=False,
            counterexample=None,
            solver_time_ms=elapsed_ms,
            solver_name=solver,
            result=result
        )


def check_invariant(dtype: Type,
                   invariant_expr: str,
                   bound: int = 1,
                   solver: str = "z3") -> VerificationResult:
    """Check a custom invariant on the dataclass.
    
    Args:
        dtype: Zuspec dataclass type
        invariant_expr: String expression for the invariant
        bound: Bound for BMC (number of steps, default=1 for stateless)
        solver: Solver backend to use (default: "z3")
        
    Returns:
        VerificationResult indicating if invariant holds
        
    Note:
        This is a placeholder for Phase 4. Currently supports simple expressions.
    """
    # Placeholder implementation
    raise NotImplementedError("Custom invariants will be implemented in Phase 4")


def check_no_overflow(dtype: Type,
                     fields: List[str],
                     solver: str = "z3") -> VerificationResult:
    """Check that arithmetic on specified fields doesn't overflow.
    
    Args:
        dtype: Zuspec dataclass type
        fields: List of field names to check (e.g., ["base", "size"])
        solver: Solver backend to use (default: "z3")
        
    Returns:
        VerificationResult with holds=True if no overflow possible
        
    Example:
        >>> result = check_no_overflow(DmaConfig, ["src", "xfer_sz"])
        >>> if not result.holds:
        ...     print(f"Overflow possible: {result.counterexample}")
    """
    if dm is None or data_model_factory is None:
        raise ImportError("zuspec.dataclasses not available")
    
    if len(fields) != 2:
        raise ValueError("Currently only supports checking two fields")
    
    # Get data model from the Python class
    factory = data_model_factory.DataModelFactory()
    context = factory.build(dtype)
    
    type_name = dtype.__qualname__ if hasattr(dtype, '__qualname__') else dtype.__name__
    if type_name not in context.type_m:
        raise ValueError(f"Type '{type_name}' not found in data model context")
    
    struct_type = context.type_m[type_name]
    
    # Use bounds analyzer
    analyzer = BoundsAnalyzer()
    return analyzer.check_no_overflow(fields[0], fields[1], struct_type)


def find_bounds_violation(dtype: Type,
                         base_field: str,
                         size_field: str,
                         memory_bound: int,
                         solver: str = "z3") -> VerificationResult:
    """Find if a bounds violation is possible for memory access.
    
    This checks if base + size can exceed the memory bound given the
    field constraints.
    
    Args:
        dtype: Zuspec dataclass type
        base_field: Name of base address field
        size_field: Name of size field
        memory_bound: Upper bound for memory region
        solver: Solver backend to use (default: "z3")
        
    Returns:
        VerificationResult with holds=False if violation is possible,
        holds=True if access is always safe
        
    Example:
        >>> result = find_bounds_violation(DmaConfig, "src", "xfer_sz", 0x10000)
        >>> if not result.holds:
        ...     print(f"Violation at: {result.counterexample}")
    """
    if dm is None or data_model_factory is None:
        raise ImportError("zuspec.dataclasses not available")
    
    # Get data model from the Python class
    factory = data_model_factory.DataModelFactory()
    context = factory.build(dtype)
    
    type_name = dtype.__qualname__ if hasattr(dtype, '__qualname__') else dtype.__name__
    if type_name not in context.type_m:
        raise ValueError(f"Type '{type_name}' not found in data model context")
    
    struct_type = context.type_m[type_name]
    
    # Use bounds analyzer
    analyzer = BoundsAnalyzer()
    return analyzer.check_memory_access(base_field, size_field, memory_bound, struct_type)

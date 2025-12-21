"""
Translation Context for RTL to SMT2 translation.

Provides context for expression and statement translation including:
- Type inference
- Variable mapping (fields, locals, parameters)
- Bit width resolution
"""

from dataclasses import dataclass, field as dc_field
from typing import Dict, Optional, Any, List
import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')

try:
    from zuspec.dataclasses import dm
except ImportError:
    dm = None

from .smt2_module import SMT2Module


@dataclass
class TranslationContext:
    """Context for expression and statement translation.
    
    Attributes:
        component: Component being translated
        module: Target SMT2 module
        field_map: Mapping from field index to SMT signal name
        local_vars: Local variable values/names
        param_map: Parameter name to value/name mapping
        type_cache: Cache for inferred types
        state_var: Name of state variable in SMT2
        next_state_var: Name of next state variable (for transitions)
    """
    
    component: Any  # dm.DataTypeComponent
    module: SMT2Module
    field_map: Dict[int, str] = dc_field(default_factory=dict)
    local_vars: Dict[str, str] = dc_field(default_factory=dict)
    param_map: Dict[str, str] = dc_field(default_factory=dict)
    type_cache: Dict[Any, Any] = dc_field(default_factory=dict)
    state_var: str = "state"
    next_state_var: str = "next_state"
    
    def get_field_smt_name(self, field_index: int) -> str:
        """Get SMT name for field by index.
        
        Args:
            field_index: Index into component.fields list
            
        Returns:
            SMT signal name
            
        Raises:
            ValueError: If field index not found
        """
        if field_index not in self.field_map:
            raise ValueError(f"Unknown field index: {field_index}")
        return self.field_map[field_index]
    
    def get_field_by_index(self, field_index: int) -> Any:
        """Get field object by index.
        
        Args:
            field_index: Index into component.fields list
            
        Returns:
            Field object
            
        Raises:
            IndexError: If index out of bounds
        """
        if field_index < 0 or field_index >= len(self.component.fields):
            raise IndexError(f"Field index out of bounds: {field_index}")
        return self.component.fields[field_index]
    
    def infer_type(self, expr: Any) -> Any:
        """Infer type of expression.
        
        Args:
            expr: Expression to infer type for
            
        Returns:
            DataType object
        """
        # Check cache first using id() since dataclasses aren't hashable
        expr_id = id(expr)
        if expr_id in self.type_cache:
            return self.type_cache[expr_id]
        
        if dm is None:
            raise ImportError("zuspec.dataclasses not available")
        
        # Infer based on expression type
        inferred_type = self._infer_type_impl(expr)
        
        # Cache result
        self.type_cache[expr_id] = inferred_type
        
        return inferred_type
    
    def _infer_type_impl(self, expr: Any) -> Any:
        """Implementation of type inference."""
        
        if isinstance(expr, dm.ExprConstant):
            # Infer from constant value
            value = expr.value
            if isinstance(value, bool):
                return dm.DataTypeInt(bits=1, signed=False)
            elif isinstance(value, int):
                # Minimum width to represent value
                if value == 0:
                    return dm.DataTypeInt(bits=1, signed=False)
                elif value > 0:
                    width = value.bit_length()
                    return dm.DataTypeInt(bits=width, signed=False)
                else:
                    # Negative - needs sign bit
                    width = (abs(value) - 1).bit_length() + 1
                    return dm.DataTypeInt(bits=width, signed=True)
            else:
                # Default for unknown types
                return dm.DataTypeInt(bits=32, signed=False)
        
        elif isinstance(expr, dm.ExprRefField):
            # Get type from field definition
            field = self.get_field_by_index(expr.index)
            return field.datatype
        
        elif isinstance(expr, dm.ExprRefLocal):
            # Would need to track local variable types
            # For now, return default
            return dm.DataTypeInt(bits=32, signed=False)
        
        elif isinstance(expr, dm.ExprRefParam):
            # Would need parameter type info
            return dm.DataTypeInt(bits=32, signed=False)
        
        elif isinstance(expr, dm.ExprBin):
            # Infer from operands
            lhs_type = self.infer_type(expr.lhs)
            rhs_type = self.infer_type(expr.rhs)
            
            # For arithmetic, take wider type
            if isinstance(lhs_type, dm.DataTypeInt) and isinstance(rhs_type, dm.DataTypeInt):
                lhs_width = lhs_type.bits if lhs_type.bits > 0 else 32
                rhs_width = rhs_type.bits if rhs_type.bits > 0 else 32
                max_width = max(lhs_width, rhs_width)
                
                # Result is signed if either operand is signed
                is_signed = lhs_type.signed or rhs_type.signed
                
                # For comparisons, result is boolean
                if expr.op in [dm.BinOp.Eq, dm.BinOp.NotEq, dm.BinOp.Lt, 
                              dm.BinOp.LtE, dm.BinOp.Gt, dm.BinOp.GtE]:
                    return dm.DataTypeInt(bits=1, signed=False)
                
                return dm.DataTypeInt(bits=max_width, signed=is_signed)
            else:
                # Default
                return dm.DataTypeInt(bits=32, signed=False)
        
        elif isinstance(expr, dm.ExprUnary):
            # Same type as operand
            return self.infer_type(expr.operand)
        
        elif isinstance(expr, dm.ExprCompare):
            # Comparison result is boolean
            return dm.DataTypeInt(bits=1, signed=False)
        
        elif isinstance(expr, dm.ExprBool):
            # Boolean operations return boolean
            return dm.DataTypeInt(bits=1, signed=False)
        
        else:
            # Unknown - default
            return dm.DataTypeInt(bits=32, signed=False)
    
    def get_bit_width(self, expr: Any) -> int:
        """Get bit width of expression.
        
        Args:
            expr: Expression to get width for
            
        Returns:
            Bit width as integer
        """
        dtype = self.infer_type(expr)
        if isinstance(dtype, dm.DataTypeInt):
            return dtype.bits if dtype.bits > 0 else 32
        return 1  # Boolean default
    
    def is_signed_type(self, expr: Any) -> bool:
        """Check if expression has signed type.
        
        Args:
            expr: Expression to check
            
        Returns:
            True if signed, False otherwise
        """
        dtype = self.infer_type(expr)
        if isinstance(dtype, dm.DataTypeInt):
            return dtype.signed
        return False
    
    def add_local_var(self, name: str, smt_expr: str):
        """Add local variable mapping.
        
        Args:
            name: Variable name
            smt_expr: SMT2 expression for variable
        """
        self.local_vars[name] = smt_expr
    
    def get_local_var(self, name: str) -> Optional[str]:
        """Get local variable SMT expression.
        
        Args:
            name: Variable name
            
        Returns:
            SMT expression or None if not found
        """
        return self.local_vars.get(name)
    
    def clone_for_next_state(self) -> 'TranslationContext':
        """Create a clone of context for next state references.
        
        Returns:
            New context with next_state as state_var
        """
        new_ctx = TranslationContext(
            component=self.component,
            module=self.module,
            field_map=self.field_map.copy(),
            local_vars=self.local_vars.copy(),
            param_map=self.param_map.copy(),
            type_cache=self.type_cache,
            state_var=self.next_state_var,
            next_state_var=self.next_state_var
        )
        return new_ctx

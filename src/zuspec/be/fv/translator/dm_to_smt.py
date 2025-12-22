"""
Data Model to SMT translation.

Converts Zuspec dataclass structures (via data model) into SMT constraints.
"""
from typing import Dict, Any, List, Optional, Tuple, Type
import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')

try:
    from zuspec.dataclasses import ir
except ImportError:
    ir = None

from .type_translator import TypeTranslator


class SMTProblem:
    """Represents an SMT problem with variables and constraints.
    
    Attributes:
        variables: Dictionary mapping field names to Z3 variables
        constraints: List of Z3 constraint expressions
        field_info: Metadata about each field (type, bounds, etc.)
    """
    
    def __init__(self):
        self.variables: Dict[str, Any] = {}
        self.constraints: List[Any] = []
        self.field_info: Dict[str, Dict[str, Any]] = {}
    
    def add_variable(self, name: str, var: Any, info: Optional[Dict[str, Any]] = None):
        """Add a variable to the problem."""
        self.variables[name] = var
        if info:
            self.field_info[name] = info
    
    def add_constraint(self, constraint: Any):
        """Add a constraint to the problem."""
        self.constraints.append(constraint)
    
    def get_all_constraints(self) -> List[Any]:
        """Get all constraints as a list."""
        return self.constraints


class DataModelTranslator:
    """Translates Zuspec data model structures to SMT problems."""
    
    def __init__(self):
        self.type_translator = TypeTranslator()
    
    def translate_struct(self, struct_type: Any, py_type: Optional[Any] = None) -> SMTProblem:
        """Translate a Zuspec struct to an SMT problem.
        
        Args:
            struct_type: DataTypeStruct from data model
            py_type: Optional Python class for metadata extraction (if None, uses struct_type.py_type)
            
        Returns:
            SMTProblem with variables and constraints
        """
        problem = SMTProblem()
        
        if ir is None:
            raise ImportError("zuspec.dataclasses not available")
        
        if not isinstance(struct_type, ir.DataTypeStruct):
            raise TypeError(f"Expected DataTypeStruct, got {type(struct_type)}")
        
        # Get Python type - use provided or extract from struct_type
        if py_type is None and hasattr(struct_type, 'py_type'):
            py_type = struct_type.py_type
        
        # Get Python dataclass fields metadata if available
        metadata_map = {}
        if py_type is not None:
            import dataclasses
            try:
                for py_field in dataclasses.fields(py_type):
                    metadata_map[py_field.name] = py_field.metadata or {}
            except:
                pass
        
        # Process each field in the struct
        for field in struct_type.fields:
            self._translate_field(field, problem, metadata_map.get(field.name, {}))
        
        return problem
    
    def _translate_field(self, field: Any, problem: SMTProblem, metadata: Optional[Dict] = None):
        """Translate a single field to SMT variable and constraints.
        
        Args:
            field: Field from data model
            problem: SMTProblem to add to
            metadata: Metadata from Python dataclass field
        """
        field_name = field.name
        field_type = field.datatype
        
        # Use provided metadata
        if metadata is None:
            metadata = {}
        
        # Determine bit width and signedness
        if isinstance(field_type, ir.DataTypeInt):
            width = abs(field_type.bits) if field_type.bits != -1 else 32
            is_signed = field_type.signed
            
            # Create Z3 variable
            var = self.type_translator.translate_int_type(field_name, width, is_signed)
            
            # Store field info
            info = {
                'type': 'int',
                'width': width,
                'signed': is_signed,
                'metadata': metadata
            }
            problem.add_variable(field_name, var, info)
            
            # Add bounds constraints if specified
            if 'bounds' in metadata:
                bounds = metadata['bounds']
                if isinstance(bounds, (tuple, list)) and len(bounds) == 2:
                    min_val, max_val = bounds
                    constraint = self.type_translator.create_bounds_constraint(
                        var, min_val, max_val, is_signed
                    )
                    problem.add_constraint(constraint)
        
        elif hasattr(ir, 'DataTypeStruct') and isinstance(field_type, ir.DataTypeStruct):
            # Handle nested structures
            nested_problem = self.translate_struct(field_type)
            
            # Add nested variables with prefixed names
            for nested_name, nested_var in nested_problem.variables.items():
                prefixed_name = f"{field_name}.{nested_name}"
                problem.add_variable(prefixed_name, nested_var, 
                                    nested_problem.field_info.get(nested_name))
            
            # Add nested constraints
            for constraint in nested_problem.constraints:
                problem.add_constraint(constraint)
    
    def extract_field_bounds(self, struct_type: Any, py_type: Optional[Type] = None) -> Dict[str, Tuple[int, int]]:
        """Extract bounds metadata from all fields.
        
        Args:
            struct_type: DataTypeStruct from data model
            py_type: Optional Python class for metadata extraction
            
        Returns:
            Dictionary mapping field names to (min, max) bounds
        """
        bounds_map = {}
        
        if ir is None or not isinstance(struct_type, ir.DataTypeStruct):
            return bounds_map
        
        # Get Python type if not provided
        if py_type is None and hasattr(struct_type, 'py_type'):
            py_type = struct_type.py_type
        
        # Get Python dataclass fields metadata if available
        metadata_map = {}
        if py_type is not None:
            import dataclasses
            try:
                for py_field in dataclasses.fields(py_type):
                    metadata_map[py_field.name] = py_field.metadata or {}
            except:
                pass
        
        for field in struct_type.fields:
            metadata = metadata_map.get(field.name, {})
            if 'bounds' in metadata:
                bounds = metadata['bounds']
                if isinstance(bounds, (tuple, list)) and len(bounds) == 2:
                    bounds_map[field.name] = tuple(bounds)
        
        return bounds_map
    
    def create_arithmetic_constraint(self, expr_str: str, problem: SMTProblem) -> Any:
        """Create an arithmetic constraint from a string expression.
        
        Args:
            expr_str: Expression like "base + size <= bound"
            problem: SMTProblem with variables
            
        Returns:
            Z3 constraint expression
        """
        # This is a simplified version - in production would use proper parsing
        # For now, support basic patterns
        import re
        
        # Pattern: var1 + var2 <= value
        match = re.match(r'(\w+)\s*\+\s*(\w+)\s*<=\s*(\d+)', expr_str)
        if match:
            var1_name, var2_name, bound_val = match.groups()
            if var1_name in problem.variables and var2_name in problem.variables:
                var1 = problem.variables[var1_name]
                var2 = problem.variables[var2_name]
                return var1 + var2 <= int(bound_val)
        
        raise ValueError(f"Cannot parse expression: {expr_str}")

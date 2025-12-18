"""
Type translator from Zuspec data model types to SMT types.
"""
from typing import Any, Optional
import z3


class TypeTranslator:
    """Translates Zuspec data model types to Z3 SMT types.
    
    Mapping:
        uint<N>_t / int<N>_t -> BitVec(N)
        bool -> Bool
        PackedStruct -> Multiple BitVec fields
        Memory -> Array(BitVec(addr_width), BitVec(data_width))
    """
    
    def __init__(self):
        """Initialize type translator."""
        self._type_cache = {}
    
    def translate_int_type(self, name: str, width: int, signed: bool = False) -> Any:
        """Translate integer type to Z3 BitVec.
        
        Args:
            name: Variable name
            width: Bit width
            signed: Whether the integer is signed (currently both map to BitVec)
            
        Returns:
            Z3 BitVec variable
        """
        return z3.BitVec(name, width)
    
    def translate_bool_type(self, name: str) -> Any:
        """Translate boolean type to Z3 Bool.
        
        Args:
            name: Variable name
            
        Returns:
            Z3 Bool variable
        """
        return z3.Bool(name)
    
    def translate_array_type(self, name: str, addr_width: int, data_width: int) -> Any:
        """Translate memory/array type to Z3 Array.
        
        Args:
            name: Array name
            addr_width: Address bit width
            data_width: Data element bit width
            
        Returns:
            Z3 Array variable
        """
        return z3.Array(name, z3.BitVecSort(addr_width), z3.BitVecSort(data_width))
    
    def create_bounds_constraint(self, var: Any, min_val: int, max_val: int, 
                                 is_signed: bool = False) -> Any:
        """Create bounds constraint for a variable.
        
        Args:
            var: Z3 variable
            min_val: Minimum value (inclusive)
            max_val: Maximum value (inclusive)
            is_signed: Whether to use signed comparison
            
        Returns:
            Z3 constraint expression
        """
        if is_signed:
            return z3.And(var >= min_val, var <= max_val)
        else:
            # For BitVec, use unsigned comparison
            if isinstance(var, z3.BitVecRef):
                return z3.And(z3.UGE(var, min_val), z3.ULE(var, max_val))
            else:
                return z3.And(var >= min_val, var <= max_val)
    
    def get_bit_width_for_type(self, type_name: str) -> Optional[int]:
        """Get bit width for standard Zuspec types.
        
        Args:
            type_name: Type name (e.g., 'uint32_t', 'int8_t')
            
        Returns:
            Bit width or None if not a standard type
        """
        # Extract width from type names like uint32_t, int8_t, etc.
        import re
        match = re.match(r'u?int(\d+)_t', type_name)
        if match:
            return int(match.group(1))
        
        # Standard types
        type_widths = {
            'uint8_t': 8,
            'uint16_t': 16,
            'uint32_t': 32,
            'uint64_t': 64,
            'int8_t': 8,
            'int16_t': 16,
            'int32_t': 32,
            'int64_t': 64,
            'bool': 1,
        }
        
        return type_widths.get(type_name)
    
    def is_signed_type(self, type_name: str) -> bool:
        """Check if a type is signed.
        
        Args:
            type_name: Type name
            
        Returns:
            True if signed, False otherwise
        """
        return type_name.startswith('int') and not type_name.startswith('uint')

"""
Pytest configuration and fixtures for zuspec-be-fv tests.
"""
import sys
from pathlib import Path

# Add src to path for imports
src_path = Path(__file__).parent.parent.parent / "src"
if str(src_path) not in sys.path:
    sys.path.insert(0, str(src_path))


def get_struct_type(context, py_class):
    """Helper to get struct type from context using Python class.
    
    Handles the fact that classes defined in test functions have 
    qualified names like 'test_func.<locals>.ClassName'.
    """
    qualname = py_class.__qualname__
    return context.type_m[qualname]

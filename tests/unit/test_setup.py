"""
Basic test to verify package setup is correct.
"""

def test_package_imports():
    """Test that the package can be imported."""
    import zuspec.be.fv
    assert zuspec.be.fv.__version__ == "0.1.0"
    assert hasattr(zuspec.be.fv, '__version__')


def test_package_structure():
    """Test that package structure is accessible."""
    from zuspec.be import fv
    assert fv.__version__ == "0.1.0"

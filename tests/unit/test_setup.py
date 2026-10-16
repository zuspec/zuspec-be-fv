"""
Basic test to verify package setup is correct.
"""
import importlib.util
import pathlib


def _version_file_version(pkg):
    """VERSION as __version__.py writes it (CI stamps a dev SUFFIX there)."""
    path = pathlib.Path(pkg.__file__).with_name("__version__.py")
    spec = importlib.util.spec_from_file_location("_fv_version", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.VERSION


def test_package_imports():
    """Test that the package can be imported."""
    import zuspec.be.fv
    assert hasattr(zuspec.be.fv, '__version__')
    assert zuspec.be.fv.__version__ == _version_file_version(zuspec.be.fv)


def test_package_structure():
    """Test that package structure is accessible."""
    from zuspec.be import fv
    assert fv.__version__ == _version_file_version(fv)

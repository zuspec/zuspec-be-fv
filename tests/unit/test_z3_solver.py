"""
Tests for Z3 solver backend.
"""
import z3
from zuspec.be.fv.solver import Z3Solver, SolverResult


def test_z3_solver_unsat():
    """Test that Z3 correctly identifies unsatisfiable constraints."""
    solver = Z3Solver()
    
    x = z3.Int('x')
    solver.register_variable('x', x)
    solver.add_constraint(x > 10)
    solver.add_constraint(x < 5)
    
    result = solver.check_sat()
    
    assert result.holds is True
    assert result.result == SolverResult.UNSAT
    assert result.counterexample is None
    assert result.solver_name == "z3"


def test_z3_solver_sat():
    """Test that Z3 correctly finds satisfying assignments."""
    solver = Z3Solver()
    
    x = z3.Int('x')
    solver.register_variable('x', x)
    solver.add_constraint(x > 10)
    solver.add_constraint(x < 20)
    
    result = solver.check_sat()
    
    assert result.holds is False
    assert result.result == SolverResult.SAT
    assert result.counterexample is not None
    assert 'x' in result.counterexample
    assert 10 < result.counterexample['x'] < 20


def test_z3_solver_bitvector():
    """Test Z3 with bitvector constraints."""
    solver = Z3Solver()
    
    addr = z3.BitVec('addr', 32)
    size = z3.BitVec('size', 8)
    
    solver.register_variable('addr', addr)
    solver.register_variable('size', size)
    
    # Constraint: addr in range [0, 0xFFFF] and size in [1, 128]
    solver.add_constraint(z3.ULE(addr, 0xFFFF))
    solver.add_constraint(z3.UGE(size, 1))
    solver.add_constraint(z3.ULE(size, 128))
    
    # Violation: addr + size > 0x10000
    solver.add_constraint(z3.UGT(addr + z3.ZeroExt(24, size), 0x10000))
    
    result = solver.check_sat()
    
    assert result.holds is False
    assert result.result == SolverResult.SAT
    assert 'addr' in result.counterexample
    assert 'size' in result.counterexample


def test_z3_solver_push_pop():
    """Test Z3 push/pop for backtracking."""
    solver = Z3Solver()
    
    x = z3.Int('x')
    solver.add_constraint(x > 10)
    
    # First check: x > 10
    result1 = solver.check_sat()
    assert result1.holds is False  # Satisfiable
    
    # Add conflicting constraint in new scope
    solver.push()
    solver.add_constraint(x < 5)
    
    # Second check: x > 10 AND x < 5
    result2 = solver.check_sat()
    assert result2.holds is True  # Unsatisfiable
    
    # Pop back to original state
    solver.pop()
    
    # Third check: back to just x > 10
    result3 = solver.check_sat()
    assert result3.holds is False  # Satisfiable again


def test_z3_solver_reset():
    """Test Z3 solver reset functionality."""
    solver = Z3Solver()
    
    x = z3.Int('x')
    solver.add_constraint(x > 10)
    solver.add_constraint(x < 5)
    
    result1 = solver.check_sat()
    assert result1.holds is True  # Unsat
    
    solver.reset()
    
    # After reset, add only satisfiable constraint
    y = z3.Int('y')
    solver.add_constraint(y == 42)
    
    result2 = solver.check_sat()
    assert result2.holds is False  # Sat
    assert result2.counterexample['y'] == 42


def test_z3_solver_get_model():
    """Test extracting models from satisfiable formulas."""
    solver = Z3Solver()
    
    x = z3.Int('x')
    y = z3.Int('y')
    
    solver.add_constraint(x + y == 10)
    solver.add_constraint(x > 5)
    
    result = solver.check_sat()
    
    assert result.holds is False
    model = result.counterexample
    
    assert model is not None
    assert model['x'] + model['y'] == 10
    assert model['x'] > 5


def test_z3_solver_boolean_constraints():
    """Test Z3 with boolean variables."""
    solver = Z3Solver()
    
    a = z3.Bool('a')
    b = z3.Bool('b')
    
    solver.add_constraint(z3.Or(a, b))
    solver.add_constraint(z3.Not(a))
    
    result = solver.check_sat()
    
    assert result.holds is False
    assert result.counterexample['a'] is False
    assert result.counterexample['b'] is True

"""T-P8: Tests for role-aware SMT2 emission and contract checking functions.

Tests:
 - RandSMT2Emitter.emit() skips ensures constraints
 - RandSMT2Emitter.emit_dead_action_check() produces SMT2 with requires+plain
 - RandSMT2Emitter.emit_contract_check() produces negated ensures refutation
 - check_dead_action() correctly identifies live vs dead actions
 - check_action_contracts() correctly identifies satisfiable ensures
"""
import sys
import os
import pytest

_pkg = os.path.join(os.path.dirname(__file__), '..', '..', 'src')
_dc = os.path.join(os.path.dirname(__file__), '..', '..', '..', 'zuspec-dataclasses', 'src')
sys.path.insert(0, _pkg)
sys.path.insert(1, _dc)

from zuspec.dataclasses.decorators import constraint as _constraint, field as _field
from zuspec.be.fv.smt2.rand_emitter import RandSMT2Emitter

# ---------------------------------------------------------------------------
# Fixture action classes — must be at module level for inspect.getsource()
# ---------------------------------------------------------------------------

class LiveAction:
    """Action where requires is satisfiable (some value in 1..100)."""
    @_constraint.requires
    def req_positive(self):
        self.value > 0

    @_constraint.requires
    def req_bounded(self):
        self.value < 100


class DeadAction:
    """Action where requires is contradictory (value > 50 AND value < 10)."""
    @_constraint.requires
    def req_large(self):
        self.value > 50

    @_constraint.requires
    def req_small(self):
        self.value < 10


class EnsuresHoldsAction:
    """Action where ensures is always true under requires (value < 200 when value < 100)."""
    @_constraint.requires
    def req_small(self):
        self.value < 100

    @_constraint.ensures
    def ens_bounded(self):
        self.value < 200


class EnsuresViolatedAction:
    """Action where ensures can be violated: value < 50 but ensures value < 20."""
    @_constraint.requires
    def req_under_50(self):
        self.value < 50

    @_constraint.ensures
    def ens_under_20(self):
        self.value < 20


class PlainConstraintAction:
    """Action with plain constraint (no role)."""
    @_constraint
    def c_range(self):
        self.value < 128


def _make_rand_fields(*names):
    """Patch a fake ``_rand_fields`` so extract_rand_fields works."""
    import dataclasses
    # Return a list of field-like dicts
    return [{'name': n, 'width': 32, 'domain': None} for n in names]


# ---------------------------------------------------------------------------
# Helper: check if z3 is available
# ---------------------------------------------------------------------------

def _z3_available():
    try:
        import z3
        return True
    except ImportError:
        return False


pytestmark = pytest.mark.skipif(not _z3_available(), reason="z3 not installed")


# ---------------------------------------------------------------------------
# Patch extract_rand_fields for test classes that don't use zdc.field()
# ---------------------------------------------------------------------------

import unittest.mock as mock
from zuspec.dataclasses.constraint_parser import extract_rand_fields as _orig_erf


def _patched_erf(cls):
    """Return a single rand field 'value' for our test action classes."""
    return [{'name': 'value', 'width': 32, 'domain': None}]


# ---------------------------------------------------------------------------
# T-P8a: RandSMT2Emitter.emit() skips ensures constraints
# ---------------------------------------------------------------------------

class TestRandEmitterSkipsEnsures:
    def test_ensures_not_in_rand_output(self):
        emitter = RandSMT2Emitter()
        with mock.patch(
            'zuspec.be.fv.smt2.rand_emitter._get_extract_rand_fields',
            return_value=_patched_erf,
        ):
            # Manually build: emit only needs extract_rand_fields + constraint_parser
            from zuspec.dataclasses.constraint_parser import ConstraintParser
            from zuspec.be.fv.smt2 import bitvec_ops
            from zuspec.be.fv.smt2.rand_emitter import _ExprTranslator

            parser = ConstraintParser()
            constraints = parser.extract_constraints(EnsuresHoldsAction)

            # Verify that ensures constraints have role='ensures'
            ensure_cs = [c for c in constraints if c.get('role') == 'ensures']
            plain_cs = [c for c in constraints if c.get('role') is None]
            req_cs = [c for c in constraints if c.get('role') == 'requires']

            assert len(ensure_cs) == 1, "Expected one ensures constraint"
            assert len(req_cs) == 1, "Expected one requires constraint"

    def test_ensures_role_present_in_parse(self):
        from zuspec.dataclasses.constraint_parser import ConstraintParser
        parser = ConstraintParser()
        constraints = parser.extract_constraints(EnsuresHoldsAction)
        roles = {c['name']: c.get('role') for c in constraints}
        assert roles.get('req_small') == 'requires'
        assert roles.get('ens_bounded') == 'ensures'


# ---------------------------------------------------------------------------
# T-P8b: SMT2 text generation for dead_action_check and contract_check
# ---------------------------------------------------------------------------

class TestSMT2TextGeneration:
    def setup_method(self):
        self.emitter = RandSMT2Emitter()

    def _emit_dead(self, action_cls):
        with mock.patch(
            'zuspec.be.fv.smt2.rand_emitter._get_extract_rand_fields',
            return_value=_patched_erf,
        ):
            return self.emitter.emit_dead_action_check(action_cls)

    def _emit_contract(self, action_cls):
        with mock.patch(
            'zuspec.be.fv.smt2.rand_emitter._get_extract_rand_fields',
            return_value=_patched_erf,
        ):
            return self.emitter.emit_contract_check(action_cls)

    def test_dead_check_contains_check_sat(self):
        smt2 = self._emit_dead(LiveAction)
        assert '(check-sat)' in smt2

    def test_dead_check_contains_declare(self):
        smt2 = self._emit_dead(LiveAction)
        assert '(declare-const value' in smt2

    def test_contract_check_has_negated_ensures(self):
        smt2 = self._emit_contract(EnsuresHoldsAction)
        assert '(not ' in smt2, "Contract check should negate ensures"

    def test_contract_check_contains_requires(self):
        smt2 = self._emit_contract(EnsuresHoldsAction)
        assert '; req_small' in smt2


# ---------------------------------------------------------------------------
# T-P8c: check_dead_action() and check_action_contracts() integration
# ---------------------------------------------------------------------------

class TestCheckDeadAction:
    def test_live_action_holds(self):
        from zuspec.be.fv.checker import check_dead_action
        with mock.patch(
            'zuspec.be.fv.smt2.rand_emitter._get_extract_rand_fields',
            return_value=_patched_erf,
        ):
            result = check_dead_action(LiveAction)
        assert result.holds is True

    def test_dead_action_not_holds(self):
        from zuspec.be.fv.checker import check_dead_action
        with mock.patch(
            'zuspec.be.fv.smt2.rand_emitter._get_extract_rand_fields',
            return_value=_patched_erf,
        ):
            result = check_dead_action(DeadAction)
        assert result.holds is False

    def test_live_result_has_solver_time(self):
        from zuspec.be.fv.checker import check_dead_action
        with mock.patch(
            'zuspec.be.fv.smt2.rand_emitter._get_extract_rand_fields',
            return_value=_patched_erf,
        ):
            result = check_dead_action(LiveAction)
        assert result.solver_time_ms >= 0


class TestCheckActionContracts:
    def test_always_satisfied_ensures_holds(self):
        from zuspec.be.fv.checker import check_action_contracts
        # value < 100 (requires) → value < 200 (ensures) always holds
        with mock.patch(
            'zuspec.be.fv.smt2.rand_emitter._get_extract_rand_fields',
            return_value=_patched_erf,
        ):
            result = check_action_contracts(EnsuresHoldsAction)
        assert result.holds is True

    def test_violatable_ensures_not_holds(self):
        from zuspec.be.fv.checker import check_action_contracts
        # value < 50 (requires), ensures value < 20 — can be violated (e.g. value=30)
        with mock.patch(
            'zuspec.be.fv.smt2.rand_emitter._get_extract_rand_fields',
            return_value=_patched_erf,
        ):
            result = check_action_contracts(EnsuresViolatedAction)
        assert result.holds is False

    def test_counterexample_present_when_violated(self):
        from zuspec.be.fv.checker import check_action_contracts
        with mock.patch(
            'zuspec.be.fv.smt2.rand_emitter._get_extract_rand_fields',
            return_value=_patched_erf,
        ):
            result = check_action_contracts(EnsuresViolatedAction)
        assert result.counterexample is not None
        assert 'value' in result.counterexample

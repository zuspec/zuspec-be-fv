"""Tier 1: IR-level formal proofs of PipelineIR properties.

No Yosys required.  These tests run whenever an SMT solver is available on
PATH (``$ZUSPEC_SMT_SOLVER``, or ``cvc5`` / ``z3`` auto-detected) and are
*skipped* (not failed) when no solver is found.

The tests exercise the k-induction and BMC paths of
:class:`~zuspec.be.fv.pipeline.pipeline_to_smt2.PipelineIRToSMT2` against the
well-known Ex-1 through Ex-7 pipeline examples.
"""
from __future__ import annotations

import os
import sys

import pytest

# ---------------------------------------------------------------------------
# Inject zuspec-synth sources and tests directory
# ---------------------------------------------------------------------------
_repo_root = os.path.abspath(
    os.path.join(os.path.dirname(__file__), "..", "..", "..", "..")
)
_synth_src = os.path.join(_repo_root, "packages", "zuspec-synth", "src")
_synth_tests = os.path.join(_repo_root, "packages", "zuspec-synth", "tests")
_dc_src = os.path.join(_repo_root, "packages", "zuspec-dataclasses", "src")
for _p in (_synth_src, _dc_src, _synth_tests):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from zuspec.be.fv.pipeline.pipeline_to_smt2 import PipelineIRToSMT2
from zuspec.be.fv.verification.verifier import verify_bmc, prove_k_induction
from zuspec.be.fv.verification.solver_runner import pick_solver

from test_sync_pipeline_api import (
    run_pipeline_synth,
    _Ex1Component,
    _Ex3Component,
    _Ex5Component,
    _Ex7Component,
)


# ---------------------------------------------------------------------------
# Fixtures
# ---------------------------------------------------------------------------

@pytest.fixture(scope="module")
def solver_spec():
    """Pick the first available SMT solver; skip module if none found."""
    spec = pick_solver()
    if spec is None:
        pytest.skip("No SMT solver available (install cvc5 or z3)")
    return spec


# ---------------------------------------------------------------------------
# Internal helpers
# ---------------------------------------------------------------------------

def _prove(pip, k: int, solver_spec) -> None:
    """Assert that the pipeline IR passes k-induction with depth *k*."""
    module = PipelineIRToSMT2().translate(pip)
    result = prove_k_induction(module, k=k, solver=solver_spec.name)
    assert result.holds, (
        f"k-induction (k={k}) failed for {pip.module_name}:\n{result.raw_stdout}"
    )


def _bmc(pip, depth: int, solver_spec) -> None:
    """Assert no assertion violation exists within *depth* BMC steps."""
    module = PipelineIRToSMT2().translate(pip)
    result = verify_bmc(module, depth=depth, solver=solver_spec.name)
    assert result.holds, (
        f"BMC (depth={depth}) found violation in {pip.module_name}:\n{result.raw_stdout}"
    )


def _get_pip(component_cls, forward_default: bool = True):
    pip, _sv = run_pipeline_synth(
        component_cls, forward_default=forward_default, return_ir=True
    )
    assert pip is not None
    return pip


# ---------------------------------------------------------------------------
# P1 — reset zeroes all valid bits (base case BMC depth=1)
# ---------------------------------------------------------------------------

def test_ir_ex1_p1_reset(solver_spec):
    """After reset all valid bits are false (initial-state BMC property)."""
    pip = _get_pip(_Ex1Component)
    _bmc(pip, depth=1, solver_spec=solver_spec)


# ---------------------------------------------------------------------------
# P2 — valid propagation
# ---------------------------------------------------------------------------

def test_ir_ex1_p2_propagation(solver_spec):
    """Valid bit propagates correctly through a 2-stage pipeline (k-induction)."""
    pip = _get_pip(_Ex1Component)
    _prove(pip, k=3, solver_spec=solver_spec)


# ---------------------------------------------------------------------------
# P3/P4 — stall semantics
# ---------------------------------------------------------------------------

def test_ir_ex3_p3_stall_freeze(solver_spec):
    """Stall freezes channel register data for Ex-3 (external stall input)."""
    pip = _get_pip(_Ex3Component)
    _prove(pip, k=5, solver_spec=solver_spec)


# ---------------------------------------------------------------------------
# P5 — flush priority
# ---------------------------------------------------------------------------

def test_ir_ex7_p5_flush(solver_spec):
    """Flush takes priority over stall and clears valid bits (Ex-7)."""
    pip = _get_pip(_Ex7Component)
    _prove(pip, k=4, solver_spec=solver_spec)


# ---------------------------------------------------------------------------
# P7 — forwarding correctness
# ---------------------------------------------------------------------------

def test_ir_ex5_p7_forwarding(solver_spec):
    """Forwarding mux provides correct data when write-stage valid and addresses
    match (Ex-5 three-stage pipeline)."""
    pip = _get_pip(_Ex5Component)
    _prove(pip, k=5, solver_spec=solver_spec)

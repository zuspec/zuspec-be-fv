"""Unit tests for PipelineExprToSMT2 — no SMT solver required.

Tests verify that Python AST expressions (the kind produced in PipelineIR
stall_cond / cancel_cond fields) are lowered to correct SMT2 Bool strings.
"""
from __future__ import annotations

import ast

import pytest

from zuspec.be.fv.pipeline.expr_to_smt2 import PipelineExprToSMT2


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _parse(src: str) -> ast.expr:
    """Parse *src* as a Python expression and return its AST node."""
    return ast.parse(src, mode="eval").body


def _make_resolver(mapping: dict) -> callable:
    """Return a SignalResolver that looks up names in *mapping*."""
    def resolve(name: str, state_var: str) -> str | None:
        if name in mapping:
            return f"(|M#{mapping[name]}| {state_var})"
        return None
    return resolve


_SIMPLE_RESOLVER = _make_resolver({
    "stall": "stall",
    "valid": "valid_if",
    "a": "a_if_to_ex",
    "b": "b_if_to_ex",
})


def _lower(src: str, resolver=None, state_var: str = "state") -> str:
    if resolver is None:
        resolver = _SIMPLE_RESOLVER
    lowerer = PipelineExprToSMT2(resolver, state_var=state_var)
    return lowerer.lower(_parse(src))


# ---------------------------------------------------------------------------
# Constant literals
# ---------------------------------------------------------------------------

def test_constant_true():
    assert _lower("True") == "true"


def test_constant_false():
    assert _lower("False") == "false"


def test_constant_int():
    result = _lower("42")
    assert "42" in result and "bv" in result


# ---------------------------------------------------------------------------
# Name references
# ---------------------------------------------------------------------------

def test_name_lookup():
    result = _lower("stall")
    assert "M#stall" in result
    assert "state" in result


def test_name_unknown_raises():
    with pytest.raises(ValueError, match="Unknown name"):
        _lower("unknown_signal")


# ---------------------------------------------------------------------------
# Attribute reads (self.X)
# ---------------------------------------------------------------------------

def test_self_attr():
    result = _lower("self.stall")
    assert "M#stall" in result


def test_non_self_attr_raises():
    with pytest.raises(ValueError, match="Unsupported attribute"):
        _lower("other.stall")


# ---------------------------------------------------------------------------
# Boolean operations
# ---------------------------------------------------------------------------

def test_bool_and():
    result = _lower("stall and valid")
    assert result.startswith("(and ")
    assert "M#stall" in result
    assert "M#valid_if" in result


def test_bool_or():
    result = _lower("stall or valid")
    assert result.startswith("(or ")


def test_unary_not():
    result = _lower("not stall")
    assert result.startswith("(not ")
    assert "M#stall" in result


# ---------------------------------------------------------------------------
# Comparison operators
# ---------------------------------------------------------------------------

def test_eq():
    result = _lower("a == b")
    assert result.startswith("(= ")


def test_neq():
    result = _lower("a != b")
    assert "(not" in result and "(=" in result


def test_lt():
    result = _lower("a < b")
    assert "bvult" in result


def test_lte():
    result = _lower("a <= b")
    assert "bvule" in result


def test_gt():
    result = _lower("a > b")
    assert "bvugt" in result


def test_gte():
    result = _lower("a >= b")
    assert "bvuge" in result


# ---------------------------------------------------------------------------
# Chained comparison should raise
# ---------------------------------------------------------------------------

def test_chained_comparison_raises():
    with pytest.raises(ValueError, match="single-comparison"):
        _lower("a < b < a")  # chained — not supported


# ---------------------------------------------------------------------------
# Nested expressions
# ---------------------------------------------------------------------------

def test_nested_and_or():
    result = _lower("(stall and valid) or not stall")
    assert "(or " in result
    assert "(and " in result
    assert "(not " in result


# ---------------------------------------------------------------------------
# State variable is forwarded correctly
# ---------------------------------------------------------------------------

def test_state_var_propagated():
    lowerer = PipelineExprToSMT2(_SIMPLE_RESOLVER, state_var="state_k")
    result = lowerer.lower(_parse("stall"))
    assert "state_k" in result


# ---------------------------------------------------------------------------
# Generic unsupported node raises
# ---------------------------------------------------------------------------

def test_unsupported_node_raises():
    lowerer = PipelineExprToSMT2(_SIMPLE_RESOLVER)
    # Pass a raw AST node type that is not handled (e.g. a lambda)
    node = ast.parse("lambda: True", mode="eval").body
    with pytest.raises(ValueError):
        lowerer.lower(node)

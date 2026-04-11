"""Lower a Python AST expression (from PipelineIR.stall_cond / cancel_cond)
to an SMT2 Bool expression referencing pipeline state signals.

The input expressions come from the ``@zdc.pipeline`` decorator body, which uses
a restricted set of Python operators:

- Comparisons: ``==``, ``!=``, ``<``, ``<=``, ``>``, ``>=``
- Boolean: ``and``, ``or``, ``not``
- Attribute reads: ``self.X`` — component port → port signal name
- Name reads: ``VAR`` — pipeline variable → channel register accessor
- Constants: ``int`` literals, ``True``, ``False``

The translator walks the AST and produces the corresponding SMT2 expression.
Context is needed to resolve variable names to accessor terms.
"""
from __future__ import annotations

import ast
from typing import Callable, Optional


# Signature: (name, state_var) → SMT2 accessor term string, or None if unknown.
SignalResolver = Callable[[str, str], Optional[str]]


class PipelineExprToSMT2(ast.NodeVisitor):
    """Recursively lower an AST expression to an SMT2 Bool expression.

    :param resolve_signal: ``Callable(name, state_var) → SMT2 term`` that maps
        a pipeline variable or port name to the corresponding SMT2 accessor term
        (e.g. ``"(|M#var_if_to_ex| state)"``).  Return ``None`` for unknown names.
    :param state_var: The SMT2 state variable name in scope, e.g. ``"state"``.
    :param width_of: Optional ``Callable(name) → int`` giving the bit-width of a
        signal for constant literal coercion.  Defaults to 32.

    :raises ValueError: For unsupported AST node types, unknown names, or multi-
        comparison expressions.
    """

    def __init__(
        self,
        resolve_signal: SignalResolver,
        state_var: str = "state",
        width_of: Optional[Callable[[str], int]] = None,
    ) -> None:
        self._resolve = resolve_signal
        self._state = state_var
        self._width_of = width_of or (lambda _: 32)

    def lower(self, node: ast.expr) -> str:
        """Lower *node* to an SMT2 Bool string.

        :param node: AST expression node (from ``stall_cond`` / ``cancel_cond``
            fields of :class:`~zuspec.synth.ir.pipeline_ir.StageIR`).
        :returns: SMT2 Bool expression string.
        :raises ValueError: If the node type is not supported or a name cannot
            be resolved.
        """
        result = self.visit(node)
        if result is None:
            raise ValueError(f"Cannot lower AST node: {ast.dump(node)}")
        return result

    # ------------------------------------------------------------------ #
    # Visitor methods                                                      #
    # ------------------------------------------------------------------ #

    def visit_Constant(self, node: ast.Constant) -> str:
        """Lower a constant literal.

        Boolean constants become ``"true"`` / ``"false"``.
        Integer constants become 32-bit bitvector literals.

        :raises ValueError: For non-bool, non-int constants.
        """
        if isinstance(node.value, bool):
            return "true" if node.value else "false"
        if isinstance(node.value, int):
            return f"(_ bv{node.value} 32)"
        raise ValueError(f"Unsupported constant: {node.value!r}")

    def visit_Name(self, node: ast.Name) -> str:
        """Lower a bare name reference (pipeline variable or free signal).

        :raises ValueError: If the name cannot be resolved.
        """
        term = self._resolve(node.id, self._state)
        if term is None:
            raise ValueError(f"Unknown name: {node.id!r}")
        return term

    def visit_Attribute(self, node: ast.Attribute) -> str:
        """Lower a ``self.X`` component port attribute read.

        Only ``self.X`` is supported; other attribute forms raise ``ValueError``.

        :raises ValueError: If the attribute is not a ``self.X`` form or if the
            port name cannot be resolved.
        """
        if (
            isinstance(node.value, ast.Name)
            and node.value.id == "self"
        ):
            term = self._resolve(node.attr, self._state)
            if term is None:
                raise ValueError(f"Unknown port: {node.attr!r}")
            return term
        raise ValueError(f"Unsupported attribute: {ast.dump(node)}")

    def visit_BoolOp(self, node: ast.BoolOp) -> str:
        """Lower ``and`` / ``or`` boolean operations."""
        operands = [self.visit(v) for v in node.values]
        op = "and" if isinstance(node.op, ast.And) else "or"
        return f"({op} {' '.join(operands)})"

    def visit_UnaryOp(self, node: ast.UnaryOp) -> str:
        """Lower unary ``not``.

        :raises ValueError: For unsupported unary operators.
        """
        operand = self.visit(node.operand)
        if isinstance(node.op, ast.Not):
            return f"(not {operand})"
        raise ValueError(f"Unsupported unary op: {type(node.op).__name__}")

    def visit_Compare(self, node: ast.Compare) -> str:
        """Lower a single comparison expression to SMT2.

        Only single-operator, single-comparator comparisons are supported
        (e.g. ``a == b``).  Chained comparisons (e.g. ``0 < x < 10``) raise
        ``ValueError``.

        :raises ValueError: For chained comparisons or unsupported operators.
        """
        if len(node.ops) != 1 or len(node.comparators) != 1:
            raise ValueError(
                "Only single-comparison expressions are supported; "
                f"got {len(node.ops)} ops in: {ast.dump(node)}"
            )
        left = self.visit(node.left)
        right = self.visit(node.comparators[0])
        op = node.ops[0]
        smt_op = {
            ast.Eq:    "=",
            ast.NotEq: None,   # emit (not (= ...))
            ast.Lt:    "bvult",
            ast.LtE:   "bvule",
            ast.Gt:    "bvugt",
            ast.GtE:   "bvuge",
        }.get(type(op))
        if smt_op is None:
            return f"(not (= {left} {right}))"
        return f"({smt_op} {left} {right})"

    def generic_visit(self, node: ast.AST) -> str:
        """Raise ``ValueError`` for any unsupported AST node type.

        :raises ValueError: Always, for node types not explicitly handled.
        """
        raise ValueError(
            f"Cannot lower AST node type {type(node).__name__}: {ast.dump(node)}"
        )

"""SMT2 expression builder helpers specific to the pipeline state sort."""
from __future__ import annotations


def bitvec_sort(width: int) -> str:
    """Return SMT2 sort string for a bitvector of *width* bits.

    :param width: Number of bits.
    :returns: e.g. ``"(_ BitVec 32)"``.
    """
    return f"(_ BitVec {width})"


def bv_lit(value: int, width: int) -> str:
    """Return SMT2 bitvector literal.

    :param value: Integer value.
    :param width: Bit-width of the literal.
    :returns: e.g. ``"(_ bv42 32)"``.
    """
    return f"(_ bv{value} {width})"


def bv_zero(width: int) -> str:
    """Return SMT2 bitvector zero literal.

    :param width: Bit-width.
    :returns: ``"(_ bv0 <width>)"``.
    """
    return bv_lit(0, width)


def bool_to_bv1(smt_bool: str) -> str:
    """Cast an SMT2 ``Bool`` expression to ``(_ BitVec 1)``.

    :param smt_bool: SMT2 Boolean expression string.
    :returns: ``"(ite <smt_bool> #b1 #b0)"``.
    """
    return f"(ite {smt_bool} #b1 #b0)"


def bv1_to_bool(smt_bv: str) -> str:
    """Cast a ``(_ BitVec 1)`` expression to ``Bool``.

    :param smt_bv: SMT2 bitvec-1 expression string.
    :returns: ``"(= <smt_bv> #b1)"``.
    """
    return f"(= {smt_bv} #b1)"


def ite(cond: str, then_: str, else_: str) -> str:
    """Return SMT2 if-then-else expression.

    :param cond: Boolean condition expression.
    :param then_: Value when condition is true.
    :param else_: Value when condition is false.
    :returns: ``"(ite <cond> <then_> <else_>)"``.
    """
    return f"(ite {cond} {then_} {else_})"


def and_(*args: str) -> str:
    """Return SMT2 conjunction of one or more expressions.

    :param args: One or more SMT2 Bool expression strings.
    :returns: Single expression or ``"(and ...)"`` when more than one argument.
    """
    if len(args) == 1:
        return args[0]
    return f"(and {' '.join(args)})"


def or_(*args: str) -> str:
    """Return SMT2 disjunction of one or more expressions.

    :param args: One or more SMT2 Bool expression strings.
    :returns: Single expression or ``"(or ...)"`` when more than one argument.
    """
    if len(args) == 1:
        return args[0]
    return f"(or {' '.join(args)})"


def not_(arg: str) -> str:
    """Return SMT2 negation.

    :param arg: SMT2 Bool expression.
    :returns: ``"(not <arg>)"``.
    """
    return f"(not {arg})"


def eq(a: str, b: str) -> str:
    """Return SMT2 equality expression.

    :param a: Left-hand side expression.
    :param b: Right-hand side expression.
    :returns: ``"(= <a> <b>)"``.
    """
    return f"(= {a} {b})"

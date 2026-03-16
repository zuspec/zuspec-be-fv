"""Shared SMT-LIB2 bitvector string-level utilities.

Pure string-to-string functions — no IR types, no context objects.
Used by both the RTL → SMT-LIB2 translator (rtl/expr_translator.py) and the
rand → SMT-LIB2 emitter (smt2/rand_emitter.py).
"""

import math


def bitvec_sort(width: int) -> str:
    """Return the SMT-LIB2 sort for a bitvector of the given width."""
    return f"(_ BitVec {width})"


def bitvec_lit(value: int, width: int) -> str:
    """Return a decimal-form bitvector literal ``(_ bvN width)``.

    ``value`` is interpreted as unsigned two's-complement; negative values are
    wrapped into the unsigned range before encoding.
    """
    if value < 0:
        value = (1 << width) + value
    value &= (1 << width) - 1
    return f"(_ bv{value} {width})"


def zero_extend(expr: str, from_w: int, to_w: int) -> str:
    """Zero-extend *expr* from *from_w* bits to *to_w* bits."""
    if from_w >= to_w:
        return expr
    return f"((_ zero_extend {to_w - from_w}) {expr})"


def sign_extend(expr: str, from_w: int, to_w: int) -> str:
    """Sign-extend *expr* from *from_w* bits to *to_w* bits."""
    if from_w >= to_w:
        return expr
    return f"((_ sign_extend {to_w - from_w}) {expr})"


def extend_bitvec(expr: str, from_w: int, to_w: int, signed: bool = False) -> str:
    """Extend *expr* to *to_w* bits using zero- or sign-extension."""
    if signed:
        return sign_extend(expr, from_w, to_w)
    return zero_extend(expr, from_w, to_w)


def min_bits_unsigned(value: int) -> int:
    """Minimum number of bits needed to represent a non-negative integer."""
    if value <= 0:
        return 1
    bits = math.ceil(math.log2(value + 1))
    return bits if bits > 0 else 1


def arith_binop(op: str, signed: bool = False) -> str:
    """Map a Python arithmetic/bitwise operator string to an SMT-LIB2 bitvector operator.

    Supported *op* values: ``+  -  *  /  //  %  &  |  ^  <<  >>``
    """
    _map_unsigned = {
        '+':  'bvadd',
        '-':  'bvsub',
        '*':  'bvmul',
        '/':  'bvudiv',
        '//': 'bvudiv',
        '%':  'bvurem',
        '&':  'bvand',
        '|':  'bvor',
        '^':  'bvxor',
        '<<': 'bvshl',
        '>>': 'bvlshr',
    }
    _map_signed = {
        '+':  'bvadd',
        '-':  'bvsub',
        '*':  'bvmul',
        '/':  'bvsdiv',
        '//': 'bvsdiv',
        '%':  'bvsrem',
        '&':  'bvand',
        '|':  'bvor',
        '^':  'bvxor',
        '<<': 'bvshl',
        '>>': 'bvashr',
    }
    table = _map_signed if signed else _map_unsigned
    if op not in table:
        raise ValueError(f"Unsupported arithmetic operator: {op!r}")
    return table[op]


def cmp_binop(op: str, signed: bool = False) -> str:
    """Map a Python comparison operator string to an SMT-LIB2 bitvector predicate.

    Supported *op* values: ``==  !=  <  <=  >  >=``
    """
    _unsigned = {
        '==': '=',
        '!=': 'distinct',
        '<':  'bvult',
        '<=': 'bvule',
        '>':  'bvugt',
        '>=': 'bvuge',
    }
    _signed = {
        '==': '=',
        '!=': 'distinct',
        '<':  'bvslt',
        '<=': 'bvsle',
        '>':  'bvsgt',
        '>=': 'bvsge',
    }
    table = _signed if signed else _unsigned
    if op not in table:
        raise ValueError(f"Unsupported comparison operator: {op!r}")
    return table[op]

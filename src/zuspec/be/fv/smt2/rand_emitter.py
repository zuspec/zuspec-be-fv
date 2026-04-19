"""SMT-LIB2 emitter for constrained randomization.

Translates a ``@zdc.dataclass`` class (with ``rand`` fields and
``@zdc.constraint`` methods) into a complete SMT-LIBv2 query that can be
solved by any QF_BV-capable solver (bitwuzla, z3, cvc5, …).

This is intentionally separate from the RTL → SMT-LIB2 pipeline in
``zuspec.be.fv.rtl``: randomization is a one-shot satisfiability check over
independent variables, not a state-machine transition relation.

Usage::

    from zuspec.be.fv.smt2.rand_emitter import RandSMT2Emitter

    emitter = RandSMT2Emitter()
    smt2_text = emitter.emit(MemTransaction, seed=42)
    # write to a file and pass to bitwuzla/z3/cvc5
"""

from __future__ import annotations

from typing import Any, Dict, List, Optional, Tuple

from . import bitvec_ops


# ---------------------------------------------------------------------------
# Lazy import of zuspec-dataclasses helpers to avoid hard compile-time dep
# ---------------------------------------------------------------------------

def _get_constraint_parser():
    from zuspec.dataclasses.constraint_parser import ConstraintParser
    return ConstraintParser


def _get_extract_rand_fields():
    from zuspec.dataclasses.constraint_parser import extract_rand_fields
    return extract_rand_fields


# ---------------------------------------------------------------------------
# Width inference for the dict-based constraint IR produced by ConstraintParser
# ---------------------------------------------------------------------------

class _WidthInferrer:
    """Bottom-up minimum-width estimator for constraint IR dicts."""

    def __init__(self, field_widths: Dict[str, int]):
        self._fw = field_widths

    def infer(self, expr: Dict[str, Any]) -> int:
        t = expr['type']
        if t == 'attribute':
            return self._fw.get(expr['attr'], 32)
        if t == 'constant':
            return bitvec_ops.min_bits_unsigned(expr['value'])
        if t == 'bin_op':
            lw = self.infer(expr['left'])
            rw = self.infer(expr['right'])
            if expr['op'] in ('+', '-', '*'):
                # Extra bit to avoid modular overflow in comparisons
                return max(lw, rw) + 1
            # For %, &, |, ^, <<, >>, /: result fits in max(lw, rw) bits
            return max(lw, rw)
        if t in ('compare', 'bool_op', 'implies'):
            return 1  # Boolean result
        if t == 'unary_op':
            return self.infer(expr['operand'])
        return 32  # Conservative fallback


# ---------------------------------------------------------------------------
# Expression translator: dict IR → SMT-LIB2 string
# ---------------------------------------------------------------------------

class _ExprTranslator:
    """Translate ConstraintParser dict IR to SMT-LIB2 expressions.

    All bitvector operands are widened to a *target_w* so that every
    sub-expression at a given node has a uniform sort.
    """

    def __init__(self, field_widths: Dict[str, int]):
        self._fw = field_widths
        self._wi = _WidthInferrer(field_widths)

    def translate(
        self, expr: Dict[str, Any], target_w: Optional[int] = None
    ) -> Tuple[str, int]:
        """Return ``(smt2_str, actual_width)``."""
        t = expr['type']

        if t == 'attribute':
            name = expr['attr']
            w = self._fw.get(name, 32)
            s = name
            if target_w and target_w > w:
                s = bitvec_ops.zero_extend(s, w, target_w)
                w = target_w
            return s, w

        if t == 'constant':
            v = expr['value']
            w = target_w if target_w else bitvec_ops.min_bits_unsigned(v)
            return bitvec_ops.bitvec_lit(v, w), w

        if t == 'bin_op':
            return self._translate_bin_op(expr, target_w)

        if t == 'compare':
            return self._translate_compare(expr)

        if t == 'bool_op':
            smt_op = 'and' if expr['op'] == 'and' else 'or'
            parts = [self.translate(v)[0] for v in expr['values']]
            return f"({smt_op} {' '.join(parts)})", 1

        if t == 'unary_op':
            return self._translate_unary(expr, target_w)

        if t == 'implies':
            ante_s, _ = self.translate(expr['antecedent'])
            cons_s, _ = self.translate(expr['consequent'])
            return f"(=> {ante_s} {cons_s})", 1

        raise ValueError(f"Unsupported constraint IR node type: {t!r}")

    # ------------------------------------------------------------------
    def _translate_bin_op(
        self, expr: Dict[str, Any], target_w: Optional[int]
    ) -> Tuple[str, int]:
        op = expr['op']
        lw = self._wi.infer(expr['left'])
        rw = self._wi.infer(expr['right'])
        if op in ('+', '-', '*'):
            op_w = max(lw, rw) + 1
        else:
            op_w = max(lw, rw)

        lhs_s, _ = self.translate(expr['left'], target_w=op_w)
        rhs_s, _ = self.translate(expr['right'], target_w=op_w)
        smt_op = bitvec_ops.arith_binop(op)
        result_s = f"({smt_op} {lhs_s} {rhs_s})"
        result_w = op_w

        if target_w and target_w > result_w:
            result_s = bitvec_ops.zero_extend(result_s, result_w, target_w)
            result_w = target_w
        return result_s, result_w

    def _translate_compare(self, expr: Dict[str, Any]) -> Tuple[str, int]:
        # Determine the common width for all operands in this comparison
        all_exprs = [expr['left']] + list(expr['comparators'])
        cmp_w = max(self._wi.infer(e) for e in all_exprs)

        left_s, _ = self.translate(expr['left'], target_w=cmp_w)

        parts: List[str] = []
        prev_s = left_s
        for op, comp in zip(expr['ops'], expr['comparators']):
            rhs_s, _ = self.translate(comp, target_w=cmp_w)
            smt_op = bitvec_ops.cmp_binop(op)
            parts.append(f"({smt_op} {prev_s} {rhs_s})")
            prev_s = rhs_s

        if len(parts) == 1:
            return parts[0], 1
        return f"(and {' '.join(parts)})", 1

    def _translate_unary(
        self, expr: Dict[str, Any], target_w: Optional[int]
    ) -> Tuple[str, int]:
        op = expr['op']
        val_s, val_w = self.translate(expr['operand'], target_w=target_w)
        if op == 'not':
            return f"(not {val_s})", 1
        if op == '-':
            return f"(bvneg {val_s})", val_w
        # unary '+' — identity
        return val_s, val_w


# ---------------------------------------------------------------------------
# Public emitter
# ---------------------------------------------------------------------------

class RandSMT2Emitter:
    """Emit a complete SMT-LIBv2 query for one randomization draw.

    The query uses the ``QF_BV`` logic (quantifier-free bitvectors) and
    contains:

    1. ``(set-option :seed N)`` — caller supplies the seed for diversity
    2. ``(set-option :produce-models true)``
    3. ``(set-logic QF_BV)``
    4. ``(declare-const …)`` for every ``rand`` field
    5. ``(assert …)`` for domain bounds derived from ``rand(domain=…)``
    6. ``(assert …)`` for each ``@zdc.constraint`` method body
    7. ``(check-sat)``
    8. ``(get-value (…))`` listing all rand fields

    Example::

        emitter = RandSMT2Emitter()
        text = emitter.emit(MemTransaction, seed=0)
        # → write to file, pass to bitwuzla --smt2 <file>
    """

    def emit(self, cls: type, seed: int = 0) -> str:
        """Return a complete SMT-LIBv2 string for one randomization query."""
        extract_rand_fields = _get_extract_rand_fields()
        ConstraintParser = _get_constraint_parser()

        fields = extract_rand_fields(cls)
        if not fields:
            raise ValueError(f"{cls.__name__} has no rand fields")

        field_widths = self._compute_field_widths(fields)
        xlator = _ExprTranslator(field_widths)

        lines: List[str] = []
        lines.append(f"(set-option :seed {seed})")
        lines.append("(set-option :produce-models true)")
        lines.append("(set-logic QF_BV)")
        lines.append("")

        # Variable declarations
        for f in fields:
            name = f['name']
            w = field_widths[name]
            lines.append(f"(declare-const {name} (_ BitVec {w}))")
        lines.append("")

        # Domain constraints
        for f in fields:
            name = f['name']
            w = field_widths[name]
            domain = f.get('domain')
            if domain is None:
                continue
            if (
                isinstance(domain, (list, tuple))
                and len(domain) == 2
                and all(isinstance(v, int) for v in domain)
            ):
                lo, hi = domain
                lines.append(
                    f"(assert (bvuge {name} {bitvec_ops.bitvec_lit(lo, w)}))"
                )
                lines.append(
                    f"(assert (bvule {name} {bitvec_ops.bitvec_lit(hi, w)}))"
                )
            elif isinstance(domain, (list, tuple)):
                # Enumerated domain: (assert (or (= name v0) (= name v1) ...))
                eqs = " ".join(
                    f"(= {name} {bitvec_ops.bitvec_lit(v, w)})" for v in domain
                )
                lines.append(f"(assert (or {eqs}))")
        lines.append("")

        # User constraints from @constraint methods
        parser = ConstraintParser()
        constraints = parser.extract_constraints(cls)
        for cinfo in constraints:
            # Postconditions (ensures) are not inputs to the randomization
            # solver — they are verified after the body executes.
            if cinfo.get('role') == 'ensures':
                continue
            cname = cinfo['name']
            for expr_dict in cinfo['exprs']:
                smt_s, _ = xlator.translate(expr_dict)
                lines.append(f"(assert {smt_s})  ; {cname}")
        lines.append("")

        lines.append("(check-sat)")
        field_names = " ".join(f['name'] for f in fields)
        lines.append(f"(get-value ({field_names}))")
        lines.append("")

        return "\n".join(lines)

    def emit_dead_action_check(self, cls: type) -> str:
        """Return SMT-LIBv2 that checks whether *cls* can ever execute.

        Includes only ``@constraint.requires`` and role-less (plain)
        ``@constraint`` methods.  If the resulting query is UNSAT the
        action is *dead* — its preconditions can never be satisfied.

        Returns a complete SMT-LIBv2 string (``(check-sat)`` only, no
        ``(get-value …)``).
        """
        return self._emit_sat_check(cls, include_roles={'requires', None})

    def emit_contract_check(self, cls: type) -> str:
        """Return SMT-LIBv2 for a refutation check of ``@constraint.ensures``.

        The query asserts:
        * All ``requires`` + plain constraints (the preconditions), AND
        * The **negation** of the conjunction of all ``ensures`` expressions.

        If the query is UNSAT the ensures postconditions *always* hold
        under the preconditions.  If SAT a counterexample is returned.

        Returns a complete SMT-LIBv2 string.
        """
        return self._emit_sat_check(cls, include_roles={'requires', None},
                                    negate_roles={'ensures'})

    def _emit_sat_check(
        self,
        cls: type,
        include_roles: set,
        negate_roles: Optional[set] = None,
    ) -> str:
        """Shared helper for :meth:`emit_dead_action_check` and
        :meth:`emit_contract_check`."""
        extract_rand_fields = _get_extract_rand_fields()
        ConstraintParser = _get_constraint_parser()

        fields = extract_rand_fields(cls)
        if not fields:
            raise ValueError(f"{cls.__name__} has no rand fields")

        field_widths = self._compute_field_widths(fields)
        xlator = _ExprTranslator(field_widths)

        lines: List[str] = []
        lines.append("(set-option :produce-models true)")
        lines.append("(set-logic QF_BV)")
        lines.append("")

        for f in fields:
            name = f['name']
            w = field_widths[name]
            lines.append(f"(declare-const {name} (_ BitVec {w}))")
        lines.append("")

        # Domain bounds
        for f in fields:
            name = f['name']
            w = field_widths[name]
            domain = f.get('domain')
            if domain is None:
                continue
            if (
                isinstance(domain, (list, tuple))
                and len(domain) == 2
                and all(isinstance(v, int) for v in domain)
            ):
                lo, hi = domain
                lines.append(
                    f"(assert (bvuge {name} {bitvec_ops.bitvec_lit(lo, w)}))"
                )
                lines.append(
                    f"(assert (bvule {name} {bitvec_ops.bitvec_lit(hi, w)}))"
                )
        lines.append("")

        parser = ConstraintParser()
        constraints = parser.extract_constraints(cls)

        negate_roles = negate_roles or set()
        negated_parts: List[str] = []

        for cinfo in constraints:
            role = cinfo.get('role')
            cname = cinfo['name']
            if role not in include_roles and role not in negate_roles:
                continue
            for expr_dict in cinfo['exprs']:
                smt_s, _ = xlator.translate(expr_dict)
                if role in negate_roles:
                    negated_parts.append(smt_s)
                else:
                    lines.append(f"(assert {smt_s})  ; {cname}")

        if negated_parts:
            # Assert NOT (ensures_1 ∧ ensures_2 ∧ …) — refutation
            if len(negated_parts) == 1:
                conj = negated_parts[0]
            else:
                conj = "(and " + " ".join(negated_parts) + ")"
            lines.append(f"(assert (not {conj}))  ; negated ensures")
        lines.append("")

        lines.append("(check-sat)")
        field_names = " ".join(f['name'] for f in fields)
        lines.append(f"(get-value ({field_names}))")
        lines.append("")

        return "\n".join(lines)

    def _compute_field_widths(self, fields: List[Dict[str, Any]]) -> Dict[str, int]:
        widths: Dict[str, int] = {}
        for f in fields:
            domain = f.get('domain')
            if domain is None:
                w = 32
            elif (
                isinstance(domain, (list, tuple))
                and len(domain) == 2
                and all(isinstance(v, int) for v in domain)
            ):
                _lo, hi = domain
                w = bitvec_ops.min_bits_unsigned(hi)
            elif isinstance(domain, (list, tuple)):
                w = bitvec_ops.min_bits_unsigned(max(domain))
            else:
                w = 32
            widths[f['name']] = max(w, 1)
        return widths


def parse_get_value(stdout: str, field_names: List[str]) -> Dict[str, int]:
    """Parse the ``(get-value …)`` response from an SMT-LIB2 solver.

    Supports ``(_ bvN W)`` decimal form and ``#b…`` / ``#x…`` literal forms.

    Returns a dict ``{field_name: int_value}``.
    """
    import re
    result: Dict[str, int] = {}

    # Match patterns like  (name (_ bvN W))  or  (name #b...)  or  (name #x...)
    bv_decimal = re.compile(r'\(\s*(\w+)\s+\(_\s+bv(\d+)\s+\d+\s*\)\s*\)')
    bv_binary  = re.compile(r'\(\s*(\w+)\s+#b([01]+)\s*\)')
    bv_hex     = re.compile(r'\(\s*(\w+)\s+#x([0-9a-fA-F]+)\s*\)')

    for m in bv_decimal.finditer(stdout):
        result[m.group(1)] = int(m.group(2))
    for m in bv_binary.finditer(stdout):
        result[m.group(1)] = int(m.group(2), 2)
    for m in bv_hex.finditer(stdout):
        result[m.group(1)] = int(m.group(2), 16)

    return result

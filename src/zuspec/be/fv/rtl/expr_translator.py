"""
Expression to SMT2 Translator - Phase 3 Complete Implementation.

Translates Zuspec expression AST nodes to SMT2 expressions with:
- Context-aware type inference
- Proper width extension
- Signed/unsigned operation selection
- Field reference resolution
"""

from typing import Any, Optional
import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')

try:
    from zuspec.dataclasses import ir
except ImportError:
    ir = None

from .translation_context import TranslationContext
from ..smt2.bitvec_ops import extend_bitvec as _extend_bitvec_shared


class ExprToSMT2Translator:
    """Translates Zuspec expressions to SMT2 format with full type handling.
    
    Phase 3 complete implementation with:
    - Type inference and width matching
    - Signed/unsigned operation selection
    - Proper bitvector extensions
    - Field reference resolution
    - Constant width inference
    """
    
    def __init__(self):
        """Initialize translator."""
        pass
    
    def translate(self, expr: Any, ctx: TranslationContext) -> str:
        """Translate an expression to SMT2.
        
        Args:
            expr: Expression node from Zuspec AST
            ctx: Translation context
            
        Returns:
            SMT2 expression string
        """
        if ir is None:
            raise ImportError("zuspec.dataclasses not available")
        
        # Dispatch to appropriate handler based on expression type
        if isinstance(expr, ir.ExprBin):
            return self.translate_bin(expr, ctx)
        elif isinstance(expr, ir.ExprUnary):
            return self.translate_unary(expr, ctx)
        elif isinstance(expr, ir.ExprConstant):
            return self.translate_constant(expr, ctx)
        elif isinstance(expr, ir.ExprRefField):
            return self.translate_ref_field(expr, ctx)
        elif isinstance(expr, ir.ExprRefParam):
            return self.translate_ref_param(expr, ctx)
        elif isinstance(expr, ir.ExprRefLocal):
            return self.translate_ref_local(expr, ctx)
        elif isinstance(expr, ir.TypeExprRefSelf):
            return self.translate_ref_self(expr, ctx)
        elif isinstance(expr, ir.ExprCall):
            return self.translate_call(expr, ctx)
        elif isinstance(expr, ir.ExprCompare):
            return self.translate_compare(expr, ctx)
        elif isinstance(expr, ir.ExprBool):
            return self.translate_bool(expr, ctx)
        else:
            # Fallback for unsupported expressions
            raise NotImplementedError(f"Expression type not yet supported: {type(expr)}")
    
    def translate_bin(self, expr: ir.ExprBin, ctx: TranslationContext) -> str:
        """Translate binary operation with proper type handling."""
        lhs_smt = self.translate(expr.lhs, ctx)
        rhs_smt = self.translate(expr.rhs, ctx)
        
        # Get types and widths
        lhs_width = ctx.get_bit_width(expr.lhs)
        rhs_width = ctx.get_bit_width(expr.rhs)
        lhs_signed = ctx.is_signed_type(expr.lhs)
        rhs_signed = ctx.is_signed_type(expr.rhs)
        
        # Extend to common width if needed
        if lhs_width != rhs_width:
            target_width = max(lhs_width, rhs_width)
            if lhs_width < target_width:
                lhs_smt = self._extend_bitvec(lhs_smt, lhs_width, target_width, lhs_signed)
                lhs_width = target_width
            if rhs_width < target_width:
                rhs_smt = self._extend_bitvec(rhs_smt, rhs_width, target_width, rhs_signed)
                rhs_width = target_width
        
        # Choose appropriate SMT2 operator
        is_signed = lhs_signed or rhs_signed
        smt_op = self._get_binary_op(expr.op, is_signed, lhs_width == 1)
        
        return f"({smt_op} {lhs_smt} {rhs_smt})"
    
    def _extend_bitvec(self, expr: str, from_width: int, to_width: int,
                       signed: bool) -> str:
        """Extend bitvector to target width (delegates to shared bitvec_ops).

        If *from_width* is 1 the source may be Bool in SMT2; convert to
        BV1 before applying zero/sign_extend.
        """
        if from_width == 1 and to_width > 1:
            # Source may be Bool in SMT2; convert to BV1 before extending.
            # BV1 literals are left as-is; Bool expressions get ite wrapping.
            if expr not in ('#b0', '#b1'):
                expr = f'(ite {expr} #b1 #b0)'
        return _extend_bitvec_shared(expr, from_width, to_width, signed)
    
    def _get_binary_op(self, op: ir.BinOp, is_signed: bool, is_bool: bool) -> str:
        """Get SMT2 operator for binary operation."""
        # Boolean operations
        if is_bool and op in [ir.BinOp.And, ir.BinOp.Or]:
            return {
                ir.BinOp.And: "and",
                ir.BinOp.Or: "or",
            }[op]
        
        # Comparison operations
        if op in [ir.BinOp.Lt, ir.BinOp.LtE, ir.BinOp.Gt, ir.BinOp.GtE]:
            if is_signed:
                return {
                    ir.BinOp.Lt: "bvslt",
                    ir.BinOp.LtE: "bvsle",
                    ir.BinOp.Gt: "bvsgt",
                    ir.BinOp.GtE: "bvsge",
                }[op]
            else:
                return {
                    ir.BinOp.Lt: "bvult",
                    ir.BinOp.LtE: "bvule",
                    ir.BinOp.Gt: "bvugt",
                    ir.BinOp.GtE: "bvuge",
                }[op]
        
        # Arithmetic and bitwise operations
        op_map = {
            ir.BinOp.Add: "bvadd",
            ir.BinOp.Sub: "bvsub",
            ir.BinOp.Mult: "bvmul",
            ir.BinOp.Div: "bvsdiv" if is_signed else "bvudiv",
            ir.BinOp.Mod: "bvsrem" if is_signed else "bvurem",
            ir.BinOp.BitAnd: "bvand",
            ir.BinOp.BitOr: "bvor",
            ir.BinOp.BitXor: "bvxor",
            ir.BinOp.LShift: "bvshl",
            ir.BinOp.RShift: "bvashr" if is_signed else "bvlshr",
            ir.BinOp.Eq: "=",
            ir.BinOp.NotEq: "distinct",
            ir.BinOp.And: "and",
            ir.BinOp.Or: "or",
        }
        
        if op not in op_map:
            raise ValueError(f"Unsupported binary operator: {op}")
        
        return op_map[op]
    
    def translate_unary(self, expr: ir.ExprUnary, ctx: TranslationContext) -> str:
        """Translate unary operation."""
        operand_smt = self.translate(expr.operand, ctx)
        
        op_map = {
            ir.UnaryOp.Invert: "bvnot",
            ir.UnaryOp.Not: "not",
            ir.UnaryOp.USub: "bvneg",
            ir.UnaryOp.UAdd: "",
        }
        
        if expr.op == ir.UnaryOp.UAdd:
            return operand_smt
        
        smt_op = op_map.get(expr.op)
        if not smt_op:
            raise ValueError(f"Unsupported unary operator: {expr.op}")
        
        return f"({smt_op} {operand_smt})"
    
    def translate_constant(self, expr: ir.ExprConstant, ctx: TranslationContext) -> str:
        """Translate constant value with context-aware width."""
        value = expr.value
        
        if isinstance(value, bool):
            return "true" if value else "false"
        
        elif isinstance(value, int):
            # Infer width from context
            inferred_type = ctx.infer_type(expr)
            if isinstance(inferred_type, ir.DataTypeInt):
                width = inferred_type.bits if inferred_type.bits > 0 else 32
            else:
                width = 32
            
            # Convert to bitvector
            if value >= 0:
                binary = bin(value)[2:].zfill(width)
            else:
                # Two's complement
                binary = bin((1 << width) + value)[2:].zfill(width)
            
            return f"#b{binary}"
        
        elif value is None:
            return "false"
        
        else:
            raise ValueError(f"Unsupported constant type: {type(value)}")
    
    def translate_ref_field(self, expr: ir.ExprRefField, ctx: TranslationContext) -> str:
        """Translate field reference to SMT signal access."""
        if isinstance(expr.base, ir.TypeExprRefSelf):
            smt_name = ctx.get_field_smt_name(expr.index)
            return f"(|{ctx.module.name}#{smt_name}| {ctx.state_var})"
        else:
            raise NotImplementedError(
                "Hierarchical field access not yet supported. "
                "Only self.field references are currently supported."
            )
    
    def translate_ref_param(self, expr: ir.ExprRefParam, ctx: TranslationContext) -> str:
        """Translate parameter reference."""
        if expr.name in ctx.param_map:
            return ctx.param_map[expr.name]
        return expr.name
    
    def translate_ref_local(self, expr: ir.ExprRefLocal, ctx: TranslationContext) -> str:
        """Translate local variable reference."""
        local_expr = ctx.get_local_var(expr.name)
        if local_expr:
            return local_expr
        raise ValueError(f"Local variable '{expr.name}' used before assignment")
    
    def translate_ref_self(self, expr: ir.TypeExprRefSelf, ctx: TranslationContext) -> str:
        """Translate self reference."""
        return ctx.state_var
    
    def translate_call(self, expr: ir.ExprCall, ctx: TranslationContext) -> str:
        """Translate function call."""
        raise NotImplementedError(
            "Function calls not yet supported in RTL expressions. "
            "Use direct operators instead."
        )
    
    @staticmethod
    def _is_bool_signal(expr, ctx):
        """Check if expr maps to a Bool-typed SMT2 signal (1-bit unsigned field)."""
        if not isinstance(expr, ir.ExprRefField):
            return False
        if not isinstance(expr.base, ir.TypeExprRefSelf):
            return False
        return ctx.get_bit_width(expr) == 1 and not ctx.is_signed_type(expr)

    @staticmethod
    def _coerce_bv1_to_bool(smt):
        """Convert a BitVec(1) literal to the equivalent Bool literal."""
        if smt == '#b1':
            return 'true'
        if smt == '#b0':
            return 'false'
        return f'(= {smt} #b1)'

    def _compare_pair(self, left_expr, right_expr, op, ctx):
        """Translate a single comparison pair, handling Bool/BV1 coercion."""
        left_smt = self.translate(left_expr, ctx)
        right_smt = self.translate(right_expr, ctx)
        is_signed = ctx.is_signed_type(left_expr) or ctx.is_signed_type(right_expr)
        left_width = ctx.get_bit_width(left_expr)
        right_width = ctx.get_bit_width(right_expr)

        # Coerce Bool/BitVec(1) mismatches for = and distinct
        if op in (ir.CmpOp.Eq, ir.CmpOp.NotEq):
            l_bool = self._is_bool_signal(left_expr, ctx)
            r_bool = self._is_bool_signal(right_expr, ctx)
            if l_bool and not r_bool and right_width == 1:
                right_smt = self._coerce_bv1_to_bool(right_smt)
                smt_op = self._get_comparison_op(op, is_signed)
                return f'({smt_op} {left_smt} {right_smt})'
            if r_bool and not l_bool and left_width == 1:
                left_smt = self._coerce_bv1_to_bool(left_smt)
                smt_op = self._get_comparison_op(op, is_signed)
                return f'({smt_op} {left_smt} {right_smt})'

        if left_width != right_width:
            target_width = max(left_width, right_width)
            if left_width < target_width:
                left_smt = self._extend_bitvec(left_smt, left_width, target_width,
                                               ctx.is_signed_type(left_expr))
            if right_width < target_width:
                right_smt = self._extend_bitvec(right_smt, right_width, target_width,
                                                ctx.is_signed_type(right_expr))

        smt_op = self._get_comparison_op(op, is_signed)
        return f'({smt_op} {left_smt} {right_smt})'

    def translate_compare(self, expr: ir.ExprCompare, ctx: TranslationContext) -> str:
        """Translate comparison expression with chained support."""
        if len(expr.comparators) == 1:
            return self._compare_pair(expr.left, expr.comparators[0],
                                      expr.ops[0], ctx)
        else:
            comparisons = []
            prev_expr = expr.left
            for op, comparator in zip(expr.ops, expr.comparators):
                comparisons.append(
                    self._compare_pair(prev_expr, comparator, op, ctx))
                prev_expr = comparator
            return f"(and {' '.join(comparisons)})"
    
    def _get_comparison_op(self, op: ir.CmpOp, is_signed: bool) -> str:
        """Get SMT2 comparison operator."""
        if op in [ir.CmpOp.Eq]:
            return "="
        elif op in [ir.CmpOp.NotEq]:
            return "distinct"
        elif op in [ir.CmpOp.Lt]:
            return "bvslt" if is_signed else "bvult"
        elif op in [ir.CmpOp.LtE]:
            return "bvsle" if is_signed else "bvule"
        elif op in [ir.CmpOp.Gt]:
            return "bvsgt" if is_signed else "bvugt"
        elif op in [ir.CmpOp.GtE]:
            return "bvsge" if is_signed else "bvuge"
        else:
            raise ValueError(f"Unsupported comparison operator: {op}")
    
    def translate_bool(self, expr: ir.ExprBool, ctx: TranslationContext) -> str:
        """Translate boolean operation."""
        values_smt = [self.translate(val, ctx) for val in expr.values]
        
        if expr.op == ir.BoolOp.And:
            return f"(and {' '.join(values_smt)})"
        elif expr.op == ir.BoolOp.Or:
            return f"(or {' '.join(values_smt)})"
        else:
            raise ValueError(f"Unsupported boolean operator: {expr.op}")

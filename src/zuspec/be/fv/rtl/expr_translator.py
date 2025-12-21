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
    from zuspec.dataclasses import dm
except ImportError:
    dm = None

from .translation_context import TranslationContext


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
        if dm is None:
            raise ImportError("zuspec.dataclasses not available")
        
        # Dispatch to appropriate handler based on expression type
        if isinstance(expr, dm.ExprBin):
            return self.translate_bin(expr, ctx)
        elif isinstance(expr, dm.ExprUnary):
            return self.translate_unary(expr, ctx)
        elif isinstance(expr, dm.ExprConstant):
            return self.translate_constant(expr, ctx)
        elif isinstance(expr, dm.ExprRefField):
            return self.translate_ref_field(expr, ctx)
        elif isinstance(expr, dm.ExprRefParam):
            return self.translate_ref_param(expr, ctx)
        elif isinstance(expr, dm.ExprRefLocal):
            return self.translate_ref_local(expr, ctx)
        elif isinstance(expr, dm.TypeExprRefSelf):
            return self.translate_ref_self(expr, ctx)
        elif isinstance(expr, dm.ExprCall):
            return self.translate_call(expr, ctx)
        elif isinstance(expr, dm.ExprCompare):
            return self.translate_compare(expr, ctx)
        elif isinstance(expr, dm.ExprBool):
            return self.translate_bool(expr, ctx)
        else:
            # Fallback for unsupported expressions
            raise NotImplementedError(f"Expression type not yet supported: {type(expr)}")
    
    def translate_bin(self, expr: dm.ExprBin, ctx: TranslationContext) -> str:
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
        """Extend bitvector to target width."""
        if from_width == to_width:
            return expr
        
        ext_bits = to_width - from_width
        if signed:
            return f"((_ sign_extend {ext_bits}) {expr})"
        else:
            return f"((_ zero_extend {ext_bits}) {expr})"
    
    def _get_binary_op(self, op: dm.BinOp, is_signed: bool, is_bool: bool) -> str:
        """Get SMT2 operator for binary operation."""
        # Boolean operations
        if is_bool and op in [dm.BinOp.And, dm.BinOp.Or]:
            return {
                dm.BinOp.And: "and",
                dm.BinOp.Or: "or",
            }[op]
        
        # Comparison operations
        if op in [dm.BinOp.Lt, dm.BinOp.LtE, dm.BinOp.Gt, dm.BinOp.GtE]:
            if is_signed:
                return {
                    dm.BinOp.Lt: "bvslt",
                    dm.BinOp.LtE: "bvsle",
                    dm.BinOp.Gt: "bvsgt",
                    dm.BinOp.GtE: "bvsge",
                }[op]
            else:
                return {
                    dm.BinOp.Lt: "bvult",
                    dm.BinOp.LtE: "bvule",
                    dm.BinOp.Gt: "bvugt",
                    dm.BinOp.GtE: "bvuge",
                }[op]
        
        # Arithmetic and bitwise operations
        op_map = {
            dm.BinOp.Add: "bvadd",
            dm.BinOp.Sub: "bvsub",
            dm.BinOp.Mult: "bvmul",
            dm.BinOp.Div: "bvsdiv" if is_signed else "bvudiv",
            dm.BinOp.Mod: "bvsrem" if is_signed else "bvurem",
            dm.BinOp.BitAnd: "bvand",
            dm.BinOp.BitOr: "bvor",
            dm.BinOp.BitXor: "bvxor",
            dm.BinOp.LShift: "bvshl",
            dm.BinOp.RShift: "bvashr" if is_signed else "bvlshr",
            dm.BinOp.Eq: "=",
            dm.BinOp.NotEq: "distinct",
            dm.BinOp.And: "and",
            dm.BinOp.Or: "or",
        }
        
        if op not in op_map:
            raise ValueError(f"Unsupported binary operator: {op}")
        
        return op_map[op]
    
    def translate_unary(self, expr: dm.ExprUnary, ctx: TranslationContext) -> str:
        """Translate unary operation."""
        operand_smt = self.translate(expr.operand, ctx)
        
        op_map = {
            dm.UnaryOp.Invert: "bvnot",
            dm.UnaryOp.Not: "not",
            dm.UnaryOp.USub: "bvneg",
            dm.UnaryOp.UAdd: "",
        }
        
        if expr.op == dm.UnaryOp.UAdd:
            return operand_smt
        
        smt_op = op_map.get(expr.op)
        if not smt_op:
            raise ValueError(f"Unsupported unary operator: {expr.op}")
        
        return f"({smt_op} {operand_smt})"
    
    def translate_constant(self, expr: dm.ExprConstant, ctx: TranslationContext) -> str:
        """Translate constant value with context-aware width."""
        value = expr.value
        
        if isinstance(value, bool):
            return "true" if value else "false"
        
        elif isinstance(value, int):
            # Infer width from context
            inferred_type = ctx.infer_type(expr)
            if isinstance(inferred_type, dm.DataTypeInt):
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
    
    def translate_ref_field(self, expr: dm.ExprRefField, ctx: TranslationContext) -> str:
        """Translate field reference to SMT signal access."""
        if isinstance(expr.base, dm.TypeExprRefSelf):
            smt_name = ctx.get_field_smt_name(expr.index)
            return f"(|{ctx.module.name}#{smt_name}| {ctx.state_var})"
        else:
            raise NotImplementedError(
                "Hierarchical field access not yet supported. "
                "Only self.field references are currently supported."
            )
    
    def translate_ref_param(self, expr: dm.ExprRefParam, ctx: TranslationContext) -> str:
        """Translate parameter reference."""
        if expr.name in ctx.param_map:
            return ctx.param_map[expr.name]
        return expr.name
    
    def translate_ref_local(self, expr: dm.ExprRefLocal, ctx: TranslationContext) -> str:
        """Translate local variable reference."""
        local_expr = ctx.get_local_var(expr.name)
        if local_expr:
            return local_expr
        raise ValueError(f"Local variable '{expr.name}' used before assignment")
    
    def translate_ref_self(self, expr: dm.TypeExprRefSelf, ctx: TranslationContext) -> str:
        """Translate self reference."""
        return ctx.state_var
    
    def translate_call(self, expr: dm.ExprCall, ctx: TranslationContext) -> str:
        """Translate function call."""
        raise NotImplementedError(
            "Function calls not yet supported in RTL expressions. "
            "Use direct operators instead."
        )
    
    def translate_compare(self, expr: dm.ExprCompare, ctx: TranslationContext) -> str:
        """Translate comparison expression with chained support."""
        if len(expr.comparators) == 1:
            left_smt = self.translate(expr.left, ctx)
            right_smt = self.translate(expr.comparators[0], ctx)
            
            is_signed = ctx.is_signed_type(expr.left) or ctx.is_signed_type(expr.comparators[0])
            left_width = ctx.get_bit_width(expr.left)
            right_width = ctx.get_bit_width(expr.comparators[0])
            
            if left_width != right_width:
                target_width = max(left_width, right_width)
                if left_width < target_width:
                    left_smt = self._extend_bitvec(left_smt, left_width, target_width, 
                                                   ctx.is_signed_type(expr.left))
                if right_width < target_width:
                    right_smt = self._extend_bitvec(right_smt, right_width, target_width,
                                                    ctx.is_signed_type(expr.comparators[0]))
            
            op = self._get_comparison_op(expr.ops[0], is_signed)
            return f"({op} {left_smt} {right_smt})"
        
        else:
            # Chained comparison
            comparisons = []
            prev_expr = expr.left
            
            for op, comparator in zip(expr.ops, expr.comparators):
                left_smt = self.translate(prev_expr, ctx)
                right_smt = self.translate(comparator, ctx)
                
                is_signed = ctx.is_signed_type(prev_expr) or ctx.is_signed_type(comparator)
                left_width = ctx.get_bit_width(prev_expr)
                right_width = ctx.get_bit_width(comparator)
                
                if left_width != right_width:
                    target_width = max(left_width, right_width)
                    if left_width < target_width:
                        left_smt = self._extend_bitvec(left_smt, left_width, target_width,
                                                       ctx.is_signed_type(prev_expr))
                    if right_width < target_width:
                        right_smt = self._extend_bitvec(right_smt, right_width, target_width,
                                                        ctx.is_signed_type(comparator))
                
                smt_op = self._get_comparison_op(op, is_signed)
                comparisons.append(f"({smt_op} {left_smt} {right_smt})")
                prev_expr = comparator
            
            return f"(and {' '.join(comparisons)})"
    
    def _get_comparison_op(self, op: dm.CmpOp, is_signed: bool) -> str:
        """Get SMT2 comparison operator."""
        if op in [dm.CmpOp.Eq]:
            return "="
        elif op in [dm.CmpOp.NotEq]:
            return "distinct"
        elif op in [dm.CmpOp.Lt]:
            return "bvslt" if is_signed else "bvult"
        elif op in [dm.CmpOp.LtE]:
            return "bvsle" if is_signed else "bvule"
        elif op in [dm.CmpOp.Gt]:
            return "bvsgt" if is_signed else "bvugt"
        elif op in [dm.CmpOp.GtE]:
            return "bvsge" if is_signed else "bvuge"
        else:
            raise ValueError(f"Unsupported comparison operator: {op}")
    
    def translate_bool(self, expr: dm.ExprBool, ctx: TranslationContext) -> str:
        """Translate boolean operation."""
        values_smt = [self.translate(val, ctx) for val in expr.values]
        
        if expr.op == dm.BoolOp.And:
            return f"(and {' '.join(values_smt)})"
        elif expr.op == dm.BoolOp.Or:
            return f"(or {' '.join(values_smt)})"
        else:
            raise ValueError(f"Unsupported boolean operator: {expr.op}")

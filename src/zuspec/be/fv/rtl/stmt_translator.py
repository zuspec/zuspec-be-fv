"""Statement to SMT2 Translator.

Translates Zuspec statement AST nodes into next-state expressions for
synchronous RTL processes.

Key semantics:
- Field assignments become register updates
- Local assignments are tracked in-context for subsequent expressions
- If/else is translated to ITE, preserving "last assignment wins" semantics
"""

from __future__ import annotations

from typing import Any, Dict, List
import sys

sys.path.insert(0, 'packages/zuspec-dataclasses/src')

try:
    from zuspec.dataclasses import ir
except ImportError:
    ir = None

from .smt2_module import SMT2Transition
from .translation_context import TranslationContext


class StmtToSMT2Translator:
    """Translates Zuspec statements to SMT2 transitions for sync processes."""

    def __init__(self, expr_translator):
        self.expr_translator = expr_translator

    def translate_sync_body(self, stmts: List[Any], ctx: TranslationContext) -> List[SMT2Transition]:
        """Translate a synchronous process body.

        Returns a single transition per assigned register with the final computed
        next value expression.
        """
        if ir is None:
            raise ImportError("zuspec.dataclasses not available")

        reg_next: Dict[str, str] = {}

        for stmt in stmts:
            self._apply_stmt(stmt, ctx, reg_next)

        return [SMT2Transition(register_name=reg, next_value_expr=expr) for reg, expr in reg_next.items()]

    def _apply_stmt(self, stmt: Any, ctx: TranslationContext, reg_next: Dict[str, str]):
        if isinstance(stmt, ir.StmtAssign):
            self._apply_assign(stmt, ctx, reg_next)
        elif isinstance(stmt, ir.StmtIf):
            self._apply_if(stmt, ctx, reg_next)
        elif isinstance(stmt, (ir.StmtAssert, ir.StmtAssume, ir.StmtCover, ir.StmtExpr, ir.StmtPass)):
            # Formal statements and side-effect-free exprs don't affect state updates
            return
        else:
            raise NotImplementedError(f"Statement type not yet supported: {type(stmt)}")

    def _apply_assign(self, stmt: ir.StmtAssign, ctx: TranslationContext, reg_next: Dict[str, str]):
        rhs_smt_base = self.expr_translator.translate(stmt.value, ctx)
        rhs_w_base = ctx.get_bit_width(stmt.value)

        for target in stmt.targets:
            if isinstance(target, ir.ExprRefField) and isinstance(target.base, ir.TypeExprRefSelf):
                reg = ctx.get_field_smt_name(target.index)
                tgt_w = ctx.get_bit_width(target)
                tgt_signed = ctx.is_signed_type(target)

                rhs_smt = rhs_smt_base
                rhs_w = rhs_w_base

                if rhs_w != tgt_w:
                    rhs_smt = self._extend(rhs_smt, rhs_w, tgt_w, tgt_signed)

                reg_next[reg] = rhs_smt

            elif isinstance(target, ir.ExprRefLocal):
                ctx.add_local_var(target.name, rhs_smt_base)

            else:
                raise ValueError(f"Unsupported assignment target: {type(target)}")

    def _apply_if(self, stmt: ir.StmtIf, ctx: TranslationContext, reg_next: Dict[str, str]):
        cond_smt = self.expr_translator.translate(stmt.test, ctx)

        base_reg_next = dict(reg_next)

        then_ctx = TranslationContext(
            component=ctx.component,
            module=ctx.module,
            field_map=ctx.field_map,
            local_vars=dict(ctx.local_vars),
            param_map=dict(ctx.param_map),
            type_cache=ctx.type_cache,
            state_var=ctx.state_var,
            next_state_var=ctx.next_state_var,
        )
        then_reg_next = dict(base_reg_next)
        for s in stmt.body:
            self._apply_stmt(s, then_ctx, then_reg_next)

        else_ctx = TranslationContext(
            component=ctx.component,
            module=ctx.module,
            field_map=ctx.field_map,
            local_vars=dict(ctx.local_vars),
            param_map=dict(ctx.param_map),
            type_cache=ctx.type_cache,
            state_var=ctx.state_var,
            next_state_var=ctx.next_state_var,
        )
        else_reg_next = dict(base_reg_next)
        for s in stmt.orelse:
            self._apply_stmt(s, else_ctx, else_reg_next)

        all_regs = set(then_reg_next.keys()) | set(else_reg_next.keys())
        for reg in all_regs:
            then_v = then_reg_next.get(reg, self._reg_current_expr(ctx, reg))
            else_v = else_reg_next.get(reg, self._reg_current_expr(ctx, reg))
            reg_next[reg] = f"(ite {cond_smt} {then_v} {else_v})"

        self._merge_locals_after_if(cond_smt, ctx, then_ctx, else_ctx)

    def _merge_locals_after_if(self, cond_smt: str, ctx: TranslationContext,
                              then_ctx: TranslationContext, else_ctx: TranslationContext):
        base_locals = ctx.local_vars
        then_locals = then_ctx.local_vars
        else_locals = else_ctx.local_vars

        all_names = set(then_locals.keys()) | set(else_locals.keys())
        for name in all_names:
            base_v = base_locals.get(name)
            then_v = then_locals.get(name, base_v)
            else_v = else_locals.get(name, base_v)

            if base_v is None and (then_v is None or else_v is None):
                continue

            if then_v is None or else_v is None:
                continue

            ctx.local_vars[name] = f"(ite {cond_smt} {then_v} {else_v})"

    def _reg_current_expr(self, ctx: TranslationContext, reg_smt_name: str) -> str:
        return f"(|{ctx.module.name}#{reg_smt_name}| {ctx.state_var})"

    def _extend(self, expr: str, from_w: int, to_w: int, signed: bool) -> str:
        if from_w == to_w:
            return expr
        ext = to_w - from_w
        return f"((_ sign_extend {ext}) {expr})" if signed else f"((_ zero_extend {ext}) {expr})"

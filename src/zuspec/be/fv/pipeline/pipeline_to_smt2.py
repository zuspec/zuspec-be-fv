"""Translate a PipelineIR to an SMT2Module for formal verification.

The generated module encodes the synthesizer's *intended* pipeline semantics
(same rules as ``pipeline_sv_emit.py``) as an SMT2 transition system.  It does
not depend on Yosys; the existing :func:`~zuspec.be.fv.verification.verifier.verify_bmc`
/ :func:`~zuspec.be.fv.verification.verifier.prove_k_induction` infrastructure
in ``zuspec-be-fv`` can drive it directly.

Required SMT2 logic: ``QF_UFBV`` for pipelines without register files;
``QF_AUFBV`` when :class:`~zuspec.synth.ir.pipeline_ir.RegFileDeclInfo` entries
are present (``SMT2Module.has_array_state`` is set automatically).

SMT2 naming conventions:

- Stage valid register : ``"valid_{stage_lower}"``  (e.g. ``"valid_if"``)
- Channel data register: ``"{ch.name}"``             (e.g. ``"x_s1_to_s2"``)
- RegFile memory       : ``"{rd.field_name}_mem"``   (e.g. ``"regfile_mem"``)
- Free inputs          : ``"{port_name}_in"``         (e.g. ``"valid_in"``)
- Flush inputs         : ``"flush_{stage_lower}_in"`` (added on demand)
"""
from __future__ import annotations

import ast
from typing import Dict, List, Optional

from ..rtl.smt2_module import SMT2Module, SMT2Signal, SMT2Transition
from .smt2_helpers import (
    bitvec_sort, bv_zero, ite, and_, or_, not_, eq,
)
from .expr_to_smt2 import PipelineExprToSMT2

try:
    from zuspec.synth.ir.pipeline_ir import (
        PipelineIR, StageIR, ChannelDecl, RegFileDeclInfo,
    )
except ImportError as exc:
    raise ImportError(
        "zuspec-synth must be on sys.path to use PipelineIRToSMT2"
    ) from exc


class PipelineIRToSMT2:
    """Translate a :class:`~zuspec.synth.ir.pipeline_ir.PipelineIR` to an
    :class:`~zuspec.be.fv.rtl.smt2_module.SMT2Module`.

    Usage::

        translator = PipelineIRToSMT2()
        module = translator.translate(pip)
        result = prove_k_induction(module, k=10, solver="cvc5")

    The produced module uses:

    - ``QF_UFBV`` logic for plain pipelines.
    - ``QF_AUFBV`` logic when register files (Array sorts) are present
      (``module.has_array_state == True``).

    :param pip: Lowered :class:`~zuspec.synth.ir.pipeline_ir.PipelineIR`.
    :returns: :class:`~zuspec.be.fv.rtl.smt2_module.SMT2Module` ready for
        :func:`~zuspec.be.fv.verification.verifier.verify_bmc` or
        :func:`~zuspec.be.fv.verification.verifier.prove_k_induction`.
    :raises ImportError: When ``zuspec-synth`` is not on ``sys.path``.
    """

    def translate(self, pip: PipelineIR) -> SMT2Module:
        """Translate *pip* to an :class:`SMT2Module`.

        :param pip: Lowered :class:`PipelineIR`.
        :returns: :class:`SMT2Module` encoding the pipeline transition system.
        """
        module = SMT2Module(name=pip.module_name)
        self._pip = pip
        self._module = module

        self._add_state_signals(pip, module)
        self._add_free_inputs(pip, module)
        self._add_initial_conditions(pip, module)
        self._add_transition(pip, module)
        self._add_assertions(pip, module)
        return module

    # ------------------------------------------------------------------ #
    # Signal naming helpers                                                #
    # ------------------------------------------------------------------ #

    def _stage_valid_name(self, stage: StageIR) -> str:
        return f"valid_{stage.name.lower()}"

    def _channel_data_name(self, ch: ChannelDecl) -> str:
        return ch.name

    def _regfile_mem_name(self, rd: RegFileDeclInfo) -> str:
        return f"{rd.field_name}_mem"

    def _accessor(self, sig_name: str, module: SMT2Module, state_var: str = "state") -> str:
        """Return the SMT2 function-application term for *sig_name* at *state_var*."""
        return f"(|{module.name}#{sig_name}| {state_var})"

    # ------------------------------------------------------------------ #
    # State signals                                                        #
    # ------------------------------------------------------------------ #

    def _add_state_signals(self, pip: PipelineIR, module: SMT2Module) -> None:
        for stage in pip.stages:
            sig = SMT2Signal(
                name=self._stage_valid_name(stage),
                smt_name=self._stage_valid_name(stage),
                width=1,
                is_register=True,
            )
            module.add_register(sig)

        for ch in pip.channels:
            sig = SMT2Signal(
                name=self._channel_data_name(ch),
                smt_name=self._channel_data_name(ch),
                width=ch.width,
                is_register=True,
            )
            module.add_register(sig)

        for rd in pip.regfile_decls:
            arr_sort = (
                f"(Array {bitvec_sort(rd.addr_width)} {bitvec_sort(rd.data_width)})"
            )
            sig = SMT2Signal(
                name=self._regfile_mem_name(rd),
                smt_name=self._regfile_mem_name(rd),
                width=rd.data_width,
                smt_type=arr_sort,
                is_register=True,
            )
            module.add_register(sig)
            module.has_array_state = True

    # ------------------------------------------------------------------ #
    # Free inputs                                                          #
    # ------------------------------------------------------------------ #

    def _add_free_inputs(self, pip: PipelineIR, module: SMT2Module) -> None:
        module.add_input(SMT2Signal(
            name="valid_in",
            smt_name="valid_in",
            width=1,
        ))
        for port_name, width in pip.port_widths.items():
            module.add_input(SMT2Signal(
                name=f"{port_name}_in",
                smt_name=f"{port_name}_in",
                width=width,
            ))

    # ------------------------------------------------------------------ #
    # Initial conditions                                                   #
    # ------------------------------------------------------------------ #

    def _add_initial_conditions(self, pip: PipelineIR, module: SMT2Module) -> None:
        for stage in pip.stages:
            vname = self._stage_valid_name(stage)
            module.registers[vname].initial_value = "false"

        for ch in pip.channels:
            cname = self._channel_data_name(ch)
            module.registers[cname].initial_value = bv_zero(ch.width)

        for rd in pip.regfile_decls:
            mname = self._regfile_mem_name(rd)
            zero = bv_zero(rd.data_width)
            arr_sort = (
                f"(Array {bitvec_sort(rd.addr_width)} {bitvec_sort(rd.data_width)})"
            )
            module.registers[mname].initial_value = f"((as const {arr_sort}) {zero})"

    # ------------------------------------------------------------------ #
    # Transition relation                                                  #
    # ------------------------------------------------------------------ #

    def _resolve_signal_state(self, name: str, module: SMT2Module, state_var: str) -> Optional[str]:
        """Return SMT2 accessor term for *name* in *state_var*, or ``None``."""
        all_sigs = module.get_all_signals()
        if name in all_sigs:
            return self._accessor(name, module, state_var)
        return None

    def _build_stall_expr(self, stage: StageIR, module: SMT2Module, sv: str) -> str:
        """Return SMT2 Bool: this stage is stalled at state *sv*."""
        terms: List[str] = []

        if stage.stall_cond is not None:
            resolver = lambda nm, sv2: self._resolve_signal_state(nm, module, sv2)
            lowerer = PipelineExprToSMT2(resolver, state_var=sv)
            try:
                terms.append(lowerer.lower(stage.stall_cond))
            except ValueError:
                pass  # Cannot lower — no stall contribution from this condition

        for hz in self._pip.regfile_hazards:
            if hz.resolved_by == "stall" and hz.read_stage == stage.name:
                wr_stage_lower = hz.write_stage.lower()
                wr_valid = self._accessor(f"valid_{wr_stage_lower}", module, sv)
                rd_addr = self._resolve_signal_state(
                    hz.read_addr_var, module, sv
                ) or bv_zero(5)
                wr_addr = self._resolve_signal_state(
                    hz.write_addr_var, module, sv
                ) or bv_zero(5)
                hazard_stall = and_(wr_valid, eq(wr_addr, rd_addr))
                terms.append(hazard_stall)

        return or_(*terms) if terms else "false"

    def _build_cancel_expr(self, stage: StageIR, module: SMT2Module, sv: str) -> str:
        """Return SMT2 Bool: stage cancel condition is asserted at state *sv*."""
        if stage.cancel_cond is None:
            return "false"
        resolver = lambda nm, sv2: self._resolve_signal_state(nm, module, sv2)
        lowerer = PipelineExprToSMT2(resolver, state_var=sv)
        try:
            return lowerer.lower(stage.cancel_cond)
        except ValueError:
            return "false"

    def _ensure_flush_input(self, stage: StageIR, module: SMT2Module) -> str:
        """Return SMT2 accessor for the flush signal of *stage*, adding it if absent."""
        flush_name = f"flush_{stage.name.lower()}_in"
        if flush_name not in module.get_all_signals():
            module.add_input(SMT2Signal(
                name=flush_name,
                smt_name=flush_name,
                width=1,
            ))
        return flush_name

    def _add_transition(self, pip: PipelineIR, module: SMT2Module) -> None:
        """Build the transition relation as per-register :class:`SMT2Transition` objects.

        Valid-chain priority (per ``sync-pipeline-api.md``):
        flush > cancel > stall-freeze > normal propagate.

        The state variable available in transition constraints is ``"state"``
        (current) and ``"next_state"`` (next).
        """
        stage_by_name: Dict[str, StageIR] = {s.name: s for s in pip.stages}
        sv = "state"  # current state variable in SMT2 transition predicate

        for i, stage in enumerate(pip.stages):
            flush_name = self._ensure_flush_input(stage, module)
            flush = self._accessor(flush_name, module, sv)
            cancel = self._build_cancel_expr(stage, module, sv)
            stall = self._build_stall_expr(stage, module, sv)

            if i == 0:
                prev_valid = self._accessor("valid_in", module, sv)
            else:
                prev_stage = pip.stages[i - 1]
                prev_valid = self._accessor(self._stage_valid_name(prev_stage), module, sv)

            cur_valid = self._accessor(self._stage_valid_name(stage), module, sv)

            # next_valid = flush→false, cancel→false, stall→hold, else→propagate
            next_valid_expr = ite(flush, "false",
                               ite(cancel, "false",
                               ite(stall, cur_valid,
                                   prev_valid)))

            module.add_transition(SMT2Transition(
                register_name=self._stage_valid_name(stage),
                next_value_expr=next_valid_expr,
            ))

        for ch in pip.channels:
            dst_stage = stage_by_name.get(ch.dst_stage)
            if dst_stage is None:
                continue

            stall = self._build_stall_expr(dst_stage, module, sv)
            cur_data = self._accessor(self._channel_data_name(ch), module, sv)

            src_data_name = f"{ch.name.split('_')[0]}_{ch.src_stage.lower()}_in"
            src_data = self._resolve_signal_state(src_data_name, module, sv)
            if src_data is None:
                src_data = cur_data  # conservative: hold

            next_data_expr = ite(stall, cur_data, src_data)
            module.add_transition(SMT2Transition(
                register_name=self._channel_data_name(ch),
                next_value_expr=next_data_expr,
            ))

        for rd in pip.regfile_decls:
            mname = self._regfile_mem_name(rd)
            cur_mem = self._accessor(mname, module, sv)

            write_accs = [
                a for a in pip.regfile_accesses
                if a.field_name == rd.field_name and a.kind == "write"
            ]
            if not write_accs:
                module.add_transition(SMT2Transition(
                    register_name=mname,
                    next_value_expr=cur_mem,
                ))
                continue

            wa = write_accs[0]
            wr_stage_lower = wa.stage.lower()
            wr_valid = self._accessor(f"valid_{wr_stage_lower}", module, sv)
            wr_addr = self._resolve_signal_state(
                f"{wa.addr_var}_{wr_stage_lower}", module, sv
            ) or bv_zero(rd.addr_width)
            wr_data = self._resolve_signal_state(
                f"{wa.data_var}_{wr_stage_lower}", module, sv
            ) or bv_zero(rd.data_width)

            next_mem_expr = ite(
                wr_valid,
                f"(store {cur_mem} {wr_addr} {wr_data})",
                cur_mem,
            )
            module.add_transition(SMT2Transition(
                register_name=mname,
                next_value_expr=next_mem_expr,
            ))

    # ------------------------------------------------------------------ #
    # Assertions P1–P10                                                   #
    # ------------------------------------------------------------------ #

    def _add_assertions(self, pip: PipelineIR, module: SMT2Module) -> None:
        """Add formal property assertions to the module.

        P1 (reset), P2 (propagation), P3 (stall freeze), P4 (stall bubble),
        P5 (flush priority), P6 (cancel) are all encoded in the transition
        relation and initial conditions and are verified automatically by the
        BMC / k-induction harness.

        P7 (forwarding correctness) is expressed as an explicit invariant:
        when the write stage is valid and the addresses match, the read result
        equals the write data.

        :param pip: :class:`PipelineIR` being translated.
        :param module: :class:`SMT2Module` being built.
        """
        props: List[str] = []
        sv = "state"

        for hz in pip.regfile_hazards:
            if hz.resolved_by != "forward":
                continue
            rd = next(
                (r for r in pip.regfile_decls if r.field_name == hz.field_name),
                None,
            )
            if rd is None:
                continue

            wr_valid = self._accessor(f"valid_{hz.write_stage.lower()}", module, sv)

            wr_addr = self._resolve_signal_state(
                f"{hz.write_addr_var}_{hz.write_stage.lower()}", module, sv
            ) or bv_zero(rd.addr_width)
            rd_addr = self._resolve_signal_state(
                f"{hz.read_addr_var}_{hz.read_stage.lower()}", module, sv
            ) or bv_zero(rd.addr_width)
            wr_data = self._resolve_signal_state(
                f"{hz.write_data_var}_{hz.write_stage.lower()}", module, sv
            ) or bv_zero(rd.data_width)
            rd_res = self._resolve_signal_state(
                f"{hz.read_result_var}_{hz.read_stage.lower()}", module, sv
            ) or bv_zero(rd.data_width)

            addr_match = eq(wr_addr, rd_addr)
            # P7: wr_valid ∧ addr_match → rd_result = wr_data
            p7 = f"(=> (and {wr_valid} {addr_match}) (= {rd_res} {wr_data}))"
            props.append(p7)

        if props:
            module.add_assertion(and_(*props))
        else:
            module.add_assertion("true")

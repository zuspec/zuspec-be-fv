"""SMT-LIBv2 problem generation for k-induction.

This is solver-independent: it only emits SMT-LIBv2 and does not require the
Python Z3 bindings.
"""

from __future__ import annotations

from pathlib import Path

from ..rtl import RTLToSMT2Translator
from ..rtl.smt2_module import SMT2Module


def generate_k_induction_step_smt2(
    translator: RTLToSMT2Translator,
    module: SMT2Module,
    *,
    k: int,
    get_model: bool = True,
) -> str:
    """Generate SMT2 for the inductive step.

    UNSAT means the inductive step holds (i.e. no counterexample to induction).
    SAT means induction fails (not necessarily that the property is false).
    """
    lines: list[str] = []

    lines.append(f"; k-induction inductive step for {module.name} k={k}")
    lines.append("(set-logic QF_UFBV)")
    lines.append("")

    lines.append(translator.generate_smt2(module))
    lines.append("")

    # states 0..k+1
    for i in range(k + 2):
        lines.append(f"(declare-const state_{i} |{module.state_sort}|)")

    for i in range(k + 2):
        lines.append(f"(assert (|{module.name}_is| state_{i}))")
        lines.append(f"(assert (|{module.name}_u| state_{i}))")
        lines.append(f"(assert (|{module.name}_h| state_{i}))")

    # transitions 0..k -> 1..k+1
    for i in range(k + 1):
        lines.append(f"(assert (|{module.name}_t| state_{i} state_{i+1}))")

    # assume property holds for 0..k
    for i in range(k + 1):
        lines.append(f"(assert (|{module.name}_a| state_{i}))")

    # try to violate at k+1
    lines.append(f"(assert (not (|{module.name}_a| state_{k+1})))")

    lines.append("(check-sat)")
    if get_model:
        lines.append("(get-model)")

    return "\n".join(lines)


def write_k_induction_step_smt2(
    translator: RTLToSMT2Translator,
    module: SMT2Module,
    out_file: str | Path,
    *,
    k: int,
    get_model: bool = True,
) -> Path:
    out_path = Path(out_file)
    out_path.write_text(generate_k_induction_step_smt2(translator, module, k=k, get_model=get_model))
    return out_path

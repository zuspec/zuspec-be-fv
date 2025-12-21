"""SMT-LIBv2 problem generation for bounded model checking (BMC).

This is solver-independent: it only emits SMT-LIBv2 and does not require the
Python Z3 bindings.

The generated problem is SAT iff an assertion can be violated.
"""

from __future__ import annotations

from pathlib import Path

from ..rtl import RTLToSMT2Translator
from ..rtl.smt2_module import SMT2Module


def generate_bmc_smt2(
    translator: RTLToSMT2Translator,
    module: SMT2Module,
    *,
    depth: int,
    check_all_steps: bool = True,
    get_model: bool = True,
) -> str:
    lines: list[str] = []

    lines.append(f"; BMC problem for {module.name} depth={depth}")
    lines.append("(set-logic QF_UFBV)")
    lines.append("")

    # Module declarations/definitions (sorts, signals, predicates)
    lines.append(translator.generate_smt2(module))
    lines.append("")

    # Declare state instances
    for k in range(depth + 1):
        lines.append(f"(declare-const state_{k} |{module.state_sort}|)")
    lines.append("")

    # Constrain states to be well-formed (if downstream tools define _is)
    for k in range(depth + 1):
        lines.append(f"(assert (|{module.name}_is| state_{k}))")

    # Initial state
    lines.append(f"(assert (|{module.name}_i| state_0))")

    # Assumptions / hierarchy predicates at each step
    for k in range(depth + 1):
        lines.append(f"(assert (|{module.name}_u| state_{k}))")
        lines.append(f"(assert (|{module.name}_h| state_{k}))")

    # Transitions
    for k in range(depth):
        lines.append(f"(assert (|{module.name}_t| state_{k} state_{k+1}))")

    lines.append("")

    # Property violation check
    if check_all_steps:
        disj = " ".join([f"(not (|{module.name}_a| state_{k}))" for k in range(depth + 1)])
        lines.append(f"(assert (or {disj}))")
    else:
        lines.append(f"(assert (not (|{module.name}_a| state_{depth})))")

    lines.append("(check-sat)")
    if get_model:
        lines.append("(get-model)")

    return "\n".join(lines)


def write_bmc_smt2(
    translator: RTLToSMT2Translator,
    module: SMT2Module,
    out_file: str | Path,
    *,
    depth: int,
    check_all_steps: bool = True,
    get_model: bool = True,
) -> Path:
    out_path = Path(out_file)
    out_path.write_text(
        generate_bmc_smt2(
            translator,
            module,
            depth=depth,
            check_all_steps=check_all_steps,
            get_model=get_model,
        )
    )
    return out_path

"""SMT-LIBv2 problem generation for cover goals.

The generated problem is SAT iff a coverage goal can be reached within the bound.
"""

from __future__ import annotations

from pathlib import Path

from ..rtl import RTLToSMT2Translator
from ..rtl.smt2_module import SMT2Module


def generate_cover_smt2(
    translator: RTLToSMT2Translator,
    module: SMT2Module,
    *,
    depth: int,
    check_all_steps: bool = True,
    get_model: bool = True,
) -> str:
    lines: list[str] = []

    lines.append(f"; COVER problem for {module.name} depth={depth}")
    lines.append("(set-logic QF_UFBV)")
    lines.append("")

    lines.append(translator.generate_smt2(module))
    lines.append("")

    for k in range(depth + 1):
        lines.append(f"(declare-const state_{k} |{module.state_sort}|)")
    lines.append("")

    for k in range(depth + 1):
        lines.append(f"(assert (|{module.name}_is| state_{k}))")

    lines.append(f"(assert (|{module.name}_i| state_0))")

    for k in range(depth + 1):
        lines.append(f"(assert (|{module.name}_u| state_{k}))")
        lines.append(f"(assert (|{module.name}_h| state_{k}))")

    for k in range(depth):
        lines.append(f"(assert (|{module.name}_t| state_{k} state_{k+1}))")

    lines.append("")

    # Coverage check via module predicate _c (OR of cover goals)
    if check_all_steps:
        disj = " ".join([f"(|{module.name}_c| state_{k})" for k in range(depth + 1)])
        lines.append(f"(assert (or {disj}))")
    else:
        lines.append(f"(assert (|{module.name}_c| state_{depth}))")

    lines.append("(check-sat)")
    if get_model:
        lines.append("(get-model)")

    return "\n".join(lines)


def write_cover_smt2(
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
        generate_cover_smt2(
            translator,
            module,
            depth=depth,
            check_all_steps=check_all_steps,
            get_model=get_model,
        )
    )
    return out_path

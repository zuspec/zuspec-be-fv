"""Counterexample trace representation and parsing helpers."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Dict, List, Optional


@dataclass
class CounterexampleTrace:
    """A counterexample trace showing a property violation."""

    depth: int
    states: List[Dict[str, Any]]
    violation_time: int

    def format_trace(self) -> str:
        lines: List[str] = []
        lines.append(f"Counterexample trace (length {self.depth}):")
        lines.append("")
        for k, st in enumerate(self.states):
            lines.append(f"Time {k}:")
            for sig, val in sorted(st.items()):
                lines.append(f"  {sig} = {val}")
            lines.append("")
        lines.append(f"Property violated at time {self.violation_time}")
        return "\n".join(lines)


def parse_get_value_output(stdout: str) -> Dict[str, Any]:
    """Best-effort parse of SMT-LIB `(get-value ...)` output.

    We support the common case where solvers print lines like:
        ((term value))

    Values are returned as strings unless they look like booleans or bitvector/int numerals.
    """
    import re

    out: Dict[str, Any] = {}

    # Match: ((<term> <value>)) possibly with whitespace/newlines.
    # This is intentionally simple/robust rather than a full S-expression parser.
    for m in re.finditer(r"\(\(\s*(?P<term>[^\s\)]+)\s+(?P<val>[^\)]+)\)\)", stdout):
        term = m.group("term")
        val_s = m.group("val").strip()

        if val_s == "true":
            val: Any = True
        elif val_s == "false":
            val = False
        else:
            # Try BV literal: #b... / #x...
            if val_s.startswith("#b"):
                try:
                    val = int(val_s[2:], 2)
                except Exception:
                    val = val_s
            elif val_s.startswith("#x"):
                try:
                    val = int(val_s[2:], 16)
                except Exception:
                    val = val_s
            elif re.fullmatch(r"-?\d+", val_s):
                try:
                    val = int(val_s)
                except Exception:
                    val = val_s
            else:
                val = val_s

        out[term] = val

    return out

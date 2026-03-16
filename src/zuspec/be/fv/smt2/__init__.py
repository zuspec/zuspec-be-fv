"""SMT-LIB2 utilities for zuspec-be-fv.

Sub-modules:

* :mod:`~zuspec.be.fv.smt2.bitvec_ops` — pure string-level bitvector helpers
  shared by both the RTL → SMT-LIB2 translator and the rand emitter.
* :mod:`~zuspec.be.fv.smt2.rand_emitter` — ``RandSMT2Emitter``: translates a
  ``@zdc.dataclass`` to a QF_BV satisfiability query for constrained
  randomization.
"""

from .rand_emitter import RandSMT2Emitter, parse_get_value

__all__ = ["RandSMT2Emitter", "parse_get_value"]

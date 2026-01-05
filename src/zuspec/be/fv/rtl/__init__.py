"""
RTL to SMT2 translation module.

This module provides classes and functions for translating Zuspec RTL descriptions
(components with input/output/comb/sync) to SMT2 format for formal verification.
"""

from .smt2_module import SMT2Module, SMT2Signal, SMT2Function, SMT2Transition
from .rtl_to_smt2 import RTLToSMT2Translator
from .translation_context import TranslationContext
from .expr_translator import ExprToSMT2Translator
from .stmt_translator import StmtToSMT2Translator

__all__ = [
    'SMT2Module',
    'SMT2Signal', 
    'SMT2Function',
    'SMT2Transition',
    'RTLToSMT2Translator',
    'TranslationContext',
    'ExprToSMT2Translator',
    'StmtToSMT2Translator',
]

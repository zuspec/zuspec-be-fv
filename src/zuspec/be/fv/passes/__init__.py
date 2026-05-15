# Copyright 2019-2026 Matthew Ballance and contributors
# SPDX-License-Identifier: Apache-2.0
"""Formal verification passes for Zuspec components."""
from .counter_formal import CounterFormalPass, CounterProperty

__all__ = ["CounterFormalPass", "CounterProperty"]

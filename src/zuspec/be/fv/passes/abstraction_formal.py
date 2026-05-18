"""AbstractionFormalPass — interface-dispatch formal verification pass.

For each :class:`~zuspec.ir.core.abstraction_field_ir.AbstractionFieldIR` in a
component's field list this pass:

1. Looks up the registered ``SVAEmittableInterface`` model via
   :func:`~zuspec.ir.core.registry.global_registry`.
2. Calls ``model.sva_assert_properties()`` or ``model.sva_assume_properties()``
   depending on the mode.
3. Accumulates ``model.bmc_depth()`` across all fields to compute the minimum
   required BMC depth.

Usage::

    from zuspec.be.fv.passes.abstraction_formal import AbstractionFormalPass

    fv = AbstractionFormalPass(Blinker, mode='assert')
    for prop in fv.all_properties():
        print(prop)
    print("min BMC depth:", fv.min_required_depth())
"""
from __future__ import annotations

import logging
from typing import List, Optional

_log = logging.getLogger(__name__)


class AbstractionFormalPass:
    """Formal verification property extractor using interface-dispatch.

    Parameters
    ----------
    component_cls:
        A ``zdc.Component`` Python class (decorated with ``@zdc.dataclass``).
    mode:
        ``'assert'`` — collect ``sva_assert_properties()`` for DUT checking.
        ``'assume'`` — collect ``sva_assume_properties()`` for cutpoint constraining.
    model_context:
        Optional pre-built ``DataModel`` context from ``DataModelFactory``.
        When ``None``, the pass builds its own.
    """

    def __init__(
        self,
        component_cls,
        mode: str = "assert",
        model_context=None,
    ):
        if mode not in ("assert", "assume"):
            raise ValueError(f"mode must be 'assert' or 'assume', got {mode!r}")
        self._cls = component_cls
        self._mode = mode
        self._ctx = model_context
        self._properties: List[str] = []
        self._depths: List[int] = []
        self._analyze()

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def all_properties(self) -> List[str]:
        """Return all SVA property strings collected from abstraction fields."""
        return list(self._properties)

    def min_required_depth(self) -> int:
        """Return the maximum BMC depth across all abstraction fields.

        Returns ``0`` if no abstraction fields are present.
        """
        return max(self._depths, default=0)

    # ------------------------------------------------------------------
    # Analysis
    # ------------------------------------------------------------------

    def _analyze(self):
        """Walk the component IR and collect properties from abstraction fields."""
        try:
            from zuspec.ir.core.abstraction_field_ir import AbstractionFieldIR
            from zuspec.ir.core.registry import global_registry
        except ImportError:
            _log.debug("AbstractionFormalPass: zuspec-ir-core not available; skipping")
            return

        ctx = self._ctx
        if ctx is None:
            ctx = self._build_context()
        if ctx is None:
            return

        comp_ir = self._get_component_ir(ctx)
        if comp_ir is None:
            _log.warning(
                "AbstractionFormalPass: could not find IR for %r",
                self._cls.__name__,
            )
            return

        registry = global_registry()

        for field in getattr(comp_ir, "fields", []):
            if not isinstance(field, AbstractionFieldIR):
                continue

            model = registry.get_fv_model(field.spec_type_name)
            if model is None:
                _log.warning(
                    "AbstractionFormalPass: no FV model for %r; skipping",
                    field.spec_type_name,
                )
                continue

            if self._mode == "assert":
                props = model.sva_assert_properties(field)
            else:
                props = model.sva_assume_properties(field)

            self._properties.extend(props)
            self._depths.append(model.bmc_depth(field))

    def _build_context(self):
        """Build a ``DataModel`` context for the component class."""
        try:
            from zuspec.dataclasses.data_model_factory import DataModelFactory
            return DataModelFactory().build(self._cls)
        except Exception as exc:
            _log.warning("AbstractionFormalPass: could not build context: %s", exc)
            return None

    def _get_component_ir(self, ctx):
        """Return the component IR from *ctx* or ``None``."""
        qualname = getattr(self._cls, "__qualname__", None)
        ir = (
            (ctx.type_m.get(qualname) if qualname else None)
            or ctx.type_m.get(self._cls.__name__)
        )
        return ir

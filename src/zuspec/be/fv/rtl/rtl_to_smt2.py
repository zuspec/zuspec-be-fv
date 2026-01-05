"""
RTL to SMT2 Translator.

Translates Zuspec components with RTL descriptions (input/output/comb/sync)
to SMT2 format for formal verification.
"""

from typing import Optional, List, Dict, Any, Set
import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')

try:
    from zuspec.dataclasses import ir
except ImportError:
    ir = None

from .smt2_module import SMT2Module, SMT2Signal, SMT2Function, SMT2Transition
from .translation_context import TranslationContext
from .expr_translator import ExprToSMT2Translator
from .stmt_translator import StmtToSMT2Translator


class RTLToSMT2Translator:
    """Translates Zuspec RTL descriptions to SMT2 format.
    
    This is the main entry point for RTL-to-SMT2 translation. It processes
    a Zuspec component and generates a complete SMT2 module with state machine
    semantics.
    
    The translation follows these steps:
    1. Process fields to identify inputs, outputs, and registers
    2. Translate combinational processes to SMT2 functions
    3. Translate synchronous processes to transition relations
    4. Extract formal properties (assertions, assumptions, coverage)
    5. Generate SMT2 output text
    """
    
    def __init__(self):
        """Initialize the translator with expression and statement translators."""
        self.expr_translator = ExprToSMT2Translator()
        self.stmt_translator = StmtToSMT2Translator(self.expr_translator)
        self.signal_counter = 0  # For generating unique SMT2 signal names
    
    def translate_component(self, comp: Any) -> SMT2Module:
        """Translate a Zuspec component to SMT2 module.
        
        Args:
            comp: DataTypeComponent from Zuspec dataclasses
            
        Returns:
            SMT2Module with complete state machine
            
        Raises:
            TypeError: If comp is not a DataTypeComponent
            ImportError: If zuspec.dataclasses not available
        """
        if ir is None:
            raise ImportError("zuspec.dataclasses not available")
        
        if not isinstance(comp, ir.DataTypeComponent):
            raise TypeError(f"Expected DataTypeComponent, got {type(comp)}")
        
        # Create module
        module = SMT2Module(name=comp.name or "top")

        field_map: Dict[int, str] = {}

        # Step 1: Process fields (inputs/outputs/wires) and build field map
        for idx, field in enumerate(comp.fields):
            smt_name = self._translate_field(field, module)
            field_map[idx] = smt_name

        # Base context (used for initial values and properties)
        base_ctx = TranslationContext(component=comp, module=module, field_map=field_map)

        # Extract initial values from fields
        for idx, field in enumerate(comp.fields):
            if getattr(field, 'initial_value', None) is not None:
                init_smt = self.expr_translator.translate(field.initial_value, base_ctx)
                sig = module.get_all_signals().get(field.name)
                if sig is not None:
                    sig.initial_value = init_smt

        # Step 2: Process combinational logic
        for func in comp.comb_processes:
            self._translate_comb_process(func, module, base_ctx)

        # Step 3: Process synchronous logic
        for func in comp.sync_processes:
            self._translate_sync_process(func, module, base_ctx)

        # Step 4: Extract formal properties
        self._extract_properties(comp, module, base_ctx)

        return module
    
    def _translate_field(self, field: Any, module: SMT2Module) -> str:
        """Translate a field to SMT2 signal and return the SMT name."""
        sig_name = field.name
        smt_name = self._generate_smt_name(sig_name)

        width, is_signed = self._get_type_info(field.datatype)

        signal = SMT2Signal(
            name=sig_name,
            smt_name=smt_name,
            datatype=field.datatype,
            direction=field.direction if hasattr(field, 'direction') else None,
            width=width,
            is_signed=is_signed,
            initial_value=None,
            is_register=False,
        )

        if field.direction == ir.SignalDirection.INPUT:
            module.add_input(signal)
        elif field.direction == ir.SignalDirection.OUTPUT:
            module.add_output(signal)
        elif field.direction == ir.SignalDirection.INOUT:
            module.add_input(signal)
            module.add_output(signal)
        else:
            module.add_wire(signal)

        return smt_name

    def _collect_field_ref_indices(self, expr: Any) -> Set[int]:
        """Collect self.field indices referenced by an expression."""
        if ir is None:
            return set()

        refs: Set[int] = set()

        def walk(e: Any):
            if e is None:
                return
            if isinstance(e, ir.ExprRefField) and isinstance(e.base, ir.TypeExprRefSelf):
                refs.add(e.index)
                return
            if isinstance(e, ir.ExprBin):
                walk(e.lhs)
                walk(e.rhs)
            elif isinstance(e, ir.ExprUnary):
                walk(e.operand)
            elif isinstance(e, ir.ExprCompare):
                walk(e.left)
                for c in e.comparators:
                    walk(c)
            elif isinstance(e, ir.ExprBool):
                for v in e.values:
                    walk(v)

        walk(expr)
        return refs
    
    def _translate_comb_process(self, func: Any, module: SMT2Module, base_ctx: TranslationContext):
        """Translate combinational process.

        Supported forms:
        - Single return statement: creates an SMT2 function
        - Single assignment to a field: creates a combinational definition for that signal
        """
        func_name = func.name
        smt_name = f"{module.name}_{func_name}"

        ctx = TranslationContext(
            component=base_ctx.component,
            module=module,
            field_map=base_ctx.field_map,
            local_vars={},
            param_map=dict(base_ctx.param_map),
            type_cache=base_ctx.type_cache,
            state_var="state",
        )

        body_expr = None
        return_type = "Bool"

        if func.returns is not None:
            if isinstance(func.returns, ir.DataTypeInt) and func.returns.bits != 1:
                return_type = f"(_ BitVec {func.returns.bits if func.returns.bits > 0 else 32})"
            else:
                return_type = "Bool" if isinstance(func.returns, ir.DataTypeInt) and func.returns.bits == 1 else return_type

        if len(func.body) == 1 and isinstance(func.body[0], ir.StmtReturn):
            ret = func.body[0]
            body_expr = self.expr_translator.translate(ret.value, ctx) if ret.value is not None else "true"

            smt_func = SMT2Function(
                name=func_name,
                smt_name=smt_name,
                params=[("state", module.state_sort)],
                return_type=return_type,
                body=body_expr,
            )
            module.add_comb_function(smt_func)

        elif len(func.body) == 1 and isinstance(func.body[0], ir.StmtAssign):
            assign = func.body[0]
            if len(assign.targets) != 1 or not isinstance(assign.targets[0], ir.ExprRefField):
                raise ValueError("Combinational assignment must be to a single field")

            target = assign.targets[0]
            if not isinstance(target.base, ir.TypeExprRefSelf):
                raise NotImplementedError("Hierarchical comb assignments not supported")

            body_expr = self.expr_translator.translate(assign.value, ctx)

            # Record as a combinational definition for the target signal
            field_name = base_ctx.component.fields[target.index].name
            sig = module.outputs.get(field_name) or module.wires.get(field_name)
            if sig is None:
                raise ValueError(f"Unknown comb assignment target: {field_name}")
            if sig.is_register or field_name in module.registers:
                raise ValueError(f"Signal {field_name} is driven by both comb and sync")

            sig.def_expr = body_expr
            sig.def_deps = [base_ctx.field_map[i] for i in self._collect_field_ref_indices(assign.value) if i in base_ctx.field_map]

        else:
            raise NotImplementedError("Combinational functions must have a single return or assignment")
    
    def _translate_sync_process(self, func: Any, module: SMT2Module, base_ctx: TranslationContext):
        """Translate synchronous process to transitions."""
        ctx = TranslationContext(
            component=base_ctx.component,
            module=module,
            field_map=base_ctx.field_map,
            local_vars={},
            param_map=dict(base_ctx.param_map),
            type_cache=base_ctx.type_cache,
            state_var="state",
            next_state_var="next_state",
        )

        transitions = self.stmt_translator.translate_sync_body(func.body, ctx)

        rev_field_map = {v: k for k, v in base_ctx.field_map.items()}
        for t in transitions:
            module.add_transition(t)

            # Mark destination as a register
            field_idx = rev_field_map.get(t.register_name)
            if field_idx is not None:
                field_name = base_ctx.component.fields[field_idx].name
                sig = module.outputs.get(field_name) or module.wires.get(field_name)
                if sig is not None:
                    if sig.def_expr is not None:
                        raise ValueError(f"Signal {field_name} is driven by both comb and sync")
                    module.add_register(sig)
    
    def _extract_properties(self, comp: Any, module: SMT2Module, base_ctx: TranslationContext):
        """Extract assertions/assumptions/cover statements and invariants."""

        def visit_stmt(stmt: Any, ctx: TranslationContext, guard: str = "true"):
            if isinstance(stmt, ir.StmtAssert):
                a = self.expr_translator.translate(stmt.test, ctx)
                module.add_assertion(a if guard == "true" else f"(=> {guard} {a})")
            elif isinstance(stmt, ir.StmtAssume):
                u = self.expr_translator.translate(stmt.test, ctx)
                module.add_assumption(u if guard == "true" else f"(=> {guard} {u})")
            elif isinstance(stmt, ir.StmtCover):
                c = self.expr_translator.translate(stmt.test, ctx)
                module.add_coverage_goal(c if guard == "true" else f"(=> {guard} {c})")
            elif isinstance(stmt, ir.StmtIf):
                cond = self.expr_translator.translate(stmt.test, ctx)
                then_guard = cond if guard == "true" else f"(and {guard} {cond})"
                else_guard = f"(not {cond})" if guard == "true" else f"(and {guard} (not {cond}))"
                for s in stmt.body:
                    visit_stmt(s, ctx, then_guard)
                for s in stmt.orelse:
                    visit_stmt(s, ctx, else_guard)

            elif isinstance(stmt, (ir.StmtFor, ir.StmtWhile)):
                for s in stmt.body:
                    visit_stmt(s, ctx, guard)
                for s in stmt.orelse:
                    visit_stmt(s, ctx, guard)

            elif isinstance(stmt, ir.StmtTry):
                for s in stmt.body:
                    visit_stmt(s, ctx, guard)
                for h in stmt.handlers:
                    for s in h.body:
                        visit_stmt(s, ctx, guard)
                for s in stmt.orelse:
                    visit_stmt(s, ctx, guard)
                for s in stmt.finalbody:
                    visit_stmt(s, ctx, guard)

            elif isinstance(stmt, ir.StmtWith):
                for s in stmt.body:
                    visit_stmt(s, ctx, guard)

            elif hasattr(stmt, 'body') and isinstance(getattr(stmt, 'body'), list):
                for s in stmt.body:
                    visit_stmt(s, ctx, guard)

            else:
                return

        # Invariant functions
        for func in getattr(comp, 'functions', []):
            if getattr(func, 'is_invariant', False):
                if len(func.body) == 1 and isinstance(func.body[0], ir.StmtReturn) and func.body[0].value is not None:
                    inv = self.expr_translator.translate(func.body[0].value, base_ctx)
                    module.add_assertion(inv)

        # Formal statements in all function bodies
        for func in (getattr(comp, 'functions', []) + getattr(comp, 'sync_processes', []) + getattr(comp, 'comb_processes', [])):
            for stmt in getattr(func, 'body', []):
                visit_stmt(stmt, base_ctx, "true")
    
    def _generate_smt_name(self, name: str) -> str:
        """Generate unique SMT2 identifier.
        
        Args:
            name: Original name
            
        Returns:
            SMT2-safe identifier
        """
        # SMT2 identifiers can contain letters, digits, and some symbols
        # Escape special characters
        safe_name = name.replace(".", "_").replace("[", "_").replace("]", "_")
        self.signal_counter += 1
        return f"{safe_name}#{self.signal_counter}"
    
    def _get_type_info(self, datatype: Any) -> tuple[int, bool]:
        """Get bit width and signedness from datatype.
        
        Args:
            datatype: Zuspec DataType
            
        Returns:
            Tuple of (width, is_signed)
        """
        if isinstance(datatype, ir.DataTypeInt):
            width = datatype.bits if datatype.bits > 0 else 32
            is_signed = datatype.signed
            return (width, is_signed)
        else:
            # Default for non-integer types
            return (1, False)
    
    def generate_smt2(self, module: SMT2Module) -> str:
        """Generate SMT2 text output from module.
        
        Args:
            module: SMT2Module to convert
            
        Returns:
            SMT2-LIBv2 formatted text
        """
        lines = []
        
        # Header comment
        lines.append(f"; SMT-LIBv2 description generated by zuspec-be-fv")
        lines.append(f"; zuspec-smt2-module {module.name}")
        
        # 1. Declare state sort
        lines.append(f"(declare-sort |{module.state_sort}| 0)")
        lines.append(f"(declare-fun |{module.name}_is| (|{module.state_sort}|) Bool)")
        
        # 2. Declare input signals
        for sig in module.inputs.values():
            lines.extend(self._declare_signal(sig, module))

        # 3. Declare registers
        for sig in module.registers.values():
            lines.extend(self._declare_signal(sig, module))

        # 4. Declare unconstrained outputs (not registers, not comb-defined)
        for sig in module.outputs.values():
            if sig.name in module.inputs or sig.name in module.registers:
                continue
            if sig.def_expr is None:
                lines.extend(self._declare_signal(sig, module))

        # 5. Declare unconstrained internal wires (not comb-defined)
        for sig in module.wires.values():
            if sig.name in module.registers or sig.name in module.inputs or sig.name in module.outputs:
                continue
            if sig.def_expr is None:
                lines.extend(self._declare_signal(sig, module))

        # 6. Define combinationally-driven signals (wires/outputs)
        for sig in self._toposort_defined_signals(module):
            lines.extend(self._define_signal(sig, module))

        # 7. Define combinational functions
        for func in module.comb_logic:
            lines.extend(self._define_function(func, module))
        
        # 8. Define state machine predicates
        lines.extend(self._generate_assertion_predicate(module))
        lines.extend(self._generate_assumption_predicate(module))
        lines.extend(self._generate_coverage_predicate(module))
        lines.extend(self._generate_initial_predicate(module))
        lines.extend(self._generate_hierarchy_predicate(module))
        lines.extend(self._generate_transition_predicate(module))
        
        lines.append(f"; end of module {module.name}")
        lines.append(f"; zuspec-smt2-topmod {module.name}")
        lines.append("; end of zuspec output")
        
        return "\n".join(lines)
    
    def _signal_smt_type(self, sig: SMT2Signal) -> str:
        if sig.width == 1 and not sig.is_signed:
            return "Bool"
        return f"(_ BitVec {sig.width})"

    def _declare_signal(self, sig: SMT2Signal, module: SMT2Module) -> List[str]:
        """Generate SMT2 declaration for a signal."""
        lines = []

        smt_type = self._signal_smt_type(sig)
        
        # Declare function from state to signal value
        lines.append(f"(declare-fun |{module.name}#{sig.smt_name}| (|{module.state_sort}|) {smt_type}) ; {sig.name}")
        
        # Add metadata comments
        if sig.direction == ir.SignalDirection.INPUT:
            lines.append(f"; zuspec-smt2-input {sig.name} {sig.width}")
        elif sig.direction == ir.SignalDirection.OUTPUT:
            lines.append(f"; zuspec-smt2-output {sig.name} {sig.width}")
        
        if sig.is_register:
            lines.append(f"; zuspec-smt2-register {sig.name} {sig.width}")
        
        lines.append(f"; zuspec-smt2-wire {sig.name} {sig.width}")
        
        return lines
    
    def _define_signal(self, sig: SMT2Signal, module: SMT2Module) -> List[str]:
        """Generate SMT2 definition for a combinationally-driven signal."""
        if sig.def_expr is None:
            return []
        if sig.is_register:
            raise ValueError(f"Cannot define register signal {sig.name} as combinational")

        lines: List[str] = []
        smt_type = self._signal_smt_type(sig)

        lines.append(f"(define-fun |{module.name}#{sig.smt_name}| ((state |{module.state_sort}|)) {smt_type}")
        lines.append(f"  {sig.def_expr}")
        lines.append(")")

        if sig.direction == ir.SignalDirection.OUTPUT:
            lines.append(f"; zuspec-smt2-output {sig.name} {sig.width}")
        lines.append(f"; zuspec-smt2-wire {sig.name} {sig.width}")
        return lines

    def _toposort_defined_signals(self, module: SMT2Module) -> List[SMT2Signal]:
        """Toposort defined comb signals to avoid forward references."""
        defined: Dict[str, SMT2Signal] = {}

        for sig in list(module.outputs.values()) + list(module.wires.values()):
            if sig.def_expr is not None and not sig.is_register and sig.name not in module.inputs and sig.name not in module.registers:
                defined[sig.smt_name] = sig

        # Build graph among defined signals only
        deps: Dict[str, Set[str]] = {}
        indeg: Dict[str, int] = {k: 0 for k in defined.keys()}

        for name, sig in defined.items():
            dset = set([d for d in getattr(sig, 'def_deps', []) if d in defined])
            deps[name] = dset
            indeg[name] = len(dset)

        ready = [k for k, v in indeg.items() if v == 0]
        ordered: List[SMT2Signal] = []

        while ready:
            n = ready.pop()
            ordered.append(defined[n])
            for m, mdeps in deps.items():
                if n in mdeps:
                    mdeps.remove(n)
                    indeg[m] -= 1
                    if indeg[m] == 0:
                        ready.append(m)

        if len(ordered) != len(defined):
            raise ValueError("Combinational definition cycle detected")

        return ordered

    def _define_function(self, func: SMT2Function, module: SMT2Module) -> List[str]:
        """Generate SMT2 function definition.
        
        Args:
            func: Function to define
            module: Parent module
            
        Returns:
            List of SMT2 definition lines
        """
        lines = []
        
        # Build parameter list
        params_str = " ".join([f"({name} |{ptype}|)" for name, ptype in func.params])
        
        # Define function
        lines.append(f"(define-fun |{func.smt_name}| ({params_str}) {func.return_type}")
        lines.append(f"  {func.body}")
        lines.append(")")
        
        return lines
    
    def _generate_assertion_predicate(self, module: SMT2Module) -> List[str]:
        """Generate assertion predicate (properties that must hold).
        
        Args:
            module: Module with assertions
            
        Returns:
            List of SMT2 lines defining assertion predicate
        """
        lines = []
        
        if not module.assertions:
            expr = "true"
        elif len(module.assertions) == 1:
            expr = module.assertions[0]
        else:
            assertions_str = " ".join(module.assertions)
            expr = f"(and {assertions_str})"
        
        lines.append(f"(define-fun |{module.name}_a| ((state |{module.state_sort}|)) Bool")
        lines.append(f"  {expr}")
        lines.append(")")
        
        return lines
    
    def _generate_assumption_predicate(self, module: SMT2Module) -> List[str]:
        """Generate assumption predicate (constraints on inputs).
        
        Args:
            module: Module with assumptions
            
        Returns:
            List of SMT2 lines defining assumption predicate
        """
        lines = []
        
        if not module.assumptions:
            expr = "true"
        elif len(module.assumptions) == 1:
            expr = module.assumptions[0]
        else:
            assumptions_str = " ".join(module.assumptions)
            expr = f"(and {assumptions_str})"
        
        lines.append(f"(define-fun |{module.name}_u| ((state |{module.state_sort}|)) Bool")
        lines.append(f"  {expr}")
        lines.append(")")
        
        return lines
    
    def _generate_coverage_predicate(self, module: SMT2Module) -> List[str]:
        """Generate coverage predicate (coverage goals).

        Note: This is not used by BMC/proving directly, but provides a standard
        place to emit cover goals for downstream tooling.
        """
        lines: List[str] = []

        if not module.coverage_goals:
            expr = "true"
        elif len(module.coverage_goals) == 1:
            expr = module.coverage_goals[0]
        else:
            expr = f"(or {' '.join(module.coverage_goals)})"

        lines.append(f"(define-fun |{module.name}_c| ((state |{module.state_sort}|)) Bool")
        lines.append(f"  {expr}")
        lines.append(")")

        return lines

    def _generate_initial_predicate(self, module: SMT2Module) -> List[str]:
        """Generate initial state predicate.
        
        Args:
            module: Module with initial conditions
            
        Returns:
            List of SMT2 lines defining initial predicate
        """
        lines = []
        
        # Combine initial conditions from signals and explicit conditions
        all_initial = []
        
        # Add register initial values
        for sig in module.registers.values():
            if sig.initial_value:
                all_initial.append(f"(= (|{module.name}#{sig.smt_name}| state) {sig.initial_value})")
        
        # Add explicit initial conditions
        all_initial.extend(module.initial_conditions)
        
        if not all_initial:
            expr = "true"
        elif len(all_initial) == 1:
            expr = all_initial[0]
        else:
            initial_str = " ".join(all_initial)
            expr = f"(and {initial_str})"
        
        lines.append(f"(define-fun |{module.name}_i| ((state |{module.state_sort}|)) Bool")
        lines.append(f"  {expr}")
        lines.append(")")
        
        return lines
    
    def _generate_hierarchy_predicate(self, module: SMT2Module) -> List[str]:
        """Generate hierarchy predicate (for hierarchical designs).
        
        Args:
            module: Module
            
        Returns:
            List of SMT2 lines defining hierarchy predicate
        """
        lines = []
        
        # For now, just return true (no hierarchy)
        lines.append(f"(define-fun |{module.name}_h| ((state |{module.state_sort}|)) Bool")
        lines.append("  true")
        lines.append(")")
        
        return lines
    
    def _generate_transition_predicate(self, module: SMT2Module) -> List[str]:
        """Generate transition relation predicate.
        
        Args:
            module: Module with transitions
            
        Returns:
            List of SMT2 lines defining transition predicate
        """
        lines = []
        
        # Build transition constraints
        trans_constraints = []
        
        for trans in module.transitions:
            constraint = f"(= {trans.next_value_expr} (|{module.name}#{trans.register_name}| next_state))"
            if trans.condition:
                constraint = f"(=> {trans.condition} {constraint})"
            trans_constraints.append(constraint)
        
        if not trans_constraints:
            expr = "true"
        elif len(trans_constraints) == 1:
            expr = trans_constraints[0]
        else:
            trans_str = "\n    ".join(trans_constraints)
            expr = f"(and\n    {trans_str})"
        
        lines.append(f"(define-fun |{module.name}_t| ((state |{module.state_sort}|) (next_state |{module.state_sort}|)) Bool")
        lines.append(f"  {expr}")
        lines.append(")")
        
        return lines

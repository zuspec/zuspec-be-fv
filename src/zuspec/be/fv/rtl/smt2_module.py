"""
SMT2 Module representation.

Defines data structures for representing an SMT2 module with state, signals,
combinational logic, and transition relations.
"""

from typing import Dict, List, Optional, Any
from dataclasses import dataclass, field
import sys
sys.path.insert(0, 'packages/zuspec-dataclasses/src')

try:
    from zuspec.dataclasses import ir
except ImportError:
    ir = None


@dataclass
class SMT2Signal:
    """Represents a signal in an SMT2 module.

    Signals are functions over the module state sort.

    For combinationally-defined wires/outputs, set `def_expr` to emit a
    `(define-fun |Module#sig| ...)` instead of a `(declare-fun ...)`.
    """

    name: str
    smt_name: str
    datatype: Any  # ir.DataType
    direction: Optional[Any] = None  # ir.SignalDirection
    width: int = 1
    is_signed: bool = False
    initial_value: Optional[str] = None
    is_register: bool = False

    # Combinational definition (Phase 5)
    def_expr: Optional[str] = None
    def_deps: List[str] = field(default_factory=list)


@dataclass
class SMT2Function:
    """Represents a combinational function in SMT2.
    
    Attributes:
        name: Function name
        smt_name: SMT2 identifier
        params: List of (name, type) tuples for parameters
        return_type: Return type description
        body: SMT2 expression string
    """
    name: str
    smt_name: str
    params: List[tuple] = field(default_factory=list)
    return_type: str = "Bool"
    body: str = "true"


@dataclass
class SMT2Transition:
    """Represents a state transition constraint.
    
    Attributes:
        register_name: Name of register being updated
        next_value_expr: SMT2 expression for next value
        condition: Optional condition (for conditional assignments)
    """
    register_name: str
    next_value_expr: str
    condition: Optional[str] = None


@dataclass
class SMT2Module:
    """Represents a complete SMT2 module with state machine.
    
    This corresponds to a Zuspec component translated to SMT2 format.
    The module captures:
    - State sort (represents a snapshot of all state)
    - Inputs, outputs, and registers
    - Combinational logic functions
    - State transition relations
    - Formal properties (assertions, assumptions, coverage)
    
    Attributes:
        name: Module name
        state_sort: SMT2 sort name for state
        inputs: Dictionary of input signals
        outputs: Dictionary of output signals  
        registers: Dictionary of register signals
        wires: Dictionary of intermediate wire signals
        comb_logic: List of combinational functions
        transitions: List of state transitions
        assertions: List of assertion expressions
        assumptions: List of assumption expressions
        initial_conditions: List of initial state constraints
        coverage_goals: List of coverage goal expressions
    """
    name: str
    state_sort: str = ""
    inputs: Dict[str, SMT2Signal] = field(default_factory=dict)
    outputs: Dict[str, SMT2Signal] = field(default_factory=dict)
    registers: Dict[str, SMT2Signal] = field(default_factory=dict)
    wires: Dict[str, SMT2Signal] = field(default_factory=dict)
    comb_logic: List[SMT2Function] = field(default_factory=list)
    transitions: List[SMT2Transition] = field(default_factory=list)
    assertions: List[str] = field(default_factory=list)
    assumptions: List[str] = field(default_factory=list)
    initial_conditions: List[str] = field(default_factory=list)
    coverage_goals: List[str] = field(default_factory=list)
    
    def __post_init__(self):
        """Initialize state sort name if not provided."""
        if not self.state_sort:
            self.state_sort = f"{self.name}_s"
    
    def add_input(self, signal: SMT2Signal):
        """Add an input signal to the module."""
        self.inputs[signal.name] = signal
    
    def add_output(self, signal: SMT2Signal):
        """Add an output signal to the module."""
        self.outputs[signal.name] = signal
    
    def add_register(self, signal: SMT2Signal):
        """Add a register signal to the module."""
        signal.is_register = True
        self.registers[signal.name] = signal
    
    def add_wire(self, signal: SMT2Signal):
        """Add a wire (combinational) signal to the module."""
        self.wires[signal.name] = signal
    
    def add_comb_function(self, func: SMT2Function):
        """Add a combinational logic function."""
        self.comb_logic.append(func)
    
    def add_transition(self, trans: SMT2Transition):
        """Add a state transition constraint."""
        self.transitions.append(trans)
    
    def add_assertion(self, expr: str):
        """Add an assertion (property that must hold)."""
        self.assertions.append(expr)
    
    def add_assumption(self, expr: str):
        """Add an assumption (constraint on inputs)."""
        self.assumptions.append(expr)
    
    def add_initial_condition(self, expr: str):
        """Add an initial state condition."""
        self.initial_conditions.append(expr)
    
    def add_coverage_goal(self, expr: str):
        """Add a coverage goal."""
        self.coverage_goals.append(expr)
    
    def get_all_signals(self) -> Dict[str, SMT2Signal]:
        """Get all signals (inputs, outputs, registers, wires)."""
        all_signals = {}
        all_signals.update(self.inputs)
        all_signals.update(self.outputs)
        all_signals.update(self.registers)
        all_signals.update(self.wires)
        return all_signals

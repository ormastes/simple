use crate::hir::{TypeId, BinOp, UnaryOp};
use simple_parser::ast::Visibility;

//==============================================================================
// Local Variable Kind (for formal verification)
//==============================================================================
// Distinguishing parameters from local variables helps with verification:
// - Parameters have defined values at function entry
// - Locals may be uninitialized until assigned
//
// Lean equivalent:
//   inductive LocalKind | parameter | local

/// Distinguishes function parameters from local variables.
/// For formal verification, parameters are known to be initialized at entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LocalKind {
    /// Function parameter - initialized at function entry
    Parameter,
    /// Local variable - may need initialization check
    Local,
}

impl LocalKind {
    /// Check if this is a function parameter.
    pub fn is_parameter(&self) -> bool {
        matches!(self, LocalKind::Parameter)
    }

    /// Check if this is a local variable.
    pub fn is_local(&self) -> bool {
        matches!(self, LocalKind::Local)
    }
}

//==============================================================================
// Effect Tracking (for formal verification)
//==============================================================================
// This module provides explicit effect tracking that maps directly to the
// Lean 4 formal verification models:
// - `verification/waitless_compile/` for blocking operation detection
// - `verification/nogc_compile/` for GC allocation detection
//
// The Lean models are:
//   inductive Effect | compute | io | wait
//   def pipelineSafe (es : List Effect) : Prop := ∀ e, e ∈ es → waitless e = true
//
//   inductive Instr | const | add | gcAlloc
//   def nogc (p : List Instr) : Prop := ∀ i, i ∈ p → i ≠ Instr.gcAlloc
//
// Invariants:
// - Waitless: No blocking wait operations in the pipeline
// - NoGC: No GC allocations in the program

//==============================================================================
// WaitlessEffect - Exact match to WaitlessCompile.lean
//==============================================================================
// This enum matches the Lean model exactly with 3 variants.
//
// Lean equivalent:
// ```lean
// inductive Effect
//   | compute
//   | io
//   | wait
//   deriving DecidableEq, Repr
// ```

/// Effect type matching WaitlessCompile.lean exactly (3 variants).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum WaitlessEffect {
    /// Pure computation
    Compute,
    /// I/O operation (non-blocking)
    Io,
    /// Blocking wait operation
    Wait,
}

/// Lean: def waitless (e : Effect) : Bool := match e with | Effect.wait => false | _ => true
pub fn waitless(e: WaitlessEffect) -> bool {
    !matches!(e, WaitlessEffect::Wait)
}

/// Lean: def pipelineSafe (es : List Effect) : Prop := ∀ e, e ∈ es → waitless e = true
pub fn pipeline_safe(es: &[WaitlessEffect]) -> bool {
    es.iter().all(|e| waitless(*e))
}

/// Lean: theorem append_safe {a b : List Effect} :
///   pipelineSafe a → pipelineSafe b → pipelineSafe (a ++ b)
///
/// This function encodes the theorem as a runtime check.
/// If both inputs are safe, the output is guaranteed safe.
pub fn append_safe(a: Vec<WaitlessEffect>, b: Vec<WaitlessEffect>) -> Vec<WaitlessEffect> {
    debug_assert!(pipeline_safe(&a), "Precondition: a must be pipeline safe");
    debug_assert!(pipeline_safe(&b), "Precondition: b must be pipeline safe");
    let mut result = a;
    result.extend(b);
    debug_assert!(pipeline_safe(&result), "Postcondition: result must be pipeline safe");
    result
}

/// Lean: theorem wait_detected (e : Effect) : pipelineSafe [e] → e ≠ Effect.wait
///
/// If a singleton list is pipeline safe, it cannot contain wait.
pub fn wait_detected(e: WaitlessEffect) -> bool {
    if pipeline_safe(&[e]) {
        e != WaitlessEffect::Wait
    } else {
        true // vacuously true if not safe
    }
}

//==============================================================================
// NogcInstr - Exact match to NogcCompile.lean
//==============================================================================
// This enum matches the Lean model exactly with 3 variants.
//
// Lean equivalent:
// ```lean
// inductive Instr
//   | const (n : Nat)
//   | add
//   | gcAlloc
//   deriving DecidableEq, Repr
// ```

/// Instruction type matching NogcCompile.lean exactly (3 variants).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NogcInstr {
    /// Load constant
    Const(u64),
    /// Addition
    Add,
    /// GC allocation (forbidden in nogc mode)
    GcAlloc,
}

/// Lean: def nogc (p : List Instr) : Prop := ∀ i, i ∈ p → i ≠ Instr.gcAlloc
pub fn nogc(p: &[NogcInstr]) -> bool {
    p.iter().all(|i| !matches!(i, NogcInstr::GcAlloc))
}

/// Lean: theorem nogc_append {a b : List Instr} : nogc a → nogc b → nogc (append a b)
///
/// This function encodes the theorem as a runtime check.
pub fn nogc_append(a: Vec<NogcInstr>, b: Vec<NogcInstr>) -> Vec<NogcInstr> {
    debug_assert!(nogc(&a), "Precondition: a must be nogc");
    debug_assert!(nogc(&b), "Precondition: b must be nogc");
    let mut result = a;
    result.extend(b);
    debug_assert!(nogc(&result), "Postcondition: result must be nogc");
    result
}

/// Lean: theorem nogc_singleton {i : Instr} (h : i ≠ Instr.gcAlloc) : nogc [i]
///
/// A singleton list is nogc if and only if the instruction is not gcAlloc.
pub fn nogc_singleton(i: &NogcInstr) -> bool {
    !matches!(i, NogcInstr::GcAlloc)
}

//==============================================================================
// Effect - Combined type for production use
//==============================================================================

/// Effect marker for instructions (combined for production use).
/// Maps directly to the Lean `Effect` inductive type with GcAlloc added.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Effect {
    /// Pure computation, no side effects
    Compute,
    /// I/O operation (non-blocking)
    Io,
    /// Blocking wait operation
    Wait,
    /// GC allocation
    GcAlloc,
}

impl Effect {
    /// Check if this effect is waitless (non-blocking).
    /// Corresponds to Lean's `waitless` predicate.
    pub fn is_waitless(&self) -> bool {
        !matches!(self, Effect::Wait)
    }

    /// Check if this effect involves GC.
    /// Corresponds to Lean's `nogc` check.
    pub fn is_nogc(&self) -> bool {
        !matches!(self, Effect::GcAlloc)
    }

    /// Convert to WaitlessEffect (for Lean model correspondence).
    pub fn to_waitless(&self) -> WaitlessEffect {
        match self {
            Effect::Compute => WaitlessEffect::Compute,
            Effect::Io => WaitlessEffect::Io,
            Effect::Wait => WaitlessEffect::Wait,
            Effect::GcAlloc => WaitlessEffect::Compute, // GcAlloc is not blocking
        }
    }
}

/// Effect set for a sequence of instructions.
/// Supports composition via append, matching Lean's list-based model.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EffectSet {
    effects: Vec<Effect>,
}

impl EffectSet {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add an effect to the set.
    pub fn push(&mut self, effect: Effect) {
        self.effects.push(effect);
    }

    /// Check if all effects are waitless.
    /// Corresponds to Lean's `pipelineSafe` predicate.
    pub fn is_pipeline_safe(&self) -> bool {
        self.effects.iter().all(|e| e.is_waitless())
    }

    /// Check if no effects involve GC.
    /// Corresponds to Lean's `nogc` predicate.
    pub fn is_nogc(&self) -> bool {
        self.effects.iter().all(|e| e.is_nogc())
    }

    /// Append another effect set (composition).
    /// Corresponds to Lean's list append for effects.
    ///
    /// Lean theorem: append_safe {a b} : pipelineSafe a → pipelineSafe b → pipelineSafe (a ++ b)
    pub fn append(&mut self, other: &EffectSet) {
        self.effects.extend(other.effects.iter().copied());
    }

    /// Append with safety preservation check.
    ///
    /// Lean: theorem append_safe {a b : List Effect} :
    ///   pipelineSafe a → pipelineSafe b → pipelineSafe (a ++ b)
    ///
    /// Returns whether the result is still pipeline safe.
    pub fn append_preserving_safety(&mut self, other: &EffectSet) -> bool {
        let was_safe = self.is_pipeline_safe() && other.is_pipeline_safe();
        self.append(other);
        // Postcondition: if both were safe, result must be safe
        debug_assert!(!was_safe || self.is_pipeline_safe(),
            "Theorem violation: append should preserve pipeline safety");
        self.is_pipeline_safe()
    }

    /// Append with nogc preservation check.
    ///
    /// Lean: theorem nogc_append {a b} : nogc a → nogc b → nogc (a ++ b)
    ///
    /// Returns whether the result is still nogc.
    pub fn append_preserving_nogc(&mut self, other: &EffectSet) -> bool {
        let was_nogc = self.is_nogc() && other.is_nogc();
        self.append(other);
        // Postcondition: if both were nogc, result must be nogc
        debug_assert!(!was_nogc || self.is_nogc(),
            "Theorem violation: append should preserve nogc property");
        self.is_nogc()
    }

    /// Get the list of effects.
    pub fn effects(&self) -> &[Effect] {
        &self.effects
    }

    /// Check if empty.
    pub fn is_empty(&self) -> bool {
        self.effects.is_empty()
    }

    /// Convert to WaitlessEffect list for Lean model correspondence.
    pub fn to_waitless(&self) -> Vec<WaitlessEffect> {
        self.effects.iter().map(|e| e.to_waitless()).collect()
    }
}

/// Trait for types that can report their effects.
pub trait HasEffects {
    /// Return the effect of this item.
    fn effect(&self) -> Effect;
}

//==============================================================================
// Builtin Functions (for formal verification)
//==============================================================================
// Explicit enumeration of known builtin functions with their effects.
// This enables exhaustive pattern matching in Lean proofs.
//
// Lean equivalent:
//   inductive BuiltinFunc
//     | await | wait | join | recv | sleep  -- blocking
//     | gcAlloc | gcNew | box              -- gc allocating
//     | print | println | read | write | send | spawn -- io
//     | other (name : String)              -- user-defined

/// Known builtin functions with statically-known effects.
/// For formal verification, having an explicit enum is better than string matching.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BuiltinFunc {
    // Blocking operations
    Await,
    Wait,
    Join,
    Recv,
    Sleep,
    // GC allocating operations
    GcAlloc,
    GcNew,
    Box,
    // I/O operations
    Print,
    Println,
    Read,
    Write,
    Send,
    Spawn,
}

impl BuiltinFunc {
    /// Get the effect category of this builtin
    pub fn effect(&self) -> Effect {
        match self {
            BuiltinFunc::Await | BuiltinFunc::Wait | BuiltinFunc::Join |
            BuiltinFunc::Recv | BuiltinFunc::Sleep => Effect::Wait,

            BuiltinFunc::GcAlloc | BuiltinFunc::GcNew | BuiltinFunc::Box => Effect::GcAlloc,

            BuiltinFunc::Print | BuiltinFunc::Println | BuiltinFunc::Read |
            BuiltinFunc::Write | BuiltinFunc::Send | BuiltinFunc::Spawn => Effect::Io,
        }
    }

    /// Try to parse a builtin from a string name
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "await" => Some(BuiltinFunc::Await),
            "wait" => Some(BuiltinFunc::Wait),
            "join" => Some(BuiltinFunc::Join),
            "recv" => Some(BuiltinFunc::Recv),
            "sleep" => Some(BuiltinFunc::Sleep),
            "gc_alloc" => Some(BuiltinFunc::GcAlloc),
            "gc_new" => Some(BuiltinFunc::GcNew),
            "box" => Some(BuiltinFunc::Box),
            "print" => Some(BuiltinFunc::Print),
            "println" => Some(BuiltinFunc::Println),
            "read" => Some(BuiltinFunc::Read),
            "write" => Some(BuiltinFunc::Write),
            "send" => Some(BuiltinFunc::Send),
            "spawn" => Some(BuiltinFunc::Spawn),
            _ => None,
        }
    }

    /// Get the canonical string name
    pub fn name(&self) -> &'static str {
        match self {
            BuiltinFunc::Await => "await",
            BuiltinFunc::Wait => "wait",
            BuiltinFunc::Join => "join",
            BuiltinFunc::Recv => "recv",
            BuiltinFunc::Sleep => "sleep",
            BuiltinFunc::GcAlloc => "gc_alloc",
            BuiltinFunc::GcNew => "gc_new",
            BuiltinFunc::Box => "box",
            BuiltinFunc::Print => "print",
            BuiltinFunc::Println => "println",
            BuiltinFunc::Read => "read",
            BuiltinFunc::Write => "write",
            BuiltinFunc::Send => "send",
            BuiltinFunc::Spawn => "spawn",
        }
    }
}

//==============================================================================
// Call Target with Effect Information
//==============================================================================
// For more precise effect tracking, calls are tagged with their effect category.
// This allows distinguishing pure computation from I/O and blocking operations.
//
// Lean equivalent:
//   inductive CallTarget
//     | builtin (func : BuiltinFunc)
//     | user (name : String)

/// Call target with effect annotation for precise verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallTarget {
    /// Pure function - no side effects, can be reordered or eliminated
    Pure(String),
    /// I/O function - has side effects but non-blocking
    Io(String),
    /// Blocking function - may block the current thread
    Blocking(String),
    /// GC-allocating function - allocates on the GC heap
    GcAllocating(String),
}

impl CallTarget {
    /// Get the function name.
    pub fn name(&self) -> &str {
        match self {
            CallTarget::Pure(n) => n,
            CallTarget::Io(n) => n,
            CallTarget::Blocking(n) => n,
            CallTarget::GcAllocating(n) => n,
        }
    }

    /// Get the effect of this call.
    pub fn effect(&self) -> Effect {
        match self {
            CallTarget::Pure(_) => Effect::Compute,
            CallTarget::Io(_) => Effect::Io,
            CallTarget::Blocking(_) => Effect::Wait,
            CallTarget::GcAllocating(_) => Effect::GcAlloc,
        }
    }

    /// Check if this call is waitless.
    pub fn is_waitless(&self) -> bool {
        self.effect().is_waitless()
    }

    /// Check if this call is nogc.
    pub fn is_nogc(&self) -> bool {
        self.effect().is_nogc()
    }

    /// Create from function name using known function effect database.
    pub fn from_name(name: &str) -> Self {
        match name {
            // Blocking functions
            "await" | "wait" | "join" | "recv" | "sleep" => CallTarget::Blocking(name.to_string()),
            // GC allocating functions
            "gc_alloc" | "gc_new" | "box" => CallTarget::GcAllocating(name.to_string()),
            // I/O functions
            "print" | "println" | "read" | "write" | "send" | "spawn" => CallTarget::Io(name.to_string()),
            // Pure functions (default)
            _ => CallTarget::Pure(name.to_string()),
        }
    }
}

//==============================================================================
// MIR Types
//==============================================================================

/// Basic block identifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct BlockId(pub u32);

/// Virtual register
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VReg(pub u32);

/// MIR instruction
#[derive(Debug, Clone, PartialEq)]
pub enum MirInst {
    /// Load constant integer
    ConstInt { dest: VReg, value: i64 },

    /// Load constant float
    ConstFloat { dest: VReg, value: f64 },

    /// Load constant bool
    ConstBool { dest: VReg, value: bool },

    /// Copy value from one register to another
    Copy { dest: VReg, src: VReg },

    /// Binary operation
    BinOp { dest: VReg, op: BinOp, left: VReg, right: VReg },

    /// Unary operation
    UnaryOp { dest: VReg, op: UnaryOp, operand: VReg },

    /// Function call with effect tracking
    Call { dest: Option<VReg>, target: CallTarget, args: Vec<VReg> },

    /// Load from memory
    Load { dest: VReg, addr: VReg, ty: TypeId },

    /// Store to memory
    Store { addr: VReg, value: VReg, ty: TypeId },

    /// Get address of local variable
    LocalAddr { dest: VReg, local_index: usize },

    /// Get element pointer (for arrays/structs)
    GetElementPtr { dest: VReg, base: VReg, index: VReg },

    /// GC allocation (explicit for verification)
    GcAlloc { dest: VReg, ty: TypeId },

    /// Blocking wait (explicit for verification)
    Wait { dest: Option<VReg>, target: VReg },
}

impl HasEffects for MirInst {
    /// Return the effect of this instruction.
    /// Enables compile-time verification of waitless/nogc properties.
    fn effect(&self) -> Effect {
        match self {
            // Pure computation
            MirInst::ConstInt { .. }
            | MirInst::ConstFloat { .. }
            | MirInst::ConstBool { .. }
            | MirInst::Copy { .. }
            | MirInst::BinOp { .. }
            | MirInst::UnaryOp { .. }
            | MirInst::Load { .. }
            | MirInst::Store { .. }
            | MirInst::LocalAddr { .. }
            | MirInst::GetElementPtr { .. } => Effect::Compute,

            // Function calls - effect depends on target
            MirInst::Call { target, .. } => target.effect(),

            // Explicit effect markers for verification
            MirInst::GcAlloc { .. } => Effect::GcAlloc,
            MirInst::Wait { .. } => Effect::Wait,
        }
    }
}

impl MirInst {
    /// Check if this instruction is waitless.
    pub fn is_waitless(&self) -> bool {
        self.effect().is_waitless()
    }

    /// Check if this instruction is nogc.
    pub fn is_nogc(&self) -> bool {
        self.effect().is_nogc()
    }
}

/// Block terminator
#[derive(Debug, Clone, PartialEq)]
pub enum Terminator {
    /// Return from function
    Return(Option<VReg>),

    /// Unconditional jump
    Jump(BlockId),

    /// Conditional branch
    Branch { cond: VReg, then_block: BlockId, else_block: BlockId },

    /// Unreachable (after infinite loop, etc.)
    Unreachable,
}

impl Terminator {
    /// Check if this is a "real" terminator (not Unreachable placeholder)
    pub fn is_sealed(&self) -> bool {
        !matches!(self, Terminator::Unreachable)
    }

    /// Check if this terminator transfers control to another block
    pub fn is_branching(&self) -> bool {
        matches!(self, Terminator::Jump(_) | Terminator::Branch { .. })
    }

    /// Get all successor block IDs
    pub fn successors(&self) -> Vec<BlockId> {
        match self {
            Terminator::Return(_) => vec![],
            Terminator::Jump(target) => vec![*target],
            Terminator::Branch { then_block, else_block, .. } => vec![*then_block, *else_block],
            Terminator::Unreachable => vec![],
        }
    }
}

//==============================================================================
// Block Builder (for formal verification)
//==============================================================================
// BlockBuilder provides a type-safe way to construct blocks where the
// terminator state is tracked explicitly. This maps to a Lean state machine:
//
//   inductive BlockBuildState
//     | open (instructions : List MirInst)
//     | sealed (instructions : List MirInst) (terminator : Terminator)
//
// Invariant: Once sealed, no more instructions can be added.

/// Block build state - tracks whether block is open or sealed
#[derive(Debug, Clone, PartialEq)]
pub enum BlockBuildState {
    /// Block is open, accepting instructions
    Open {
        id: BlockId,
        instructions: Vec<MirInst>,
    },
    /// Block has been sealed with a terminator
    Sealed {
        id: BlockId,
        instructions: Vec<MirInst>,
        terminator: Terminator,
    },
}

impl BlockBuildState {
    /// Create a new open block
    pub fn new(id: BlockId) -> Self {
        BlockBuildState::Open {
            id,
            instructions: Vec::new(),
        }
    }

    /// Check if block is open (can accept more instructions)
    pub fn is_open(&self) -> bool {
        matches!(self, BlockBuildState::Open { .. })
    }

    /// Check if block is sealed (has terminator)
    pub fn is_sealed(&self) -> bool {
        matches!(self, BlockBuildState::Sealed { .. })
    }

    /// Get block ID
    pub fn id(&self) -> BlockId {
        match self {
            BlockBuildState::Open { id, .. } => *id,
            BlockBuildState::Sealed { id, .. } => *id,
        }
    }

    /// Get instructions (regardless of state)
    pub fn instructions(&self) -> &[MirInst] {
        match self {
            BlockBuildState::Open { instructions, .. } => instructions,
            BlockBuildState::Sealed { instructions, .. } => instructions,
        }
    }

    /// Get terminator if sealed
    pub fn terminator(&self) -> Option<&Terminator> {
        match self {
            BlockBuildState::Open { .. } => None,
            BlockBuildState::Sealed { terminator, .. } => Some(terminator),
        }
    }
}

/// Type-safe block builder that enforces build state transitions
#[derive(Debug)]
pub struct BlockBuilder {
    state: BlockBuildState,
}

/// Error type for block building operations
#[derive(Debug, Clone, PartialEq)]
pub enum BlockBuildError {
    /// Tried to add instruction to sealed block
    AlreadySealed,
    /// Tried to seal an already sealed block
    AlreadySealedWith(Terminator),
    /// Tried to finalize an open block
    NotSealed,
}

impl BlockBuilder {
    /// Create a new block builder for the given block ID
    pub fn new(id: BlockId) -> Self {
        Self {
            state: BlockBuildState::new(id),
        }
    }

    /// Get current build state
    pub fn state(&self) -> &BlockBuildState {
        &self.state
    }

    /// Check if block is open
    pub fn is_open(&self) -> bool {
        self.state.is_open()
    }

    /// Check if block is sealed
    pub fn is_sealed(&self) -> bool {
        self.state.is_sealed()
    }

    /// Get block ID
    pub fn id(&self) -> BlockId {
        self.state.id()
    }

    /// Add an instruction to the block (only if open)
    pub fn push(&mut self, inst: MirInst) -> Result<(), BlockBuildError> {
        match &mut self.state {
            BlockBuildState::Open { instructions, .. } => {
                instructions.push(inst);
                Ok(())
            }
            BlockBuildState::Sealed { .. } => Err(BlockBuildError::AlreadySealed),
        }
    }

    /// Seal the block with a terminator (only if open)
    pub fn seal(&mut self, terminator: Terminator) -> Result<(), BlockBuildError> {
        match std::mem::replace(&mut self.state, BlockBuildState::Open {
            id: BlockId(0),
            instructions: Vec::new(),
        }) {
            BlockBuildState::Open { id, instructions } => {
                self.state = BlockBuildState::Sealed {
                    id,
                    instructions,
                    terminator,
                };
                Ok(())
            }
            BlockBuildState::Sealed { id, instructions, terminator: old_term } => {
                // Restore the sealed state
                self.state = BlockBuildState::Sealed {
                    id,
                    instructions,
                    terminator: old_term.clone(),
                };
                Err(BlockBuildError::AlreadySealedWith(old_term))
            }
        }
    }

    /// Seal with jump if not already sealed (for fallthrough)
    pub fn seal_with_jump_if_open(&mut self, target: BlockId) {
        if self.is_open() {
            let _ = self.seal(Terminator::Jump(target));
        }
    }

    /// Finalize and return the completed block (only if sealed)
    pub fn finalize(self) -> Result<MirBlock, BlockBuildError> {
        match self.state {
            BlockBuildState::Sealed { id, instructions, terminator } => {
                Ok(MirBlock {
                    id,
                    instructions,
                    terminator,
                })
            }
            BlockBuildState::Open { .. } => Err(BlockBuildError::NotSealed),
        }
    }

    /// Force finalize - use Unreachable if not sealed (for compatibility)
    pub fn finalize_or_unreachable(self) -> MirBlock {
        match self.state {
            BlockBuildState::Sealed { id, instructions, terminator } => {
                MirBlock { id, instructions, terminator }
            }
            BlockBuildState::Open { id, instructions } => {
                MirBlock {
                    id,
                    instructions,
                    terminator: Terminator::Unreachable,
                }
            }
        }
    }
}

/// Basic block in MIR
#[derive(Debug, Clone)]
pub struct MirBlock {
    pub id: BlockId,
    pub instructions: Vec<MirInst>,
    pub terminator: Terminator,
}

impl MirBlock {
    pub fn new(id: BlockId) -> Self {
        Self {
            id,
            instructions: Vec::new(),
            terminator: Terminator::Unreachable,
        }
    }

    /// Create from a block builder (must be sealed)
    pub fn from_builder(builder: BlockBuilder) -> Result<Self, BlockBuildError> {
        builder.finalize()
    }

    /// Check if block is properly terminated (not Unreachable)
    pub fn is_sealed(&self) -> bool {
        self.terminator.is_sealed()
    }

    /// Collect all effects in this block.
    pub fn effects(&self) -> EffectSet {
        let mut set = EffectSet::new();
        for inst in &self.instructions {
            set.push(inst.effect());
        }
        set
    }

    /// Check if this block is waitless (no blocking operations).
    pub fn is_waitless(&self) -> bool {
        self.effects().is_pipeline_safe()
    }

    /// Check if this block is nogc (no GC allocations).
    pub fn is_nogc(&self) -> bool {
        self.effects().is_nogc()
    }
}

/// Local variable in MIR function
#[derive(Debug, Clone)]
pub struct MirLocal {
    pub name: String,
    pub ty: TypeId,
    pub kind: LocalKind,
}

impl MirLocal {
    /// Check if this is a function argument/parameter.
    /// Helper for backwards compatibility.
    pub fn is_arg(&self) -> bool {
        self.kind.is_parameter()
    }
}

/// MIR function
#[derive(Debug, Clone)]
pub struct MirFunction {
    pub name: String,
    pub params: Vec<MirLocal>,
    pub locals: Vec<MirLocal>,
    pub return_type: TypeId,
    pub blocks: Vec<MirBlock>,
    pub entry_block: BlockId,
    pub visibility: Visibility,
    next_vreg: u32,
    next_block: u32,
}

impl MirFunction {
    /// Create a new MIR function with the given visibility.
    pub fn new(name: String, return_type: TypeId, visibility: Visibility) -> Self {
        let entry = MirBlock::new(BlockId(0));
        Self {
            name,
            params: Vec::new(),
            locals: Vec::new(),
            return_type,
            blocks: vec![entry],
            entry_block: BlockId(0),
            visibility,
            next_vreg: 0,
            next_block: 1,
        }
    }

    /// Create a new MIR function from a boolean public flag.
    /// Helper for backwards compatibility during migration.
    pub fn new_from_bool(name: String, return_type: TypeId, is_public: bool) -> Self {
        let visibility = if is_public { Visibility::Public } else { Visibility::Private };
        Self::new(name, return_type, visibility)
    }

    /// Check if this function is public.
    /// Helper for backwards compatibility.
    pub fn is_public(&self) -> bool {
        self.visibility.is_public()
    }

    pub fn new_vreg(&mut self) -> VReg {
        let reg = VReg(self.next_vreg);
        self.next_vreg += 1;
        reg
    }

    pub fn new_block(&mut self) -> BlockId {
        let id = BlockId(self.next_block);
        self.next_block += 1;
        self.blocks.push(MirBlock::new(id));
        id
    }

    pub fn block(&self, id: BlockId) -> Option<&MirBlock> {
        self.blocks.iter().find(|b| b.id == id)
    }

    pub fn block_mut(&mut self, id: BlockId) -> Option<&mut MirBlock> {
        self.blocks.iter_mut().find(|b| b.id == id)
    }

    /// Collect all effects in this function.
    pub fn effects(&self) -> EffectSet {
        let mut set = EffectSet::new();
        for block in &self.blocks {
            set.append(&block.effects());
        }
        set
    }

    /// Check if this function is waitless (no blocking operations).
    pub fn is_waitless(&self) -> bool {
        self.effects().is_pipeline_safe()
    }

    /// Check if this function is nogc (no GC allocations).
    pub fn is_nogc(&self) -> bool {
        self.effects().is_nogc()
    }
}

/// MIR module
#[derive(Debug)]
pub struct MirModule {
    pub name: Option<String>,
    pub functions: Vec<MirFunction>,
}

impl MirModule {
    pub fn new() -> Self {
        Self {
            name: None,
            functions: Vec::new(),
        }
    }
}

impl Default for MirModule {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mir_function_creation() {
        let func = MirFunction::new("test".to_string(), TypeId::VOID, Visibility::Private);
        assert_eq!(func.name, "test");
        assert_eq!(func.blocks.len(), 1);
        assert_eq!(func.entry_block, BlockId(0));
        assert!(!func.is_public());
    }

    #[test]
    fn test_mir_function_visibility() {
        let pub_func = MirFunction::new("pub_fn".to_string(), TypeId::VOID, Visibility::Public);
        let priv_func = MirFunction::new("priv_fn".to_string(), TypeId::VOID, Visibility::Private);

        assert!(pub_func.is_public());
        assert!(!priv_func.is_public());
        assert_eq!(pub_func.visibility, Visibility::Public);
        assert_eq!(priv_func.visibility, Visibility::Private);
    }

    #[test]
    fn test_vreg_allocation() {
        let mut func = MirFunction::new("test".to_string(), TypeId::VOID, Visibility::Private);

        let r0 = func.new_vreg();
        let r1 = func.new_vreg();
        let r2 = func.new_vreg();

        assert_eq!(r0, VReg(0));
        assert_eq!(r1, VReg(1));
        assert_eq!(r2, VReg(2));
    }

    #[test]
    fn test_block_creation() {
        let mut func = MirFunction::new("test".to_string(), TypeId::VOID, Visibility::Private);

        let b1 = func.new_block();
        let b2 = func.new_block();

        assert_eq!(b1, BlockId(1));
        assert_eq!(b2, BlockId(2));
        assert_eq!(func.blocks.len(), 3);
    }

    #[test]
    fn test_mir_instructions() {
        let mut func = MirFunction::new("add".to_string(), TypeId::I64, Visibility::Public);

        let r0 = func.new_vreg();
        let r1 = func.new_vreg();
        let r2 = func.new_vreg();

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry.instructions.push(MirInst::ConstInt { dest: r0, value: 1 });
        entry.instructions.push(MirInst::ConstInt { dest: r1, value: 2 });
        entry.instructions.push(MirInst::BinOp {
            dest: r2,
            op: BinOp::Add,
            left: r0,
            right: r1
        });
        entry.terminator = Terminator::Return(Some(r2));

        assert_eq!(entry.instructions.len(), 3);
    }
}

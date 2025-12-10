use crate::hir::{BinOp, TypeId, UnaryOp};
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
// - `verification/async_compile/` for blocking operation detection
// - `verification/nogc_compile/` for GC allocation detection
//
// The Lean models are:
//   inductive Effect | compute | io | wait
//   def pipelineSafe (es : List Effect) : Prop := ∀ e, e ∈ es → is_async e = true
//
//   inductive Instr | const | add | gcAlloc
//   def nogc (p : List Instr) : Prop := ∀ i, i ∈ p → i ≠ Instr.gcAlloc
//
// Invariants:
// - Async: No blocking wait operations in the pipeline
// - NoGC: No GC allocations in the program

//==============================================================================
// AsyncEffect - Exact match to AsyncCompile.lean
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

/// Effect type matching AsyncCompile.lean exactly (3 variants).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum AsyncEffect {
    /// Pure computation
    Compute,
    /// I/O operation (non-blocking)
    Io,
    /// Blocking wait operation
    Wait,
}

/// Lean: def is_async (e : Effect) : Bool := match e with | Effect.wait => false | _ => true
pub fn is_async(e: AsyncEffect) -> bool {
    !matches!(e, AsyncEffect::Wait)
}

/// Lean: def pipelineSafe (es : List Effect) : Prop := ∀ e, e ∈ es → is_async e = true
pub fn pipeline_safe(es: &[AsyncEffect]) -> bool {
    es.iter().all(|e| is_async(*e))
}

/// Lean: theorem append_safe {a b : List Effect} :
///   pipelineSafe a → pipelineSafe b → pipelineSafe (a ++ b)
///
/// This function encodes the theorem as a runtime check.
/// If both inputs are safe, the output is guaranteed safe.
pub fn append_safe(a: Vec<AsyncEffect>, b: Vec<AsyncEffect>) -> Vec<AsyncEffect> {
    debug_assert!(pipeline_safe(&a), "Precondition: a must be pipeline safe");
    debug_assert!(pipeline_safe(&b), "Precondition: b must be pipeline safe");
    let mut result = a;
    result.extend(b);
    debug_assert!(
        pipeline_safe(&result),
        "Postcondition: result must be pipeline safe"
    );
    result
}

/// Lean: theorem wait_detected (e : Effect) : pipelineSafe [e] → e ≠ Effect.wait
///
/// If a singleton list is pipeline safe, it cannot contain wait.
pub fn wait_detected(e: AsyncEffect) -> bool {
    if pipeline_safe(&[e]) {
        e != AsyncEffect::Wait
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
    /// Check if this effect is async (non-blocking).
    /// Corresponds to Lean's `is_async` predicate.
    pub fn is_async(&self) -> bool {
        !matches!(self, Effect::Wait)
    }

    /// Check if this effect involves GC.
    /// Corresponds to Lean's `nogc` check.
    pub fn is_nogc(&self) -> bool {
        !matches!(self, Effect::GcAlloc)
    }

    /// Convert to AsyncEffect (for Lean model correspondence).
    pub fn to_async(&self) -> AsyncEffect {
        match self {
            Effect::Compute => AsyncEffect::Compute,
            Effect::Io => AsyncEffect::Io,
            Effect::Wait => AsyncEffect::Wait,
            Effect::GcAlloc => AsyncEffect::Compute, // GcAlloc is not blocking
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

    /// Check if all effects are async (non-blocking).
    /// Corresponds to Lean's `pipelineSafe` predicate.
    pub fn is_pipeline_safe(&self) -> bool {
        self.effects.iter().all(|e| e.is_async())
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
        debug_assert!(
            !was_safe || self.is_pipeline_safe(),
            "Theorem violation: append should preserve pipeline safety"
        );
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
        debug_assert!(
            !was_nogc || self.is_nogc(),
            "Theorem violation: append should preserve nogc property"
        );
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

    /// Convert to AsyncEffect list for Lean model correspondence.
    pub fn to_async(&self) -> Vec<AsyncEffect> {
        self.effects.iter().map(|e| e.to_async()).collect()
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
            BuiltinFunc::Await
            | BuiltinFunc::Wait
            | BuiltinFunc::Join
            | BuiltinFunc::Recv
            | BuiltinFunc::Sleep => Effect::Wait,

            BuiltinFunc::GcAlloc | BuiltinFunc::GcNew | BuiltinFunc::Box => Effect::GcAlloc,

            BuiltinFunc::Print
            | BuiltinFunc::Println
            | BuiltinFunc::Read
            | BuiltinFunc::Write
            | BuiltinFunc::Send
            | BuiltinFunc::Spawn => Effect::Io,
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

    /// Check if this call is async (non-blocking).
    pub fn is_async(&self) -> bool {
        self.effect().is_async()
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
            "print" | "println" | "read" | "write" | "send" | "spawn" => {
                CallTarget::Io(name.to_string())
            }
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
    BinOp {
        dest: VReg,
        op: BinOp,
        left: VReg,
        right: VReg,
    },

    /// Unary operation
    UnaryOp {
        dest: VReg,
        op: UnaryOp,
        operand: VReg,
    },

    /// Function call with effect tracking
    Call {
        dest: Option<VReg>,
        target: CallTarget,
        args: Vec<VReg>,
    },

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

    // =========================================================================
    // Interpreter fallback instructions (will be removed once all codegen implemented)
    // =========================================================================
    /// Call interpreter for a function that can't be compiled yet.
    /// This is a temporary fallback - will be removed once all features have native codegen.
    InterpCall {
        dest: Option<VReg>,
        func_name: String,
        args: Vec<VReg>,
    },

    /// Evaluate an expression via interpreter fallback.
    /// Temporary - will be removed once all expressions have native codegen.
    InterpEval { dest: VReg, expr_index: u32 },

    // =========================================================================
    // Collection instructions
    // =========================================================================
    /// Create an array literal from elements
    ArrayLit { dest: VReg, elements: Vec<VReg> },

    /// Create a tuple literal from elements
    TupleLit { dest: VReg, elements: Vec<VReg> },

    /// Create a dictionary literal from key-value pairs
    DictLit {
        dest: VReg,
        keys: Vec<VReg>,
        values: Vec<VReg>,
    },

    /// Get an element from a collection by index
    IndexGet {
        dest: VReg,
        collection: VReg,
        index: VReg,
    },

    /// Set an element in a collection by index
    IndexSet {
        collection: VReg,
        index: VReg,
        value: VReg,
    },

    /// Create a slice of a collection
    SliceOp {
        dest: VReg,
        collection: VReg,
        start: Option<VReg>,
        end: Option<VReg>,
        step: Option<VReg>,
    },

    /// Spread/unpack a collection into multiple values
    Spread { dest: VReg, source: VReg },

    /// Create a constant string
    ConstString { dest: VReg, value: String },

    /// Create a symbol
    ConstSymbol { dest: VReg, value: String },

    /// Format string interpolation
    FStringFormat { dest: VReg, parts: Vec<FStringPart> },

    // =========================================================================
    // Closure instructions (Phase 3)
    // =========================================================================
    /// Create a closure with captured variables (zero-cost: typed struct allocation)
    ClosureCreate {
        dest: VReg,
        /// Function name for direct call
        func_name: String,
        /// Total closure size: 8 (fn_ptr) + sum of capture sizes
        closure_size: u32,
        /// Byte offsets for each capture (first capture at offset 8)
        capture_offsets: Vec<u32>,
        /// Types of captured variables (for correct store instruction)
        capture_types: Vec<TypeId>,
        /// Captured variable values
        captures: Vec<VReg>,
    },

    /// Indirect call through a closure or function pointer (zero-cost: load + indirect call)
    IndirectCall {
        dest: Option<VReg>,
        /// The closure/function pointer to call
        callee: VReg,
        /// Parameter types for the call signature
        param_types: Vec<TypeId>,
        /// Return type
        return_type: TypeId,
        /// Arguments to pass
        args: Vec<VReg>,
        /// Effect annotation for the call
        effect: Effect,
    },

    // =========================================================================
    // Object/Method instructions (Phase 4)
    // =========================================================================
    /// Initialize a struct/class instance (zero-cost: inline allocation + stores)
    StructInit {
        dest: VReg,
        /// Type ID for the struct
        type_id: TypeId,
        /// Total struct size in bytes (for allocation)
        struct_size: u32,
        /// Byte offsets for each field (for direct stores)
        field_offsets: Vec<u32>,
        /// Field types (for correct store instruction)
        field_types: Vec<TypeId>,
        /// Field values in declaration order
        field_values: Vec<VReg>,
    },

    /// Get a field from an object (zero-cost: pointer arithmetic + load)
    FieldGet {
        dest: VReg,
        object: VReg,
        /// Byte offset from object pointer (computed at compile time)
        byte_offset: u32,
        /// Field type (for correct load instruction)
        field_type: TypeId,
    },

    /// Set a field on an object (zero-cost: pointer arithmetic + store)
    FieldSet {
        object: VReg,
        /// Byte offset from object pointer (computed at compile time)
        byte_offset: u32,
        /// Field type (for correct store instruction)
        field_type: TypeId,
        value: VReg,
    },

    /// Static method call (zero-cost: direct function call)
    /// Receiver type is known at compile time, so we can call directly.
    MethodCallStatic {
        dest: Option<VReg>,
        receiver: VReg,
        /// Direct function name (Type::method format)
        func_name: String,
        /// Arguments (not including receiver)
        args: Vec<VReg>,
    },

    /// Virtual method call (vtable-based dispatch for dyn types)
    /// Only used when receiver type is unknown at compile time.
    MethodCallVirtual {
        dest: Option<VReg>,
        receiver: VReg,
        /// Vtable slot index (computed at compile time)
        vtable_slot: u32,
        /// Method signature for indirect call
        param_types: Vec<TypeId>,
        return_type: TypeId,
        /// Arguments (not including receiver)
        args: Vec<VReg>,
    },

    /// Built-in method call (e.g., array.push, string.len)
    BuiltinMethod {
        dest: Option<VReg>,
        receiver: VReg,
        /// Type of the receiver (for dispatch)
        receiver_type: String,
        /// Method name
        method: String,
        /// Arguments (not including receiver)
        args: Vec<VReg>,
    },

    // =========================================================================
    // Pattern matching instructions (Phase 5)
    // =========================================================================
    /// Test if a value matches a pattern
    PatternTest {
        dest: VReg,
        subject: VReg,
        pattern: MirPattern,
    },

    /// Bind variables from a pattern match
    PatternBind {
        dest: VReg,
        subject: VReg,
        /// Binding path within the pattern
        binding: PatternBinding,
    },

    /// Get enum discriminant (variant index)
    EnumDiscriminant { dest: VReg, value: VReg },

    /// Get enum payload
    EnumPayload { dest: VReg, value: VReg },

    /// Create a unit enum variant (no payload)
    EnumUnit {
        dest: VReg,
        /// Enum type name
        enum_name: String,
        /// Variant name
        variant_name: String,
    },

    /// Create an enum variant with payload
    EnumWith {
        dest: VReg,
        /// Enum type name
        enum_name: String,
        /// Variant name
        variant_name: String,
        /// Payload value
        payload: VReg,
    },

    // =========================================================================
    // Async/Generator instructions (Phase 6)
    // =========================================================================
    /// Create a future
    FutureCreate {
        dest: VReg,
        /// Block containing the async body
        body_block: BlockId,
    },

    /// Await a future
    Await { dest: VReg, future: VReg },

    /// Spawn an actor
    ActorSpawn {
        dest: VReg,
        /// Block containing the actor body
        body_block: BlockId,
    },

    /// Send a message to an actor
    ActorSend { actor: VReg, message: VReg },

    /// Receive a message from the current actor's mailbox
    ActorRecv { dest: VReg },

    /// Create a generator
    GeneratorCreate {
        dest: VReg,
        /// Block containing the generator body
        body_block: BlockId,
    },

    /// Yield a value from a generator
    Yield { value: VReg },

    /// Get next value from a generator
    GeneratorNext { dest: VReg, generator: VReg },

    // =========================================================================
    // Error handling instructions (Phase 7)
    // =========================================================================
    /// Try to unwrap a Result/Option, branching on error
    TryUnwrap {
        dest: VReg,
        value: VReg,
        /// Block to jump to on error
        error_block: BlockId,
        /// Register to store error value
        error_dest: VReg,
    },

    /// Create Option::Some
    OptionSome { dest: VReg, value: VReg },

    /// Create Option::None
    OptionNone { dest: VReg },

    /// Create Result::Ok
    ResultOk { dest: VReg, value: VReg },

    /// Create Result::Err
    ResultErr { dest: VReg, value: VReg },
}

/// Captured variable in a closure
#[derive(Debug, Clone, PartialEq)]
pub struct CapturedVar {
    /// Original variable register
    pub source: VReg,
    /// Capture mode
    pub mode: CaptureMode,
}

/// How a variable is captured by a closure
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CaptureMode {
    /// Capture by value (copy)
    ByValue,
    /// Capture by reference (borrow)
    ByRef,
    /// Capture by mutable reference
    ByMutRef,
}

/// Pattern for pattern matching
#[derive(Debug, Clone, PartialEq)]
pub enum MirPattern {
    /// Wildcard pattern (matches anything)
    Wildcard,
    /// Literal value pattern
    Literal(MirLiteral),
    /// Variable binding pattern
    Binding(String),
    /// Enum variant pattern
    Variant {
        enum_name: String,
        variant_name: String,
        payload: Option<Box<MirPattern>>,
    },
    /// Tuple pattern
    Tuple(Vec<MirPattern>),
    /// Struct pattern
    Struct {
        type_name: String,
        fields: Vec<(String, MirPattern)>,
    },
    /// Or pattern (match any of)
    Or(Vec<MirPattern>),
    /// Guard pattern (pattern with condition)
    Guard {
        pattern: Box<MirPattern>,
        condition: VReg,
    },
}

/// Literal value for pattern matching
#[derive(Debug, Clone, PartialEq)]
pub enum MirLiteral {
    Int(i64),
    Float(f64),
    Bool(bool),
    String(String),
    Nil,
}

/// Binding path for extracting values from patterns
#[derive(Debug, Clone, PartialEq)]
pub struct PatternBinding {
    /// Name of the bound variable
    pub name: String,
    /// Path to the value (e.g., [TupleIndex(0), FieldName("x")])
    pub path: Vec<BindingStep>,
}

/// Step in a binding path
#[derive(Debug, Clone, PartialEq)]
pub enum BindingStep {
    /// Tuple index
    TupleIndex(u32),
    /// Struct field
    FieldName(String),
    /// Enum payload
    EnumPayload,
}

/// Part of an f-string for MIR
#[derive(Debug, Clone, PartialEq)]
pub enum FStringPart {
    /// Literal string part
    Literal(String),
    /// Expression value to format
    Expr(VReg),
}

impl HasEffects for MirInst {
    /// Return the effect of this instruction.
    /// Enables compile-time verification of async/nogc properties.
    fn effect(&self) -> Effect {
        match self {
            // Pure computation
            MirInst::ConstInt { .. }
            | MirInst::ConstFloat { .. }
            | MirInst::ConstBool { .. }
            | MirInst::ConstString { .. }
            | MirInst::ConstSymbol { .. }
            | MirInst::Copy { .. }
            | MirInst::BinOp { .. }
            | MirInst::UnaryOp { .. }
            | MirInst::Load { .. }
            | MirInst::Store { .. }
            | MirInst::LocalAddr { .. }
            | MirInst::GetElementPtr { .. }
            | MirInst::IndexGet { .. }
            | MirInst::IndexSet { .. }
            | MirInst::SliceOp { .. }
            | MirInst::FieldGet { .. }
            | MirInst::FieldSet { .. }
            | MirInst::EnumDiscriminant { .. }
            | MirInst::EnumPayload { .. }
            | MirInst::PatternTest { .. }
            | MirInst::PatternBind { .. } => Effect::Compute,

            // Collection allocation (GcAlloc effect)
            MirInst::ArrayLit { .. }
            | MirInst::TupleLit { .. }
            | MirInst::DictLit { .. }
            | MirInst::Spread { .. }
            | MirInst::FStringFormat { .. }
            | MirInst::ClosureCreate { .. }
            | MirInst::StructInit { .. }
            | MirInst::EnumUnit { .. }
            | MirInst::EnumWith { .. }
            | MirInst::OptionSome { .. }
            | MirInst::OptionNone { .. }
            | MirInst::ResultOk { .. }
            | MirInst::ResultErr { .. }
            | MirInst::FutureCreate { .. }
            | MirInst::GeneratorCreate { .. } => Effect::GcAlloc,

            // Function calls - effect depends on target
            MirInst::Call { target, .. } => target.effect(),

            // Indirect call - uses provided effect annotation
            MirInst::IndirectCall { effect, .. } => *effect,

            // Method calls may have side effects
            MirInst::MethodCallStatic { .. }
            | MirInst::MethodCallVirtual { .. }
            | MirInst::BuiltinMethod { .. } => Effect::Io,

            // Explicit effect markers for verification
            MirInst::GcAlloc { .. } => Effect::GcAlloc,
            MirInst::Wait { .. } => Effect::Wait,

            // Blocking operations
            MirInst::Await { .. }
            | MirInst::ActorRecv { .. }
            | MirInst::GeneratorNext { .. }
            | MirInst::TryUnwrap { .. } => Effect::Wait,

            // Non-blocking I/O
            MirInst::ActorSpawn { .. } | MirInst::ActorSend { .. } | MirInst::Yield { .. } => {
                Effect::Io
            }

            // Interpreter fallback (temporary - will be removed)
            MirInst::InterpCall { .. } | MirInst::InterpEval { .. } => Effect::Io,
        }
    }
}

impl MirInst {
    /// Check if this instruction is async (non-blocking).
    pub fn is_async(&self) -> bool {
        self.effect().is_async()
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
    Branch {
        cond: VReg,
        then_block: BlockId,
        else_block: BlockId,
    },

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
            Terminator::Branch {
                then_block,
                else_block,
                ..
            } => vec![*then_block, *else_block],
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
        match std::mem::replace(
            &mut self.state,
            BlockBuildState::Open {
                id: BlockId(0),
                instructions: Vec::new(),
            },
        ) {
            BlockBuildState::Open { id, instructions } => {
                self.state = BlockBuildState::Sealed {
                    id,
                    instructions,
                    terminator,
                };
                Ok(())
            }
            BlockBuildState::Sealed {
                id,
                instructions,
                terminator: old_term,
            } => {
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
            BlockBuildState::Sealed {
                id,
                instructions,
                terminator,
            } => Ok(MirBlock {
                id,
                instructions,
                terminator,
            }),
            BlockBuildState::Open { .. } => Err(BlockBuildError::NotSealed),
        }
    }

    /// Force finalize - use Unreachable if not sealed (for compatibility)
    pub fn finalize_or_unreachable(self) -> MirBlock {
        match self.state {
            BlockBuildState::Sealed {
                id,
                instructions,
                terminator,
            } => MirBlock {
                id,
                instructions,
                terminator,
            },
            BlockBuildState::Open { id, instructions } => MirBlock {
                id,
                instructions,
                terminator: Terminator::Unreachable,
            },
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

    /// Check if this block is async (no blocking operations).
    pub fn is_async(&self) -> bool {
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
    /// Outlined bodies generated from body_block instructions (Actor/Generator/Future).
    /// Maps the original BlockId to the outlined function name.
    pub outlined_bodies: std::collections::HashMap<BlockId, String>,
    next_vreg: u32,
    next_block: u32,
}

impl MirFunction {
    /// Create a simple outlined function name from a base name and block id.
    pub fn outlined_name(&self, block: BlockId) -> String {
        format!("{}_outlined_{}", self.name, block.0)
    }
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
            outlined_bodies: std::collections::HashMap::new(),
            next_vreg: 0,
            next_block: 1,
        }
    }

    /// Create a new MIR function from a boolean public flag.
    /// Helper for backwards compatibility during migration.
    pub fn new_from_bool(name: String, return_type: TypeId, is_public: bool) -> Self {
        let visibility = if is_public {
            Visibility::Public
        } else {
            Visibility::Private
        };
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

    /// Check if this function is async (no blocking operations).
    pub fn is_async(&self) -> bool {
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
        entry
            .instructions
            .push(MirInst::ConstInt { dest: r0, value: 1 });
        entry
            .instructions
            .push(MirInst::ConstInt { dest: r1, value: 2 });
        entry.instructions.push(MirInst::BinOp {
            dest: r2,
            op: BinOp::Add,
            left: r0,
            right: r1,
        });
        entry.terminator = Terminator::Return(Some(r2));

        assert_eq!(entry.instructions.len(), 3);
    }
}

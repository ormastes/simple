//! Effect tracking for formal verification.
//!
//! This module provides explicit effect tracking that maps directly to the
//! Lean 4 formal verification models:
//! - `verification/async_compile/` for blocking operation detection
//! - `verification/nogc_compile/` for GC allocation detection

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

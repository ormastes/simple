//! Effect tracking for formal verification and production use.
//!
//! This module is organized in two sections:
//!
//! ## Section 1: Lean-Aligned Core (for formal verification)
//! Types and functions that map EXACTLY to the Lean 4 formal models:
//! - `AsyncEffect`, `is_async()`, `pipeline_safe()` → `verification/async_compile/`
//! - `NogcInstr`, `nogc()` → `verification/nogc_compile/`
//!
//! ## Section 2: Production Helpers
//! Convenience types for production use that build on the core:
//! - `Effect` - Combined effect type (async + gc concerns)
//! - `EffectSet` - Effect tracking for instruction sequences
//! - `BuiltinFunc`, `CallTarget`, `LocalKind` - Production conveniences
//!
//! When modifying Lean models, update Section 1 to match exactly.
//! Section 2 types are Rust-only conveniences.

//##############################################################################
//# SECTION 1: LEAN-ALIGNED CORE (Formal Verification)
//##############################################################################

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

/// Lean: def is_async (e : Effect) : Bool := match e with | wait => false | compute => true | io => true
pub fn is_async(e: AsyncEffect) -> bool {
    match e {
        AsyncEffect::Wait => false,
        // Explicit: compute and io are async-safe
        AsyncEffect::Compute | AsyncEffect::Io => true,
    }
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

//##############################################################################
//# SECTION 2: PRODUCTION HELPERS (Rust-only conveniences)
//##############################################################################

//==============================================================================
// Effect - Combined type for production use
//==============================================================================

/// Effect marker for instructions (combined for production use).
/// Combines async safety (from AsyncCompile.lean) and GC safety (from NogcCompile.lean)
/// into a single enum for convenient tracking.
///
/// Extended with capability-related effects (Net, Fs, Unsafe) to support
/// the module capability system.
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
    /// Network operation (requires @net capability)
    Net,
    /// Filesystem operation (requires @fs capability)
    Fs,
    /// Unsafe/unchecked operation (requires @unsafe capability)
    Unsafe,
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

    /// Check if this effect is pure (no side effects).
    pub fn is_pure(&self) -> bool {
        matches!(self, Effect::Compute)
    }

    /// Check if this effect requires network capability.
    pub fn is_net(&self) -> bool {
        matches!(self, Effect::Net)
    }

    /// Check if this effect requires filesystem capability.
    pub fn is_fs(&self) -> bool {
        matches!(self, Effect::Fs)
    }

    /// Check if this effect requires unsafe capability.
    pub fn is_unsafe(&self) -> bool {
        matches!(self, Effect::Unsafe)
    }

    /// Convert to AsyncEffect (for Lean model correspondence).
    pub fn to_async(&self) -> AsyncEffect {
        match self {
            Effect::Compute => AsyncEffect::Compute,
            Effect::Io => AsyncEffect::Io,
            Effect::Wait => AsyncEffect::Wait,
            // These are non-blocking, so they map to Compute or Io
            Effect::GcAlloc => AsyncEffect::Compute,
            Effect::Net => AsyncEffect::Io,         // Network is I/O
            Effect::Fs => AsyncEffect::Io,          // Filesystem is I/O
            Effect::Unsafe => AsyncEffect::Compute, // Unsafe is computation
        }
    }

    /// Convert from AST Effect to MIR Effect.
    pub fn from_ast_effect(ast_effect: &simple_parser::ast::Effect) -> Self {
        use simple_parser::ast::Effect as AstEffect;
        match ast_effect {
            AstEffect::Async => Effect::Wait, // Async functions may wait
            AstEffect::Pure => Effect::Compute,
            AstEffect::Io => Effect::Io,
            AstEffect::Net => Effect::Net,
            AstEffect::Fs => Effect::Fs,
            AstEffect::Unsafe => Effect::Unsafe,
            // Verification effects are compile-time only, no runtime effect
            AstEffect::Verify => Effect::Compute,
            AstEffect::Trusted => Effect::Compute,
            AstEffect::Ghost => Effect::Compute, // Ghost is compile-time only
        }
    }

    /// Get the name of this effect for error messages.
    pub fn name(&self) -> &'static str {
        match self {
            Effect::Compute => "compute",
            Effect::Io => "io",
            Effect::Wait => "wait",
            Effect::GcAlloc => "gc_alloc",
            Effect::Net => "net",
            Effect::Fs => "fs",
            Effect::Unsafe => "unsafe",
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

    /// Check if all effects are pure (no side effects).
    pub fn is_pure(&self) -> bool {
        self.effects.iter().all(|e| e.is_pure())
    }

    /// Check if any effect requires network capability.
    pub fn has_net(&self) -> bool {
        self.effects.iter().any(|e| e.is_net())
    }

    /// Check if any effect requires filesystem capability.
    pub fn has_fs(&self) -> bool {
        self.effects.iter().any(|e| e.is_fs())
    }

    /// Check if any effect requires unsafe capability.
    pub fn has_unsafe(&self) -> bool {
        self.effects.iter().any(|e| e.is_unsafe())
    }

    /// Get all unique effect kinds in this set.
    pub fn effect_kinds(&self) -> Vec<Effect> {
        let mut kinds = Vec::new();
        for e in &self.effects {
            if !kinds.contains(e) {
                kinds.push(*e);
            }
        }
        kinds
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
// Builtin Functions (production convenience)
//==============================================================================
// Explicit enumeration of known builtin functions with their effects.
// NOTE: This is a Rust-only convenience type. There is no Lean equivalent.

/// Known builtin functions with statically-known effects.
/// Production convenience for categorizing function calls by effect.
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
    // Network operations
    HttpGet,
    HttpPost,
    TcpConnect,
    TcpListen,
    UdpBind,
    // Filesystem operations
    ReadFile,
    WriteFile,
    OpenFile,
    DeleteFile,
    ListDir,
    CreateDir,
    // Unsafe operations
    UnsafePtr,
    UnsafeDeref,
    UnsafeCast,
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

            BuiltinFunc::HttpGet
            | BuiltinFunc::HttpPost
            | BuiltinFunc::TcpConnect
            | BuiltinFunc::TcpListen
            | BuiltinFunc::UdpBind => Effect::Net,

            BuiltinFunc::ReadFile
            | BuiltinFunc::WriteFile
            | BuiltinFunc::OpenFile
            | BuiltinFunc::DeleteFile
            | BuiltinFunc::ListDir
            | BuiltinFunc::CreateDir => Effect::Fs,

            BuiltinFunc::UnsafePtr | BuiltinFunc::UnsafeDeref | BuiltinFunc::UnsafeCast => {
                Effect::Unsafe
            }
        }
    }

    /// Try to parse a builtin from a string name
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            // Blocking
            "await" => Some(BuiltinFunc::Await),
            "wait" => Some(BuiltinFunc::Wait),
            "join" => Some(BuiltinFunc::Join),
            "recv" => Some(BuiltinFunc::Recv),
            "sleep" => Some(BuiltinFunc::Sleep),
            // GC
            "gc_alloc" => Some(BuiltinFunc::GcAlloc),
            "gc_new" => Some(BuiltinFunc::GcNew),
            "box" => Some(BuiltinFunc::Box),
            // I/O
            "print" => Some(BuiltinFunc::Print),
            "println" => Some(BuiltinFunc::Println),
            "read" => Some(BuiltinFunc::Read),
            "write" => Some(BuiltinFunc::Write),
            "send" => Some(BuiltinFunc::Send),
            "spawn" => Some(BuiltinFunc::Spawn),
            // Network
            "http_get" => Some(BuiltinFunc::HttpGet),
            "http_post" => Some(BuiltinFunc::HttpPost),
            "tcp_connect" => Some(BuiltinFunc::TcpConnect),
            "tcp_listen" => Some(BuiltinFunc::TcpListen),
            "udp_bind" => Some(BuiltinFunc::UdpBind),
            // Filesystem
            "read_file" => Some(BuiltinFunc::ReadFile),
            "write_file" => Some(BuiltinFunc::WriteFile),
            "open_file" => Some(BuiltinFunc::OpenFile),
            "delete_file" => Some(BuiltinFunc::DeleteFile),
            "list_dir" => Some(BuiltinFunc::ListDir),
            "create_dir" => Some(BuiltinFunc::CreateDir),
            // Unsafe
            "unsafe_ptr" => Some(BuiltinFunc::UnsafePtr),
            "unsafe_deref" => Some(BuiltinFunc::UnsafeDeref),
            "unsafe_cast" => Some(BuiltinFunc::UnsafeCast),
            _ => None,
        }
    }

    /// Get the canonical string name
    pub fn name(&self) -> &'static str {
        match self {
            // Blocking
            BuiltinFunc::Await => "await",
            BuiltinFunc::Wait => "wait",
            BuiltinFunc::Join => "join",
            BuiltinFunc::Recv => "recv",
            BuiltinFunc::Sleep => "sleep",
            // GC
            BuiltinFunc::GcAlloc => "gc_alloc",
            BuiltinFunc::GcNew => "gc_new",
            BuiltinFunc::Box => "box",
            // I/O
            BuiltinFunc::Print => "print",
            BuiltinFunc::Println => "println",
            BuiltinFunc::Read => "read",
            BuiltinFunc::Write => "write",
            BuiltinFunc::Send => "send",
            BuiltinFunc::Spawn => "spawn",
            // Network
            BuiltinFunc::HttpGet => "http_get",
            BuiltinFunc::HttpPost => "http_post",
            BuiltinFunc::TcpConnect => "tcp_connect",
            BuiltinFunc::TcpListen => "tcp_listen",
            BuiltinFunc::UdpBind => "udp_bind",
            // Filesystem
            BuiltinFunc::ReadFile => "read_file",
            BuiltinFunc::WriteFile => "write_file",
            BuiltinFunc::OpenFile => "open_file",
            BuiltinFunc::DeleteFile => "delete_file",
            BuiltinFunc::ListDir => "list_dir",
            BuiltinFunc::CreateDir => "create_dir",
            // Unsafe
            BuiltinFunc::UnsafePtr => "unsafe_ptr",
            BuiltinFunc::UnsafeDeref => "unsafe_deref",
            BuiltinFunc::UnsafeCast => "unsafe_cast",
        }
    }
}

//==============================================================================
// Call Target with Effect Information (production convenience)
//==============================================================================
// For more precise effect tracking, calls are tagged with their effect category.
// This allows distinguishing pure computation from I/O and blocking operations.
// NOTE: This is a Rust-only convenience type. There is no Lean equivalent.

/// Call target with effect annotation for production use.
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
    /// Network function - requires @net capability
    Net(String),
    /// Filesystem function - requires @fs capability
    Fs(String),
    /// Unsafe function - requires @unsafe capability
    Unsafe(String),
}

impl CallTarget {
    /// Get the function name.
    pub fn name(&self) -> &str {
        match self {
            CallTarget::Pure(n) => n,
            CallTarget::Io(n) => n,
            CallTarget::Blocking(n) => n,
            CallTarget::GcAllocating(n) => n,
            CallTarget::Net(n) => n,
            CallTarget::Fs(n) => n,
            CallTarget::Unsafe(n) => n,
        }
    }

    /// Get the effect of this call.
    pub fn effect(&self) -> Effect {
        match self {
            CallTarget::Pure(_) => Effect::Compute,
            CallTarget::Io(_) => Effect::Io,
            CallTarget::Blocking(_) => Effect::Wait,
            CallTarget::GcAllocating(_) => Effect::GcAlloc,
            CallTarget::Net(_) => Effect::Net,
            CallTarget::Fs(_) => Effect::Fs,
            CallTarget::Unsafe(_) => Effect::Unsafe,
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

    /// Check if this call requires network capability.
    pub fn is_net(&self) -> bool {
        self.effect().is_net()
    }

    /// Check if this call requires filesystem capability.
    pub fn is_fs(&self) -> bool {
        self.effect().is_fs()
    }

    /// Check if this call requires unsafe capability.
    pub fn is_unsafe(&self) -> bool {
        self.effect().is_unsafe()
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
            // Network functions
            "http_get" | "http_post" | "tcp_connect" | "tcp_listen" | "udp_bind" => {
                CallTarget::Net(name.to_string())
            }
            // Filesystem functions
            "read_file" | "write_file" | "open_file" | "delete_file" | "list_dir"
            | "create_dir" => CallTarget::Fs(name.to_string()),
            // Unsafe functions
            "unsafe_ptr" | "unsafe_deref" | "unsafe_cast" => CallTarget::Unsafe(name.to_string()),
            // Pure functions (default)
            _ => CallTarget::Pure(name.to_string()),
        }
    }
}

//==============================================================================
// Local Variable Kind (production convenience)
//==============================================================================
// Distinguishing parameters from local variables helps with code generation:
// - Parameters have defined values at function entry
// - Locals may be uninitialized until assigned
// NOTE: This is a Rust-only convenience type. There is no Lean equivalent.

/// Distinguishes function parameters from local variables.
/// Production convenience for tracking initialization state.
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

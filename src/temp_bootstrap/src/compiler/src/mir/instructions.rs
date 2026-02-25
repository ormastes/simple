//! MIR instruction definitions.
//!
//! This module defines all MIR instructions, patterns, and related types.

use crate::hir::{BinOp, PointerKind, TypeId, UnaryOp};

use super::effects::{CallTarget, Effect, HasEffects};

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
    // Pointer instructions
    // =========================================================================
    /// Allocate a new pointer wrapping a value
    PointerNew {
        dest: VReg,
        kind: PointerKind,
        value: VReg,
    },

    /// Create a borrow reference (immutable or mutable)
    PointerRef {
        dest: VReg,
        kind: PointerKind, // Borrow or BorrowMut
        source: VReg,
    },

    /// Dereference a pointer to get its value
    PointerDeref {
        dest: VReg,
        pointer: VReg,
        kind: PointerKind,
    },

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

    // =========================================================================
    // Contract instructions (Design by Contract support)
    // =========================================================================
    /// Check a contract condition (precondition, postcondition, or invariant).
    /// Panics with contract violation error if condition is false.
    ContractCheck {
        /// The condition to check (should be boolean)
        condition: VReg,
        /// Type of contract being checked
        kind: ContractKind,
        /// Function name for error message
        func_name: String,
        /// Optional custom error message
        message: Option<String>,
    },

    /// Capture a value at function entry for use in postconditions with old().
    /// The captured value is stored in a temporary slot.
    ContractOldCapture {
        /// Destination for the captured value
        dest: VReg,
        /// The expression value to capture
        value: VReg,
    },
}

/// Kind of contract being checked
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContractKind {
    /// Precondition (in:/requires:) - checked at function entry
    Precondition,
    /// Postcondition (out(ret):/ensures:) - checked on success return
    Postcondition,
    /// Error postcondition (out_err(err):) - checked on error return
    ErrorPostcondition,
    /// Invariant at function entry
    InvariantEntry,
    /// Invariant at function exit
    InvariantExit,
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
            | MirInst::PatternBind { .. }
            | MirInst::ContractOldCapture { .. }
            | MirInst::PointerDeref { .. } => Effect::Compute,

            // Contract checks may panic (Io effect due to potential panic)
            MirInst::ContractCheck { .. } => Effect::Io,

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
            | MirInst::GeneratorCreate { .. }
            | MirInst::PointerNew { .. }
            | MirInst::PointerRef { .. } => Effect::GcAlloc,

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

    /// Destination register if this instruction defines one.
    pub fn dest(&self) -> Option<VReg> {
        match self {
            MirInst::ConstInt { dest, .. }
            | MirInst::ConstFloat { dest, .. }
            | MirInst::ConstBool { dest, .. }
            | MirInst::ConstString { dest, .. }
            | MirInst::ConstSymbol { dest, .. }
            | MirInst::Copy { dest, .. }
            | MirInst::BinOp { dest, .. }
            | MirInst::UnaryOp { dest, .. }
            | MirInst::Load { dest, .. }
            | MirInst::LocalAddr { dest, .. }
            | MirInst::GetElementPtr { dest, .. }
            | MirInst::GcAlloc { dest, .. }
            | MirInst::ArrayLit { dest, .. }
            | MirInst::TupleLit { dest, .. }
            | MirInst::DictLit { dest, .. }
            | MirInst::IndexGet { dest, .. }
            | MirInst::SliceOp { dest, .. }
            | MirInst::Spread { dest, .. }
            | MirInst::FStringFormat { dest, .. }
            | MirInst::ClosureCreate { dest, .. }
            | MirInst::StructInit { dest, .. }
            | MirInst::FieldGet { dest, .. }
            | MirInst::PatternTest { dest, .. }
            | MirInst::PatternBind { dest, .. }
            | MirInst::EnumDiscriminant { dest, .. }
            | MirInst::EnumPayload { dest, .. }
            | MirInst::EnumUnit { dest, .. }
            | MirInst::EnumWith { dest, .. }
            | MirInst::FutureCreate { dest, .. }
            | MirInst::Await { dest, .. }
            | MirInst::ActorSpawn { dest, .. }
            | MirInst::ActorRecv { dest, .. }
            | MirInst::GeneratorCreate { dest, .. }
            | MirInst::GeneratorNext { dest, .. }
            | MirInst::TryUnwrap { dest, .. }
            | MirInst::OptionSome { dest, .. }
            | MirInst::OptionNone { dest, .. }
            | MirInst::ResultOk { dest, .. }
            | MirInst::ResultErr { dest, .. }
            | MirInst::InterpEval { dest, .. }
            | MirInst::ContractOldCapture { dest, .. }
            | MirInst::PointerNew { dest, .. }
            | MirInst::PointerRef { dest, .. }
            | MirInst::PointerDeref { dest, .. } => Some(*dest),
            MirInst::Call { dest, .. }
            | MirInst::IndirectCall { dest, .. }
            | MirInst::Wait { dest, .. }
            | MirInst::InterpCall { dest, .. }
            | MirInst::MethodCallStatic { dest, .. }
            | MirInst::MethodCallVirtual { dest, .. }
            | MirInst::BuiltinMethod { dest, .. } => *dest,
            _ => None,
        }
    }

    /// Registers used by this instruction (excluding destination).
    pub fn uses(&self) -> Vec<VReg> {
        match self {
            MirInst::ConstInt { .. }
            | MirInst::ConstFloat { .. }
            | MirInst::ConstBool { .. }
            | MirInst::ConstString { .. }
            | MirInst::ConstSymbol { .. }
            | MirInst::GcAlloc { .. } => vec![],
            MirInst::Copy { src, .. } => vec![*src],
            MirInst::BinOp { left, right, .. } => vec![*left, *right],
            MirInst::UnaryOp { operand, .. } => vec![*operand],
            MirInst::Load { addr, .. } => vec![*addr],
            MirInst::Store { addr, value, .. } => vec![*addr, *value],
            MirInst::LocalAddr { .. } => vec![],
            MirInst::GetElementPtr { base, index, .. } => vec![*base, *index],
            MirInst::Call { args, .. } => args.clone(),
            MirInst::IndirectCall { callee, args, .. } => {
                let mut v = Vec::with_capacity(1 + args.len());
                v.push(*callee);
                v.extend(args.iter().copied());
                v
            }
            MirInst::Wait { target, .. } => vec![*target],
            MirInst::PatternTest { subject, .. } => vec![*subject],
            MirInst::PatternBind { subject, .. } => vec![*subject],
            MirInst::EnumDiscriminant { value, .. } => vec![*value],
            MirInst::EnumPayload { value, .. } => vec![*value],
            MirInst::EnumUnit { .. } => vec![],
            MirInst::EnumWith { payload, .. } => vec![*payload],
            MirInst::FutureCreate { .. } => vec![],
            MirInst::Await { future, .. } => vec![*future],
            MirInst::ActorSpawn { .. } => vec![],
            MirInst::ActorSend { actor, message } => vec![*actor, *message],
            MirInst::ActorRecv { .. } => vec![],
            MirInst::GeneratorCreate { .. } => vec![],
            MirInst::Yield { value } => vec![*value],
            MirInst::GeneratorNext { generator, .. } => vec![*generator],
            MirInst::TryUnwrap {
                value, error_dest, ..
            } => vec![*value, *error_dest],
            MirInst::OptionSome { value, .. } => vec![*value],
            MirInst::OptionNone { .. } => vec![],
            MirInst::ResultOk { value, .. } => vec![*value],
            MirInst::ResultErr { value, .. } => vec![*value],
            MirInst::TupleLit { elements, .. } | MirInst::ArrayLit { elements, .. } => {
                elements.clone()
            }
            MirInst::DictLit { keys, values, .. } => {
                let mut v = Vec::with_capacity(keys.len() + values.len());
                v.extend(keys.iter().copied());
                v.extend(values.iter().copied());
                v
            }
            MirInst::IndexGet {
                collection, index, ..
            } => vec![*collection, *index],
            MirInst::IndexSet {
                collection,
                index,
                value,
            } => vec![*collection, *index, *value],
            MirInst::SliceOp {
                collection,
                start,
                end,
                step,
                ..
            } => {
                let mut v = vec![*collection];
                if let Some(s) = start {
                    v.push(*s);
                }
                if let Some(e) = end {
                    v.push(*e);
                }
                if let Some(s) = step {
                    v.push(*s);
                }
                v
            }
            MirInst::Spread { source, .. } => vec![*source],
            MirInst::StructInit { field_values, .. } => field_values.clone(),
            MirInst::FieldGet { object, .. } => vec![*object],
            MirInst::FieldSet { object, value, .. } => vec![*object, *value],
            MirInst::MethodCallStatic { receiver, args, .. }
            | MirInst::MethodCallVirtual { receiver, args, .. } => {
                let mut v = Vec::with_capacity(1 + args.len());
                v.push(*receiver);
                v.extend(args.iter().copied());
                v
            }
            MirInst::BuiltinMethod { receiver, args, .. } => {
                let mut v = Vec::with_capacity(1 + args.len());
                v.push(*receiver);
                v.extend(args.iter().copied());
                v
            }
            MirInst::FStringFormat { parts, .. } => {
                let mut v = Vec::new();
                for part in parts {
                    match part {
                        FStringPart::Literal(_) => {}
                        FStringPart::Expr(reg) => v.push(*reg),
                    }
                }
                v
            }
            MirInst::ClosureCreate { captures, .. } => captures.clone(),
            MirInst::InterpCall { args, .. } => args.clone(),
            MirInst::InterpEval { .. } => vec![],
            MirInst::ContractCheck { condition, .. } => vec![*condition],
            MirInst::ContractOldCapture { value, .. } => vec![*value],
            MirInst::PointerNew { value, .. } => vec![*value],
            MirInst::PointerRef { source, .. } => vec![*source],
            MirInst::PointerDeref { pointer, .. } => vec![*pointer],
        }
    }
}

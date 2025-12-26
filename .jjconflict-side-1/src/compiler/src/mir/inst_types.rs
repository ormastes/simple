// =============================================================================
// Supporting types for MIR instructions
// =============================================================================
//
// This section contains all the supporting types, enums, and structs used by
// MIR instructions.

/// Backend preference for parallel operations
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParallelBackend {
    /// CPU parallel threads
    Cpu,
    /// CPU SIMD vectorization
    Simd,
    /// GPU compute
    Gpu,
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

/// Overflow behavior for unit bound checks
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum UnitOverflowBehavior {
    /// Default: panic in debug mode, no-op in release mode
    #[default]
    Default,
    /// Always panic on overflow (checked arithmetic)
    Checked,
    /// Clamp to range bounds
    Saturate,
    /// Wrap around (modulo range)
    Wrap,
}

impl From<crate::hir::HirOverflowBehavior> for UnitOverflowBehavior {
    fn from(hob: crate::hir::HirOverflowBehavior) -> Self {
        match hob {
            crate::hir::HirOverflowBehavior::Default => UnitOverflowBehavior::Default,
            crate::hir::HirOverflowBehavior::Checked => UnitOverflowBehavior::Checked,
            crate::hir::HirOverflowBehavior::Saturate => UnitOverflowBehavior::Saturate,
            crate::hir::HirOverflowBehavior::Wrap => UnitOverflowBehavior::Wrap,
        }
    }
}

/// GPU memory fence scope
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GpuMemoryScope {
    /// Work group local memory only
    WorkGroup,
    /// Global device memory
    Device,
    /// All memory (work group + device)
    All,
}

/// GPU atomic operation type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GpuAtomicOp {
    /// Atomic add
    Add,
    /// Atomic subtract
    Sub,
    /// Atomic minimum
    Min,
    /// Atomic maximum
    Max,
    /// Atomic bitwise AND
    And,
    /// Atomic bitwise OR
    Or,
    /// Atomic bitwise XOR
    Xor,
    /// Atomic exchange
    Xchg,
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

/// Literal value for pattern matching
#[derive(Debug, Clone, PartialEq)]
pub enum MirLiteral {
    Int(i64),
    Float(f64),
    Bool(bool),
    String(String),
    Nil,
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
    /// Union type pattern (matches a specific type in the union)
    Union {
        /// Index of the type in the union's variant list
        type_index: usize,
        /// Optional nested pattern to match the value
        inner: Option<Box<MirPattern>>,
    },
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

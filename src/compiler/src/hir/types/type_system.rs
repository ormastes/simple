use simple_parser::ast::ReferenceCapability;

//==============================================================================
// Signedness (for formal verification)
//==============================================================================
// Replaces boolean `signed` field with explicit enum.
//
// Lean equivalent:
// ```lean
// inductive Signedness
//   | signed
//   | unsigned
// ```

/// Integer signedness - whether the type is signed or unsigned.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum Signedness {
    /// Signed integer (can represent negative values)
    #[default]
    Signed,
    /// Unsigned integer (non-negative values only)
    Unsigned,
}

impl Signedness {
    /// Check if signed
    pub fn is_signed(&self) -> bool {
        matches!(self, Signedness::Signed)
    }

    /// Check if unsigned
    pub fn is_unsigned(&self) -> bool {
        matches!(self, Signedness::Unsigned)
    }
}

//==============================================================================
// Unit Type Constraints (for bit-limited units)
//==============================================================================

/// Overflow behavior for constrained unit types
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum HirOverflowBehavior {
    /// Default behavior (depends on debug/release mode)
    #[default]
    Default,
    /// Panic on overflow (debug mode)
    Checked,
    /// Clamp to range bounds
    Saturate,
    /// Wrap around (modulo)
    Wrap,
}

impl From<simple_parser::ast::OverflowBehavior> for HirOverflowBehavior {
    fn from(ob: simple_parser::ast::OverflowBehavior) -> Self {
        match ob {
            simple_parser::ast::OverflowBehavior::Default => HirOverflowBehavior::Default,
            simple_parser::ast::OverflowBehavior::Checked => HirOverflowBehavior::Checked,
            simple_parser::ast::OverflowBehavior::Saturate => HirOverflowBehavior::Saturate,
            simple_parser::ast::OverflowBehavior::Wrap => HirOverflowBehavior::Wrap,
        }
    }
}

/// Constraints for unit types with bit-limited representations
#[derive(Debug, Clone, PartialEq, Default)]
pub struct HirUnitConstraints {
    /// Valid value range (min, max)
    pub range: Option<(i64, i64)>,
    /// Overflow behavior
    pub overflow: HirOverflowBehavior,
}

/// Unique identifier for types in the HIR
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(pub u32);

//==============================================================================
// Type IDs (for formal verification)
//==============================================================================
// TypeId is a simple newtype over u32 for type identity.
// Built-in types have fixed IDs, custom types are allocated sequentially.
//
// For verification purposes, we distinguish between:
// - Known types (ID < u32::MAX) - have a resolved HirType
// - UNKNOWN (ID == u32::MAX) - type inference failed
//
// IMPORTANT: UNKNOWN should be avoided in new code. Instead:
// - Return Err(LowerError::CannotInferType) for inference failures
// - Use TypeId::VOID for empty/unit types
// - Use explicit type annotations where inference is insufficient

impl TypeId {
    pub const VOID: TypeId = TypeId(0);
    pub const BOOL: TypeId = TypeId(1);
    pub const I8: TypeId = TypeId(2);
    pub const I16: TypeId = TypeId(3);
    pub const I32: TypeId = TypeId(4);
    pub const I64: TypeId = TypeId(5);
    pub const U8: TypeId = TypeId(6);
    pub const U16: TypeId = TypeId(7);
    pub const U32: TypeId = TypeId(8);
    pub const U64: TypeId = TypeId(9);
    pub const F32: TypeId = TypeId(10);
    pub const F64: TypeId = TypeId(11);
    pub const STRING: TypeId = TypeId(12);
    pub const NIL: TypeId = TypeId(13);

    /// DEPRECATED: Use explicit errors instead of UNKNOWN.
    /// This constant exists for backwards compatibility but should be avoided.
    #[deprecated(note = "Use explicit LowerError::CannotInferType instead")]
    pub const UNKNOWN: TypeId = TypeId(u32::MAX);

    /// Check if this is a known (resolved) type.
    pub fn is_known(&self) -> bool {
        self.0 != u32::MAX
    }

    /// Check if this is the UNKNOWN sentinel.
    #[deprecated(note = "Check for errors in lowering instead")]
    pub fn is_unknown(&self) -> bool {
        self.0 == u32::MAX
    }
}

/// Mixin method signature
#[derive(Debug, Clone, PartialEq)]
pub struct HirMixinMethod {
    /// Method name
    pub name: String,
    /// Parameter types
    pub params: Vec<TypeId>,
    /// Return type
    pub ret: TypeId,
}

/// Resolved type information
#[derive(Debug, Clone, PartialEq)]
pub enum HirType {
    Void,
    Bool,
    Int {
        bits: u8,
        signedness: Signedness,
    },
    Float {
        bits: u8,
    },
    String,
    Nil,
    Pointer {
        kind: PointerKind,
        capability: ReferenceCapability,
        inner: TypeId,
    },
    Array {
        element: TypeId,
        size: Option<usize>,
    },
    /// SIMD vector type: vec[N, T] where N is lane count
    Simd {
        lanes: u32,
        element: TypeId,
    },
    Tuple(Vec<TypeId>),
    Function {
        params: Vec<TypeId>,
        ret: TypeId,
    },
    Struct {
        name: String,
        fields: Vec<(String, TypeId)>,
        /// CTR-062: Whether this struct has custom snapshot semantics (#[snapshot])
        has_snapshot: bool,
    },
    Enum {
        name: String,
        variants: Vec<(String, Option<Vec<TypeId>>)>,
    },
    /// Semantic unit type with optional repr constraints
    /// e.g., `_cm:u12 where range: 0..4000, checked`
    UnitType {
        /// Unit name (e.g., "_cm", "_kg")
        name: String,
        /// Underlying representation type
        repr: TypeId,
        /// Bit width (e.g., 12 for u12)
        bits: u8,
        /// Whether the repr is signed
        signedness: Signedness,
        /// Whether the repr is floating point
        is_float: bool,
        /// Constraints (range, overflow behavior)
        constraints: HirUnitConstraints,
    },
    /// Tagged union type: `A | B | C`
    /// Compiles to an enum internally with variants for each type
    Union {
        /// Types that can be held in this union
        variants: Vec<TypeId>,
    },
    /// Mixin type: reusable composition unit
    /// Mixins provide fields and methods that can be composed into classes
    Mixin {
        /// Mixin name
        name: String,
        /// Type parameters (e.g., <T>)
        type_params: Vec<String>,
        /// Fields provided by the mixin
        fields: Vec<(String, TypeId)>,
        /// Method signatures provided by the mixin
        methods: Vec<HirMixinMethod>,
        /// Required trait bounds (e.g., Self: Trait)
        trait_bounds: Vec<String>,
        /// Required methods that the target must implement
        required_methods: Vec<String>,
    },
    Unknown,
}

impl HirType {
    /// Create a signed integer type with the given bit width
    pub fn signed_int(bits: u8) -> Self {
        HirType::Int {
            bits,
            signedness: Signedness::Signed,
        }
    }

    /// Create an unsigned integer type with the given bit width
    pub fn unsigned_int(bits: u8) -> Self {
        HirType::Int {
            bits,
            signedness: Signedness::Unsigned,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PointerKind {
    Unique,
    Shared,
    Weak,
    Handle,
    Borrow,
    BorrowMut,
}

impl From<simple_parser::PointerKind> for PointerKind {
    fn from(pk: simple_parser::PointerKind) -> Self {
        match pk {
            simple_parser::PointerKind::Unique => PointerKind::Unique,
            simple_parser::PointerKind::Shared => PointerKind::Shared,
            simple_parser::PointerKind::Weak => PointerKind::Weak,
            simple_parser::PointerKind::Handle => PointerKind::Handle,
            simple_parser::PointerKind::Borrow => PointerKind::Borrow,
            simple_parser::PointerKind::BorrowMut => PointerKind::BorrowMut,
        }
    }
}

//==============================================================================
// Concurrency Modes (for capability restrictions)
//==============================================================================
// Controls what capabilities are allowed in functions based on their
// concurrency model. This enables safe shared mutable state in lock_base mode
// while preventing it in actor mode (message passing only).

/// Concurrency mode for a function
///
/// Determines what capabilities are allowed and what synchronization
/// primitives are available.
///
/// Lean equivalent:
/// ```lean
/// inductive ConcurrencyMode
///   | actor      -- Message passing only (default)
///   | lock_base  -- Shared mutable state with locks
///   | unsafe     -- Manual control, no guarantees
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum ConcurrencyMode {
    /// Actor mode (default): Message passing only
    /// - Only iso T allowed for transfers
    /// - No mut T (no shared mutable state)
    /// - Safe by construction
    #[default]
    Actor,

    /// Lock-based mode: Shared mutable state with locks
    /// - mut T allowed with proper synchronization
    /// - iso T allowed for transfers
    /// - Requires lock acquisition for mut access
    LockBase,

    /// Unsafe mode: Manual control
    /// - All capabilities allowed
    /// - No compiler-enforced safety
    /// - Used for low-level code
    Unsafe,
}

impl ConcurrencyMode {
    /// Parse from attribute argument string
    pub fn from_attr_arg(arg: &str) -> Option<Self> {
        match arg {
            "actor" => Some(ConcurrencyMode::Actor),
            "lock_base" => Some(ConcurrencyMode::LockBase),
            "unsafe" => Some(ConcurrencyMode::Unsafe),
            _ => None,
        }
    }

    /// Check if mut T is allowed in this mode
    pub fn allows_mut(&self) -> bool {
        match self {
            ConcurrencyMode::Actor => false,
            ConcurrencyMode::LockBase => true,
            ConcurrencyMode::Unsafe => true,
        }
    }

    /// Check if iso T is allowed in this mode (always true)
    pub fn allows_iso(&self) -> bool {
        true // iso T can be transferred in all modes
    }

    /// Get human-readable name
    pub fn name(&self) -> &'static str {
        match self {
            ConcurrencyMode::Actor => "actor",
            ConcurrencyMode::LockBase => "lock_base",
            ConcurrencyMode::Unsafe => "unsafe",
        }
    }
}

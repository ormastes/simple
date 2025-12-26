use simple_parser::ast::{Mutability, ReferenceCapability, Visibility};
use std::collections::HashMap;

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
    Unknown,
}

//==============================================================================
// Struct Layout (for zero-cost field access like C++/Rust)
//==============================================================================

/// Memory layout information for a struct type.
/// Enables zero-cost field access through compile-time offset computation.
///
/// Layout follows C ABI rules:
/// - Fields are aligned to their natural alignment
/// - Struct is padded to its largest member alignment
/// - vtable pointer (if present) is at offset 0
#[derive(Debug, Clone, PartialEq)]
pub struct StructLayout {
    /// Type name
    pub name: String,
    /// Field information: (name, type_id, byte_offset, size)
    pub fields: Vec<FieldLayout>,
    /// Total size of the struct in bytes (including padding)
    pub size: u32,
    /// Alignment requirement in bytes
    pub alignment: u8,
    /// Whether this struct has a vtable pointer (for virtual dispatch)
    pub has_vtable: bool,
    /// Class/struct ID for runtime type identification
    pub type_id: u32,
}

/// Layout information for a single field
#[derive(Debug, Clone, PartialEq)]
pub struct FieldLayout {
    /// Field name
    pub name: String,
    /// Field type
    pub ty: TypeId,
    /// Byte offset from struct start (after vtable if present)
    pub offset: u32,
    /// Size of the field in bytes
    pub size: u32,
}

impl StructLayout {
    /// Create a new struct layout with computed offsets.
    /// Uses C ABI rules for alignment and padding.
    pub fn new(
        name: String,
        fields: &[(String, TypeId)],
        registry: &TypeRegistry,
        has_vtable: bool,
        type_id: u32,
    ) -> Self {
        let mut field_layouts = Vec::with_capacity(fields.len());
        let mut current_offset: u32 = if has_vtable { 8 } else { 0 }; // vtable ptr is 8 bytes
        let mut max_align: u8 = if has_vtable { 8 } else { 1 };

        for (field_name, field_ty) in fields {
            let (size, align) = Self::type_size_align(*field_ty, registry);

            // Align current offset
            let align_u32 = align as u32;
            let padding = (align_u32 - (current_offset % align_u32)) % align_u32;
            current_offset += padding;

            field_layouts.push(FieldLayout {
                name: field_name.clone(),
                ty: *field_ty,
                offset: current_offset,
                size,
            });

            current_offset += size;
            max_align = max_align.max(align);
        }

        // Pad struct to alignment
        let max_align_u32 = max_align as u32;
        let final_padding = (max_align_u32 - (current_offset % max_align_u32)) % max_align_u32;
        let total_size = current_offset + final_padding;

        Self {
            name,
            fields: field_layouts,
            size: total_size,
            alignment: max_align,
            has_vtable,
            type_id,
        }
    }

    /// Get size and alignment for a type (C ABI rules)
    fn type_size_align(ty: TypeId, _registry: &TypeRegistry) -> (u32, u8) {
        match ty {
            TypeId::VOID => (0, 1),
            TypeId::BOOL => (1, 1),
            TypeId::I8 | TypeId::U8 => (1, 1),
            TypeId::I16 | TypeId::U16 => (2, 2),
            TypeId::I32 | TypeId::U32 => (4, 4),
            TypeId::I64 | TypeId::U64 => (8, 8),
            TypeId::F32 => (4, 4),
            TypeId::F64 => (8, 8),
            TypeId::STRING => (8, 8), // Pointer to string
            TypeId::NIL => (8, 8),    // Tagged value
            _ => (8, 8),              // Default to pointer size for custom types
        }
    }

    /// Get field offset by index (O(1))
    pub fn field_offset(&self, index: usize) -> Option<u32> {
        self.fields.get(index).map(|f| f.offset)
    }

    /// Get field offset by name (O(n))
    pub fn field_offset_by_name(&self, name: &str) -> Option<u32> {
        self.fields
            .iter()
            .find(|f| f.name == name)
            .map(|f| f.offset)
    }

    /// Get field index by name
    pub fn field_index(&self, name: &str) -> Option<usize> {
        self.fields.iter().position(|f| f.name == name)
    }
}

/// Registry of struct layouts for all types in a module
#[derive(Debug, Default)]
pub struct LayoutRegistry {
    layouts: HashMap<TypeId, StructLayout>,
    name_to_type: HashMap<String, TypeId>,
    next_type_id: u32,
}

impl LayoutRegistry {
    pub fn new() -> Self {
        Self {
            layouts: HashMap::new(),
            name_to_type: HashMap::new(),
            next_type_id: 0,
        }
    }

    /// Register a struct layout and return its runtime type ID
    pub fn register(&mut self, type_id: TypeId, layout: StructLayout) -> u32 {
        let runtime_id = self.next_type_id;
        self.next_type_id += 1;
        self.name_to_type.insert(layout.name.clone(), type_id);
        self.layouts.insert(type_id, layout);
        runtime_id
    }

    /// Get layout for a type
    pub fn get(&self, type_id: TypeId) -> Option<&StructLayout> {
        self.layouts.get(&type_id)
    }

    /// Get layout by name
    pub fn get_by_name(&self, name: &str) -> Option<&StructLayout> {
        self.name_to_type
            .get(name)
            .and_then(|id| self.layouts.get(id))
    }
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

/// GPU intrinsic function kind for kernel-side operations
include!("gpu_intrinsics.rs");

include!("type_registry.rs");

/// HIR expression with type information attached
#[derive(Debug, Clone, PartialEq)]
pub struct HirExpr {
    pub kind: HirExprKind,
    pub ty: TypeId,
}

impl HirExpr {
    /// Substitute local variable references in an expression (CTR-012)
    ///
    /// This is used for module boundary checking to adapt type invariants
    /// (which reference `self` as local 0) to work with different parameters.
    ///
    /// For example, if an invariant references `self.x > 0` and we want to
    /// check it for parameter `param` at index 2, we substitute local 0 with local 2.
    pub fn substitute_local(&self, from_idx: usize, to_idx: usize) -> HirExpr {
        HirExpr {
            kind: self.kind.substitute_local(from_idx, to_idx),
            ty: self.ty,
        }
    }

    /// Substitute local index 0 (self) with ContractResult for return value checking
    pub fn substitute_self_with_result(&self) -> HirExpr {
        HirExpr {
            kind: self.kind.substitute_self_with_result(),
            ty: self.ty,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum HirExprKind {
    // Literals
    Integer(i64),
    Float(f64),
    String(String),
    Bool(bool),
    Nil,

    // Variables
    Local(usize),   // Index into local variable table
    Global(String), // Global symbol name

    // Operations
    Binary {
        op: BinOp,
        left: Box<HirExpr>,
        right: Box<HirExpr>,
    },
    Unary {
        op: UnaryOp,
        operand: Box<HirExpr>,
    },

    // Function calls
    Call {
        func: Box<HirExpr>,
        args: Vec<HirExpr>,
    },

    // Struct/field access
    FieldAccess {
        receiver: Box<HirExpr>,
        field_index: usize,
    },

    // Array/index access
    Index {
        receiver: Box<HirExpr>,
        index: Box<HirExpr>,
    },

    // Compound literals
    Tuple(Vec<HirExpr>),
    Array(Vec<HirExpr>),
    /// SIMD vector literal: vec[1.0, 2.0, 3.0, 4.0]
    VecLiteral(Vec<HirExpr>),
    StructInit {
        ty: TypeId,
        fields: Vec<HirExpr>,
    },

    // Control flow expressions
    If {
        condition: Box<HirExpr>,
        then_branch: Box<HirExpr>,
        else_branch: Option<Box<HirExpr>>,
    },

    // Memory operations
    Ref(Box<HirExpr>),
    Deref(Box<HirExpr>),
    /// Allocate a new pointer wrapping a value
    /// Created from `new &T(value)` or `new *T(value)` syntax
    PointerNew {
        kind: PointerKind,
        value: Box<HirExpr>,
    },

    // Cast
    Cast {
        expr: Box<HirExpr>,
        target: TypeId,
    },

    // Lambda/closure
    Lambda {
        params: Vec<(String, TypeId)>,
        body: Box<HirExpr>,
        captures: Vec<usize>, // indices of captured locals
    },

    // Async/generator operations
    Yield(Box<HirExpr>),
    GeneratorCreate {
        body: Box<HirExpr>, // lambda body
    },
    FutureCreate {
        body: Box<HirExpr>,
    },
    Await(Box<HirExpr>),
    ActorSpawn {
        body: Box<HirExpr>,
    },

    // Built-in function calls (prelude functions like print, println, etc.)
    BuiltinCall {
        name: String,
        args: Vec<HirExpr>,
    },

    // Contract-specific expressions (Design by Contract support)
    /// Result identifier in postconditions - refers to return value
    /// Used in `out(ret):` and `ensures:` blocks
    ContractResult,
    /// old(expr) in postconditions - refers to value at function entry
    /// The expression is evaluated at function entry and stored for use in postconditions
    ContractOld(Box<HirExpr>),

    // GPU intrinsic operations
    /// GPU intrinsic call (global_id, local_id, barrier, etc.)
    GpuIntrinsic {
        intrinsic: GpuIntrinsicKind,
        args: Vec<HirExpr>,
    },

    /// SIMD neighbor access: array.left_neighbor or array.right_neighbor
    /// Accesses element at (this.index() - 1) or (this.index() + 1)
    NeighborAccess {
        array: Box<HirExpr>,
        direction: NeighborDirection,
    },
}

/// Direction for SIMD neighbor access
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NeighborDirection {
    /// Access element at (this.index() - 1)
    Left,
    /// Access element at (this.index() + 1)
    Right,
}

impl HirExprKind {
    /// Substitute local variable references (CTR-012)
    pub fn substitute_local(&self, from_idx: usize, to_idx: usize) -> HirExprKind {
        match self {
            HirExprKind::Local(idx) if *idx == from_idx => HirExprKind::Local(to_idx),
            HirExprKind::Local(idx) => HirExprKind::Local(*idx),

            // Recursively substitute in nested expressions
            HirExprKind::Binary { op, left, right } => HirExprKind::Binary {
                op: *op,
                left: Box::new(left.substitute_local(from_idx, to_idx)),
                right: Box::new(right.substitute_local(from_idx, to_idx)),
            },
            HirExprKind::Unary { op, operand } => HirExprKind::Unary {
                op: *op,
                operand: Box::new(operand.substitute_local(from_idx, to_idx)),
            },
            HirExprKind::Call { func, args } => HirExprKind::Call {
                func: Box::new(func.substitute_local(from_idx, to_idx)),
                args: args.iter().map(|a| a.substitute_local(from_idx, to_idx)).collect(),
            },
            HirExprKind::FieldAccess { receiver, field_index } => HirExprKind::FieldAccess {
                receiver: Box::new(receiver.substitute_local(from_idx, to_idx)),
                field_index: *field_index,
            },
            HirExprKind::Index { receiver, index } => HirExprKind::Index {
                receiver: Box::new(receiver.substitute_local(from_idx, to_idx)),
                index: Box::new(index.substitute_local(from_idx, to_idx)),
            },
            HirExprKind::Tuple(elements) => HirExprKind::Tuple(
                elements.iter().map(|e| e.substitute_local(from_idx, to_idx)).collect(),
            ),
            HirExprKind::Array(elements) => HirExprKind::Array(
                elements.iter().map(|e| e.substitute_local(from_idx, to_idx)).collect(),
            ),
            HirExprKind::StructInit { ty, fields } => HirExprKind::StructInit {
                ty: *ty,
                fields: fields.iter().map(|f| f.substitute_local(from_idx, to_idx)).collect(),
            },
            HirExprKind::If { condition, then_branch, else_branch } => HirExprKind::If {
                condition: Box::new(condition.substitute_local(from_idx, to_idx)),
                then_branch: Box::new(then_branch.substitute_local(from_idx, to_idx)),
                else_branch: else_branch.as_ref().map(|e| Box::new(e.substitute_local(from_idx, to_idx))),
            },
            HirExprKind::Ref(inner) => HirExprKind::Ref(Box::new(inner.substitute_local(from_idx, to_idx))),
            HirExprKind::Deref(inner) => HirExprKind::Deref(Box::new(inner.substitute_local(from_idx, to_idx))),
            HirExprKind::PointerNew { kind, value } => HirExprKind::PointerNew {
                kind: *kind,
                value: Box::new(value.substitute_local(from_idx, to_idx)),
            },
            HirExprKind::Cast { expr, target } => HirExprKind::Cast {
                expr: Box::new(expr.substitute_local(from_idx, to_idx)),
                target: *target,
            },
            HirExprKind::ContractOld(inner) => HirExprKind::ContractOld(Box::new(inner.substitute_local(from_idx, to_idx))),
            HirExprKind::BuiltinCall { name, args } => HirExprKind::BuiltinCall {
                name: name.clone(),
                args: args.iter().map(|a| a.substitute_local(from_idx, to_idx)).collect(),
            },
            HirExprKind::GpuIntrinsic { intrinsic, args } => HirExprKind::GpuIntrinsic {
                intrinsic: *intrinsic,
                args: args.iter().map(|a| a.substitute_local(from_idx, to_idx)).collect(),
            },

            HirExprKind::NeighborAccess { array, direction } => HirExprKind::NeighborAccess {
                array: Box::new(array.substitute_local(from_idx, to_idx)),
                direction: *direction,
            },

            // Literals and other non-local expressions are unchanged
            _ => self.clone(),
        }
    }

    /// Substitute local index 0 (self) with ContractResult for return value checking (CTR-012)
    pub fn substitute_self_with_result(&self) -> HirExprKind {
        match self {
            HirExprKind::Local(0) => HirExprKind::ContractResult,
            HirExprKind::Local(idx) => HirExprKind::Local(*idx),

            // Recursively substitute in nested expressions
            HirExprKind::Binary { op, left, right } => HirExprKind::Binary {
                op: *op,
                left: Box::new(left.substitute_self_with_result()),
                right: Box::new(right.substitute_self_with_result()),
            },
            HirExprKind::Unary { op, operand } => HirExprKind::Unary {
                op: *op,
                operand: Box::new(operand.substitute_self_with_result()),
            },
            HirExprKind::Call { func, args } => HirExprKind::Call {
                func: Box::new(func.substitute_self_with_result()),
                args: args.iter().map(|a| a.substitute_self_with_result()).collect(),
            },
            HirExprKind::FieldAccess { receiver, field_index } => HirExprKind::FieldAccess {
                receiver: Box::new(receiver.substitute_self_with_result()),
                field_index: *field_index,
            },
            HirExprKind::Index { receiver, index } => HirExprKind::Index {
                receiver: Box::new(receiver.substitute_self_with_result()),
                index: Box::new(index.substitute_self_with_result()),
            },
            HirExprKind::Tuple(elements) => HirExprKind::Tuple(
                elements.iter().map(|e| e.substitute_self_with_result()).collect(),
            ),
            HirExprKind::Array(elements) => HirExprKind::Array(
                elements.iter().map(|e| e.substitute_self_with_result()).collect(),
            ),
            HirExprKind::StructInit { ty, fields } => HirExprKind::StructInit {
                ty: *ty,
                fields: fields.iter().map(|f| f.substitute_self_with_result()).collect(),
            },
            HirExprKind::If { condition, then_branch, else_branch } => HirExprKind::If {
                condition: Box::new(condition.substitute_self_with_result()),
                then_branch: Box::new(then_branch.substitute_self_with_result()),
                else_branch: else_branch.as_ref().map(|e| Box::new(e.substitute_self_with_result())),
            },
            HirExprKind::Ref(inner) => HirExprKind::Ref(Box::new(inner.substitute_self_with_result())),
            HirExprKind::Deref(inner) => HirExprKind::Deref(Box::new(inner.substitute_self_with_result())),
            HirExprKind::PointerNew { kind, value } => HirExprKind::PointerNew {
                kind: *kind,
                value: Box::new(value.substitute_self_with_result()),
            },
            HirExprKind::Cast { expr, target } => HirExprKind::Cast {
                expr: Box::new(expr.substitute_self_with_result()),
                target: *target,
            },
            HirExprKind::ContractOld(inner) => HirExprKind::ContractOld(Box::new(inner.substitute_self_with_result())),
            HirExprKind::BuiltinCall { name, args } => HirExprKind::BuiltinCall {
                name: name.clone(),
                args: args.iter().map(|a| a.substitute_self_with_result()).collect(),
            },
            HirExprKind::GpuIntrinsic { intrinsic, args } => HirExprKind::GpuIntrinsic {
                intrinsic: *intrinsic,
                args: args.iter().map(|a| a.substitute_self_with_result()).collect(),
            },

            HirExprKind::NeighborAccess { array, direction } => HirExprKind::NeighborAccess {
                array: Box::new(array.substitute_self_with_result()),
                direction: *direction,
            },

            // Literals and other expressions are unchanged
            _ => self.clone(),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    FloorDiv,
    // Comparison
    Eq,
    NotEq,
    Lt,
    Gt,
    LtEq,
    GtEq,
    /// Identity comparison (object identity, not value equality)
    Is,
    /// Membership test (element in collection)
    In,
    // Logical
    And,
    Or,
    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
}

impl From<simple_parser::BinOp> for BinOp {
    fn from(op: simple_parser::BinOp) -> Self {
        match op {
            simple_parser::BinOp::Add => BinOp::Add,
            simple_parser::BinOp::Sub => BinOp::Sub,
            simple_parser::BinOp::Mul => BinOp::Mul,
            simple_parser::BinOp::Div => BinOp::Div,
            simple_parser::BinOp::Mod => BinOp::Mod,
            simple_parser::BinOp::Pow => BinOp::Pow,
            simple_parser::BinOp::FloorDiv => BinOp::FloorDiv,
            simple_parser::BinOp::Eq => BinOp::Eq,
            simple_parser::BinOp::NotEq => BinOp::NotEq,
            simple_parser::BinOp::Lt => BinOp::Lt,
            simple_parser::BinOp::Gt => BinOp::Gt,
            simple_parser::BinOp::LtEq => BinOp::LtEq,
            simple_parser::BinOp::GtEq => BinOp::GtEq,
            simple_parser::BinOp::And => BinOp::And,
            simple_parser::BinOp::Or => BinOp::Or,
            simple_parser::BinOp::BitAnd => BinOp::BitAnd,
            simple_parser::BinOp::BitOr => BinOp::BitOr,
            simple_parser::BinOp::BitXor => BinOp::BitXor,
            simple_parser::BinOp::ShiftLeft => BinOp::ShiftLeft,
            simple_parser::BinOp::ShiftRight => BinOp::ShiftRight,
            simple_parser::BinOp::Is => BinOp::Is,
            simple_parser::BinOp::In => BinOp::In,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
    BitNot,
}

impl From<simple_parser::UnaryOp> for UnaryOp {
    fn from(op: simple_parser::UnaryOp) -> Self {
        match op {
            simple_parser::UnaryOp::Neg => UnaryOp::Neg,
            simple_parser::UnaryOp::Not => UnaryOp::Not,
            simple_parser::UnaryOp::BitNot => UnaryOp::BitNot,
            simple_parser::UnaryOp::Ref => UnaryOp::Not, // Handled separately
            simple_parser::UnaryOp::RefMut => UnaryOp::Not, // Handled separately
            simple_parser::UnaryOp::Deref => UnaryOp::Not, // Handled separately
        }
    }
}

/// HIR statement
#[derive(Debug, Clone, PartialEq)]
pub enum HirStmt {
    Let {
        local_index: usize,
        ty: TypeId,
        value: Option<HirExpr>,
    },
    Assign {
        target: HirExpr,
        value: HirExpr,
    },
    Return(Option<HirExpr>),
    Expr(HirExpr),
    If {
        condition: HirExpr,
        then_block: Vec<HirStmt>,
        else_block: Option<Vec<HirStmt>>,
    },
    While {
        condition: HirExpr,
        body: Vec<HirStmt>,
    },
    Loop {
        body: Vec<HirStmt>,
    },
    Break,
    Continue,
}

/// Local variable info
#[derive(Debug, Clone)]
pub struct LocalVar {
    pub name: String,
    pub ty: TypeId,
    pub mutability: Mutability,
    /// Per-parameter DI injection flag (#1013)
    pub inject: bool,
}

impl LocalVar {
    /// Check if this variable is mutable (helper for backwards compatibility)
    pub fn is_mutable(&self) -> bool {
        self.mutability.is_mutable()
    }
}

/// HIR contract clause - a single condition in a contract block
#[derive(Debug, Clone, PartialEq)]
pub struct HirContractClause {
    /// The boolean condition expression
    pub condition: HirExpr,
    /// Optional error message for contract violation
    pub message: Option<String>,
}

/// HIR contract block for function contracts
#[derive(Debug, Clone, Default)]
pub struct HirContract {
    /// Preconditions (in:/requires:) - checked at function entry
    pub preconditions: Vec<HirContractClause>,
    /// Invariants (invariant:) - checked at entry and exit
    pub invariants: Vec<HirContractClause>,
    /// Postconditions (out(ret):/ensures:) - checked on success exit
    pub postconditions: Vec<HirContractClause>,
    /// Binding name for return value in postconditions (default: "ret")
    pub postcondition_binding: Option<String>,
    /// Error postconditions (out_err(err):) - checked on error exit
    pub error_postconditions: Vec<HirContractClause>,
    /// Binding name for error value in error postconditions (default: "err")
    pub error_binding: Option<String>,
    /// Captured "old" values - (local_index, snapshot_index)
    /// These are expressions evaluated at function entry for use in postconditions
    pub old_values: Vec<(usize, HirExpr)>,
}

impl HirContract {
    /// Check if this contract block has any clauses
    pub fn is_empty(&self) -> bool {
        self.preconditions.is_empty()
            && self.invariants.is_empty()
            && self.postconditions.is_empty()
            && self.error_postconditions.is_empty()
    }
}

/// HIR function definition
#[derive(Debug, Clone)]
pub struct HirFunction {
    pub name: String,
    pub params: Vec<LocalVar>,
    pub locals: Vec<LocalVar>,
    pub return_type: TypeId,
    pub body: Vec<HirStmt>,
    pub visibility: Visibility,
    /// Function contract (preconditions, postconditions, invariants)
    pub contract: Option<HirContract>,
    /// Whether this function is marked as pure (no side effects)
    /// Pure functions can be called from contract expressions (CTR-030-032)
    pub is_pure: bool,
    /// Whether this function uses DI constructor injection
    pub inject: bool,
    /// Concurrency mode for this function (actor, lock_base, unsafe)
    pub concurrency_mode: ConcurrencyMode,
    /// Module path where this function is defined (for AOP predicate matching)
    pub module_path: String,
    /// Compile-time attributes (e.g., "inline", "deprecated") for AOP matching
    pub attributes: Vec<String>,
    /// Effect decorators (e.g., "async", "pure", "io") for AOP effect() selector
    pub effects: Vec<String>,
}

impl HirFunction {
    /// Check if this function is public (helper for backwards compatibility)
    pub fn is_public(&self) -> bool {
        self.visibility.is_public()
    }
}

/// Type invariant for struct/class types
#[derive(Debug, Clone, Default)]
pub struct HirTypeInvariant {
    /// Invariant conditions (using 'self' to refer to the instance)
    pub conditions: Vec<HirContractClause>,
}

/// Refined type definition (CTR-020)
///
/// A refined type is a type alias with a predicate that constrains values.
/// Example: `type PosI64 = i64 where self > 0`
#[derive(Debug, Clone)]
pub struct HirRefinedType {
    /// Name of the refined type
    pub name: String,
    /// Base type that is being refined
    pub base_type: TypeId,
    /// Refinement predicate (using 'self' to refer to the value)
    pub predicate: HirExpr,
}

/// CTR-021: Subtype relationship result
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SubtypeResult {
    /// Types are the same - no coercion needed
    Same,
    /// Source is a subtype of target - no runtime check needed (widening)
    /// Example: PosI64 -> i64 (refined to base)
    Subtype,
    /// Target is a subtype of source - runtime check needed (narrowing)
    /// Example: i64 -> PosI64 (base to refined)
    NeedsCheck,
    /// Types are incompatible
    Incompatible,
}

impl HirRefinedType {
    /// CTR-022: Attempt to evaluate a constant predicate at compile time
    ///
    /// Returns Some(true) if the predicate is definitely satisfied,
    /// Some(false) if it's definitely violated, or None if we can't determine.
    pub fn try_const_eval(&self, value: &HirExpr) -> Option<bool> {
        // Simple constant folding for common cases
        match (&self.predicate.kind, &value.kind) {
            // For predicates like `self > 0` with integer constants
            (HirExprKind::Binary { op, left, right }, HirExprKind::Integer(val)) => {
                // Check if predicate is in form: self <op> <const>
                if let (HirExprKind::Local(0), HirExprKind::Integer(bound)) = (&left.kind, &right.kind) {
                    match op {
                        BinOp::Gt => return Some(*val > *bound),
                        BinOp::GtEq => return Some(*val >= *bound),
                        BinOp::Lt => return Some(*val < *bound),
                        BinOp::LtEq => return Some(*val <= *bound),
                        BinOp::Eq => return Some(*val == *bound),
                        BinOp::NotEq => return Some(*val != *bound),
                        _ => {}
                    }
                }
                // Check reversed: <const> <op> self
                if let (HirExprKind::Integer(bound), HirExprKind::Local(0)) = (&left.kind, &right.kind) {
                    match op {
                        BinOp::Gt => return Some(*bound > *val),
                        BinOp::GtEq => return Some(*bound >= *val),
                        BinOp::Lt => return Some(*bound < *val),
                        BinOp::LtEq => return Some(*bound <= *val),
                        BinOp::Eq => return Some(*bound == *val),
                        BinOp::NotEq => return Some(*bound != *val),
                        _ => {}
                    }
                }
            }
            _ => {}
        }
        None
    }
}

// === AOP & Unified Predicates (#1000-1050) ===

/// HIR representation of an AOP advice declaration.
#[derive(Debug, Clone)]
pub struct HirAopAdvice {
    pub predicate_text: String,
    pub advice_function: String,
    pub form: String, // "before", "after_success", "after_error", "around"
    pub priority: i64,
}

/// HIR representation of a DI binding.
#[derive(Debug, Clone)]
pub struct HirDiBinding {
    pub predicate_text: String,
    pub implementation: String,
    pub scope: Option<String>, // "singleton", "transient", "scoped"
    pub priority: i64,
}

/// HIR representation of an architecture rule.
#[derive(Debug, Clone)]
pub struct HirArchRule {
    pub rule_type: String, // "forbid" or "allow"
    pub predicate_text: String,
    pub message: Option<String>,
    pub priority: i64,
}

/// HIR representation of a mock declaration.
#[derive(Debug, Clone)]
pub struct HirMockDecl {
    pub name: String,
    pub trait_name: String,
    pub expectations: Vec<String>,
}

/// HIR representation of an import statement.
#[derive(Debug, Clone)]
pub struct HirImport {
    /// The module path being imported from (e.g., ["crate", "core", "Option"])
    pub from_path: Vec<String>,
    /// The items being imported (name -> optional alias)
    pub items: Vec<(String, Option<String>)>,
    /// Whether this is a glob import (import *)
    pub is_glob: bool,
}

/// HIR module
#[derive(Debug)]
pub struct HirModule {
    pub name: Option<String>,
    pub types: TypeRegistry,
    pub functions: Vec<HirFunction>,
    pub globals: Vec<(String, TypeId)>,
    /// Type invariants: maps type name to its invariant
    pub type_invariants: std::collections::HashMap<String, HirTypeInvariant>,
    /// Refined types: maps refined type name to its definition (CTR-020)
    pub refined_types: std::collections::HashMap<String, HirRefinedType>,
    /// AOP advice declarations (#1000-1050)
    pub aop_advices: Vec<HirAopAdvice>,
    /// DI bindings (#1009-1019)
    pub di_bindings: Vec<HirDiBinding>,
    /// Architecture rules (#1026-1035)
    pub arch_rules: Vec<HirArchRule>,
    /// Mock declarations (#1020-1025)
    pub mock_decls: Vec<HirMockDecl>,
    /// Import statements for dependency tracking
    pub imports: Vec<HirImport>,
}

impl HirModule {
    pub fn new() -> Self {
        Self {
            name: None,
            types: TypeRegistry::new(),
            functions: Vec::new(),
            globals: Vec::new(),
            type_invariants: std::collections::HashMap::new(),
            refined_types: std::collections::HashMap::new(),
            aop_advices: Vec::new(),
            di_bindings: Vec::new(),
            arch_rules: Vec::new(),
            mock_decls: Vec::new(),
            imports: Vec::new(),
        }
    }

    /// Get the type invariant for a type by name
    pub fn get_type_invariant(&self, type_name: &str) -> Option<&HirTypeInvariant> {
        self.type_invariants.get(type_name)
    }

    /// Get the refined type definition by name (CTR-020)
    pub fn get_refined_type(&self, type_name: &str) -> Option<&HirRefinedType> {
        self.refined_types.get(type_name)
    }

    /// CTR-021: Check subtype relationship between two types
    ///
    /// Returns the relationship between `from_type` and `to_type`:
    /// - `Same`: Types are identical
    /// - `Subtype`: from_type is a subtype of to_type (no check needed)
    /// - `NeedsCheck`: Narrowing from base to refined (runtime check needed)
    /// - `Incompatible`: Types are not related
    pub fn check_subtype(&self, from_type: TypeId, to_type: TypeId) -> SubtypeResult {
        if from_type == to_type {
            return SubtypeResult::Same;
        }

        // Check if either type is a refined type
        let from_type_name = self.types.get_type_name(from_type);
        let to_type_name = self.types.get_type_name(to_type);

        // Check refined type relationships
        if let Some(from_name) = from_type_name {
            if let Some(refined) = self.refined_types.get(from_name) {
                // from_type is refined, check if to_type is its base
                if refined.base_type == to_type {
                    // Widening: refined -> base (no check needed)
                    return SubtypeResult::Subtype;
                }
            }
        }

        if let Some(to_name) = to_type_name {
            if let Some(refined) = self.refined_types.get(to_name) {
                // to_type is refined, check if from_type is its base
                if refined.base_type == from_type {
                    // Narrowing: base -> refined (check needed)
                    return SubtypeResult::NeedsCheck;
                }
            }
        }

        // Check through type aliases
        if let Some(from_name) = from_type_name {
            if let Some(from_alias_id) = self.types.lookup(from_name) {
                if from_alias_id == to_type {
                    return SubtypeResult::Same;
                }
            }
        }

        SubtypeResult::Incompatible
    }

    /// CTR-022/CTR-023: Check if a value satisfies a refined type's predicate
    ///
    /// Returns:
    /// - `Ok(true)`: Predicate is provably satisfied at compile time
    /// - `Ok(false)`: Predicate is provably violated at compile time
    /// - `Err(predicate)`: Cannot prove at compile time, need runtime check
    pub fn check_refinement(
        &self,
        type_name: &str,
        value: &HirExpr,
    ) -> Result<bool, HirExpr> {
        if let Some(refined) = self.refined_types.get(type_name) {
            // CTR-022: Try compile-time evaluation
            if let Some(result) = refined.try_const_eval(value) {
                return Ok(result);
            }
            // CTR-023: Can't prove at compile time, return predicate for runtime check
            // Substitute self (local 0) with the actual value
            Err(refined.predicate.clone())
        } else {
            // Not a refined type, always satisfied
            Ok(true)
        }
    }
}

impl Default for HirModule {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_registry_builtins() {
        let registry = TypeRegistry::new();

        assert_eq!(registry.get(TypeId::VOID), Some(&HirType::Void));
        assert_eq!(registry.get(TypeId::BOOL), Some(&HirType::Bool));
        assert_eq!(registry.get(TypeId::I64), Some(&HirType::signed_int(64)));
        assert_eq!(
            registry.get(TypeId::F64),
            Some(&HirType::Float { bits: 64 })
        );
        assert_eq!(registry.get(TypeId::STRING), Some(&HirType::String));
    }

    #[test]
    fn test_type_registry_lookup() {
        let registry = TypeRegistry::new();

        // Primary type names with bit-width
        assert_eq!(registry.lookup("i64"), Some(TypeId::I64));
        assert_eq!(registry.lookup("i32"), Some(TypeId::I32));
        assert_eq!(registry.lookup("f64"), Some(TypeId::F64));
        assert_eq!(registry.lookup("f32"), Some(TypeId::F32));
        assert_eq!(registry.lookup("bool"), Some(TypeId::BOOL));
        assert_eq!(registry.lookup("str"), Some(TypeId::STRING));
        assert_eq!(registry.lookup("Nonexistent"), None);
    }

    #[test]
    fn test_all_numeric_types() {
        let registry = TypeRegistry::new();

        // Signed integers
        assert_eq!(registry.lookup("i8"), Some(TypeId::I8));
        assert_eq!(registry.lookup("i16"), Some(TypeId::I16));
        assert_eq!(registry.lookup("i32"), Some(TypeId::I32));
        assert_eq!(registry.lookup("i64"), Some(TypeId::I64));

        // Unsigned integers
        assert_eq!(registry.lookup("u8"), Some(TypeId::U8));
        assert_eq!(registry.lookup("u16"), Some(TypeId::U16));
        assert_eq!(registry.lookup("u32"), Some(TypeId::U32));
        assert_eq!(registry.lookup("u64"), Some(TypeId::U64));

        // Floats
        assert_eq!(registry.lookup("f32"), Some(TypeId::F32));
        assert_eq!(registry.lookup("f64"), Some(TypeId::F64));
    }

    #[test]
    fn test_type_registry_register() {
        let mut registry = TypeRegistry::new();

        let struct_type = HirType::Struct {
            name: "Point".to_string(),
            fields: vec![
                ("x".to_string(), TypeId::F64),
                ("y".to_string(), TypeId::F64),
            ],
            has_snapshot: false,
        };

        let id = registry.register_named("Point".to_string(), struct_type.clone());
        assert_eq!(registry.get(id), Some(&struct_type));
        assert_eq!(registry.lookup("Point"), Some(id));
    }

    #[test]
    fn test_hir_expr_integer() {
        let expr = HirExpr {
            kind: HirExprKind::Integer(42),
            ty: TypeId::I64,
        };

        assert_eq!(expr.ty, TypeId::I64);
        if let HirExprKind::Integer(n) = expr.kind {
            assert_eq!(n, 42);
        } else {
            panic!("Expected Integer");
        }
    }

    #[test]
    fn test_hir_expr_binary() {
        let left = Box::new(HirExpr {
            kind: HirExprKind::Integer(1),
            ty: TypeId::I64,
        });
        let right = Box::new(HirExpr {
            kind: HirExprKind::Integer(2),
            ty: TypeId::I64,
        });

        let expr = HirExpr {
            kind: HirExprKind::Binary {
                op: BinOp::Add,
                left,
                right,
            },
            ty: TypeId::I64,
        };

        assert_eq!(expr.ty, TypeId::I64);
    }

    #[test]
    fn test_hir_function() {
        let func = HirFunction {
            name: "add".to_string(),
            params: vec![
                LocalVar {
                    name: "a".to_string(),
                    ty: TypeId::I64,
                    mutability: Mutability::Immutable,
                    inject: false,
                },
                LocalVar {
                    name: "b".to_string(),
                    ty: TypeId::I64,
                    mutability: Mutability::Immutable,
                    inject: false,
                },
            ],
            locals: vec![],
            return_type: TypeId::I64,
            body: vec![HirStmt::Return(Some(HirExpr {
                kind: HirExprKind::Binary {
                    op: BinOp::Add,
                    left: Box::new(HirExpr {
                        kind: HirExprKind::Local(0),
                        ty: TypeId::I64,
                    }),
                    right: Box::new(HirExpr {
                        kind: HirExprKind::Local(1),
                        ty: TypeId::I64,
                    }),
                },
                ty: TypeId::I64,
            }))],
            visibility: Visibility::Public,
            contract: None,
            is_pure: false,
            inject: false,
            concurrency_mode: ConcurrencyMode::Actor,
            module_path: String::new(),
            attributes: vec![],
            effects: vec![],
        };

        assert_eq!(func.name, "add");
        assert_eq!(func.params.len(), 2);
        assert_eq!(func.return_type, TypeId::I64);
        assert!(func.is_public());
        assert!(!func.params[0].is_mutable());
    }

    #[test]
    fn test_hir_module() {
        let module = HirModule::new();

        assert!(module.name.is_none());
        assert!(module.functions.is_empty());
        assert!(module.globals.is_empty());
        // Verify builtin types are registered with lowercase names
        assert!(module.types.lookup("i64").is_some());
        assert!(module.types.lookup("bool").is_some());
        assert!(module.types.lookup("str").is_some());
    }
}

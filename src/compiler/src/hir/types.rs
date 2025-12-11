use simple_parser::ast::{Mutability, Visibility};
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
        inner: TypeId,
    },
    Array {
        element: TypeId,
        size: Option<usize>,
    },
    Tuple(Vec<TypeId>),
    Function {
        params: Vec<TypeId>,
        ret: TypeId,
    },
    Struct {
        name: String,
        fields: Vec<(String, TypeId)>,
    },
    Enum {
        name: String,
        variants: Vec<(String, Option<Vec<TypeId>>)>,
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

/// Type ID allocator for formal verification.
///
/// Separates ID allocation from type storage, making allocation semantics explicit:
/// - `alloc()` always returns a fresh ID (monotonically increasing)
/// - No ID reuse is possible
///
/// Lean equivalent:
/// ```lean
/// structure TypeIdAllocator := (next : Nat)
///
/// def alloc (a : TypeIdAllocator) : TypeId × TypeIdAllocator :=
///   (TypeId.mk a.next, { next := a.next + 1 })
/// ```
#[derive(Debug, Clone)]
pub struct TypeIdAllocator {
    next: u32,
}

impl TypeIdAllocator {
    /// Create a new allocator starting after built-in types.
    pub fn new() -> Self {
        Self { next: 14 } // Built-in types 0-13
    }

    /// Create an allocator with a custom starting ID.
    pub fn with_start(start: u32) -> Self {
        Self { next: start }
    }

    /// Allocate a fresh TypeId.
    /// Invariant: returned ID is always unique and greater than any previous allocation.
    pub fn alloc(&mut self) -> TypeId {
        let id = TypeId(self.next);
        self.next += 1;
        id
    }

    /// Get the next ID that would be allocated (for debugging/verification).
    pub fn peek_next(&self) -> u32 {
        self.next
    }
}

impl Default for TypeIdAllocator {
    fn default() -> Self {
        Self::new()
    }
}

/// Type registry that maps TypeId to HirType
#[derive(Debug, Default)]
pub struct TypeRegistry {
    types: HashMap<TypeId, HirType>,
    allocator: TypeIdAllocator,
    name_to_id: HashMap<String, TypeId>,
}

impl TypeRegistry {
    pub fn new() -> Self {
        let mut registry = Self {
            types: HashMap::new(),
            allocator: TypeIdAllocator::new(),
            name_to_id: HashMap::new(),
        };

        // Register built-in types
        registry.types.insert(TypeId::VOID, HirType::Void);
        registry.types.insert(TypeId::BOOL, HirType::Bool);
        registry.types.insert(TypeId::I8, HirType::signed_int(8));
        registry.types.insert(TypeId::I16, HirType::signed_int(16));
        registry.types.insert(TypeId::I32, HirType::signed_int(32));
        registry.types.insert(TypeId::I64, HirType::signed_int(64));
        registry.types.insert(TypeId::U8, HirType::unsigned_int(8));
        registry
            .types
            .insert(TypeId::U16, HirType::unsigned_int(16));
        registry
            .types
            .insert(TypeId::U32, HirType::unsigned_int(32));
        registry
            .types
            .insert(TypeId::U64, HirType::unsigned_int(64));
        registry
            .types
            .insert(TypeId::F32, HirType::Float { bits: 32 });
        registry
            .types
            .insert(TypeId::F64, HirType::Float { bits: 64 });
        registry.types.insert(TypeId::STRING, HirType::String);
        registry.types.insert(TypeId::NIL, HirType::Nil);

        // Register type names (lowercase with bit-width)
        registry.name_to_id.insert("void".to_string(), TypeId::VOID);
        registry.name_to_id.insert("bool".to_string(), TypeId::BOOL);
        registry.name_to_id.insert("i8".to_string(), TypeId::I8);
        registry.name_to_id.insert("i16".to_string(), TypeId::I16);
        registry.name_to_id.insert("i32".to_string(), TypeId::I32);
        registry.name_to_id.insert("i64".to_string(), TypeId::I64);
        registry.name_to_id.insert("u8".to_string(), TypeId::U8);
        registry.name_to_id.insert("u16".to_string(), TypeId::U16);
        registry.name_to_id.insert("u32".to_string(), TypeId::U32);
        registry.name_to_id.insert("u64".to_string(), TypeId::U64);
        registry.name_to_id.insert("f16".to_string(), TypeId::F32); // f16 maps to f32 for now
        registry.name_to_id.insert("f32".to_string(), TypeId::F32);
        registry.name_to_id.insert("f64".to_string(), TypeId::F64);
        registry
            .name_to_id
            .insert("str".to_string(), TypeId::STRING);
        registry.name_to_id.insert("nil".to_string(), TypeId::NIL);

        registry
    }

    pub fn register(&mut self, ty: HirType) -> TypeId {
        let id = self.allocator.alloc();
        self.types.insert(id, ty);
        id
    }

    /// Get the allocator for inspection (useful for verification).
    pub fn allocator(&self) -> &TypeIdAllocator {
        &self.allocator
    }

    pub fn register_named(&mut self, name: String, ty: HirType) -> TypeId {
        let id = self.register(ty);
        self.name_to_id.insert(name, id);
        id
    }

    pub fn get(&self, id: TypeId) -> Option<&HirType> {
        self.types.get(&id)
    }

    pub fn lookup(&self, name: &str) -> Option<TypeId> {
        self.name_to_id.get(name).copied()
    }
}

/// HIR expression with type information attached
#[derive(Debug, Clone, PartialEq)]
pub struct HirExpr {
    pub kind: HirExprKind,
    pub ty: TypeId,
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
}

impl LocalVar {
    /// Check if this variable is mutable (helper for backwards compatibility)
    pub fn is_mutable(&self) -> bool {
        self.mutability.is_mutable()
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
}

impl HirFunction {
    /// Check if this function is public (helper for backwards compatibility)
    pub fn is_public(&self) -> bool {
        self.visibility.is_public()
    }
}

/// HIR module
#[derive(Debug)]
pub struct HirModule {
    pub name: Option<String>,
    pub types: TypeRegistry,
    pub functions: Vec<HirFunction>,
    pub globals: Vec<(String, TypeId)>,
}

impl HirModule {
    pub fn new() -> Self {
        Self {
            name: None,
            types: TypeRegistry::new(),
            functions: Vec::new(),
            globals: Vec::new(),
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
                },
                LocalVar {
                    name: "b".to_string(),
                    ty: TypeId::I64,
                    mutability: Mutability::Immutable,
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

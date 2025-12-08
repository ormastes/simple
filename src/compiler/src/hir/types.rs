use std::collections::HashMap;

/// Unique identifier for types in the HIR
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TypeId(pub u32);

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
    pub const UNKNOWN: TypeId = TypeId(u32::MAX);
}

/// Resolved type information
#[derive(Debug, Clone, PartialEq)]
pub enum HirType {
    Void,
    Bool,
    Int { bits: u8, signed: bool },
    Float { bits: u8 },
    String,
    Nil,
    Pointer { kind: PointerKind, inner: TypeId },
    Array { element: TypeId, size: Option<usize> },
    Tuple(Vec<TypeId>),
    Function { params: Vec<TypeId>, ret: TypeId },
    Struct { name: String, fields: Vec<(String, TypeId)> },
    Enum { name: String, variants: Vec<(String, Option<Vec<TypeId>>)> },
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PointerKind {
    Unique,
    Shared,
    Weak,
    Handle,
}

impl From<simple_parser::PointerKind> for PointerKind {
    fn from(pk: simple_parser::PointerKind) -> Self {
        match pk {
            simple_parser::PointerKind::Unique => PointerKind::Unique,
            simple_parser::PointerKind::Shared => PointerKind::Shared,
            simple_parser::PointerKind::Weak => PointerKind::Weak,
            simple_parser::PointerKind::Handle => PointerKind::Handle,
        }
    }
}

/// Type registry that maps TypeId to HirType
#[derive(Debug, Default)]
pub struct TypeRegistry {
    types: HashMap<TypeId, HirType>,
    next_id: u32,
    name_to_id: HashMap<String, TypeId>,
}

impl TypeRegistry {
    pub fn new() -> Self {
        let mut registry = Self {
            types: HashMap::new(),
            next_id: 14, // Start after built-in types
            name_to_id: HashMap::new(),
        };

        // Register built-in types
        registry.types.insert(TypeId::VOID, HirType::Void);
        registry.types.insert(TypeId::BOOL, HirType::Bool);
        registry.types.insert(TypeId::I8, HirType::Int { bits: 8, signed: true });
        registry.types.insert(TypeId::I16, HirType::Int { bits: 16, signed: true });
        registry.types.insert(TypeId::I32, HirType::Int { bits: 32, signed: true });
        registry.types.insert(TypeId::I64, HirType::Int { bits: 64, signed: true });
        registry.types.insert(TypeId::U8, HirType::Int { bits: 8, signed: false });
        registry.types.insert(TypeId::U16, HirType::Int { bits: 16, signed: false });
        registry.types.insert(TypeId::U32, HirType::Int { bits: 32, signed: false });
        registry.types.insert(TypeId::U64, HirType::Int { bits: 64, signed: false });
        registry.types.insert(TypeId::F32, HirType::Float { bits: 32 });
        registry.types.insert(TypeId::F64, HirType::Float { bits: 64 });
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
        registry.name_to_id.insert("str".to_string(), TypeId::STRING);
        registry.name_to_id.insert("nil".to_string(), TypeId::NIL);

        registry
    }

    pub fn register(&mut self, ty: HirType) -> TypeId {
        let id = TypeId(self.next_id);
        self.next_id += 1;
        self.types.insert(id, ty);
        id
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
    Local(usize),      // Index into local variable table
    Global(String),    // Global symbol name

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
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Arithmetic
    Add, Sub, Mul, Div, Mod, Pow, FloorDiv,
    // Comparison
    Eq, NotEq, Lt, Gt, LtEq, GtEq,
    // Logical
    And, Or,
    // Bitwise
    BitAnd, BitOr, BitXor, ShiftLeft, ShiftRight,
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
            simple_parser::BinOp::Is => BinOp::Eq, // Approximate
            simple_parser::BinOp::In => BinOp::Eq, // Approximate - needs special handling
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
    pub is_mutable: bool,
}

/// HIR function definition
#[derive(Debug, Clone)]
pub struct HirFunction {
    pub name: String,
    pub params: Vec<LocalVar>,
    pub locals: Vec<LocalVar>,
    pub return_type: TypeId,
    pub body: Vec<HirStmt>,
    pub is_public: bool,
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
        assert_eq!(registry.get(TypeId::I64), Some(&HirType::Int { bits: 64, signed: true }));
        assert_eq!(registry.get(TypeId::F64), Some(&HirType::Float { bits: 64 }));
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
                LocalVar { name: "a".to_string(), ty: TypeId::I64, is_mutable: false },
                LocalVar { name: "b".to_string(), ty: TypeId::I64, is_mutable: false },
            ],
            locals: vec![],
            return_type: TypeId::I64,
            body: vec![
                HirStmt::Return(Some(HirExpr {
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
                })),
            ],
            is_public: true,
        };

        assert_eq!(func.name, "add");
        assert_eq!(func.params.len(), 2);
        assert_eq!(func.return_type, TypeId::I64);
    }

    #[test]
    fn test_hir_module() {
        let module = HirModule::new();

        assert!(module.name.is_none());
        assert!(module.functions.is_empty());
        assert!(module.globals.is_empty());
        assert!(module.types.lookup("Int").is_some());
    }
}

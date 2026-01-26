use super::*;

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

    /// Method call with dispatch mode
    /// Static dispatch: direct call to monomorphized function
    /// Dynamic dispatch: vtable lookup at runtime
    MethodCall {
        receiver: Box<HirExpr>,
        method: String,
        args: Vec<HirExpr>,
        dispatch: DispatchMode,
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
    /// Array repeat: [value; count] - creates array with count copies of value
    ArrayRepeat {
        value: Box<HirExpr>,
        count: Box<HirExpr>,
    },
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

/// Dispatch mode for method calls - determines static vs dynamic dispatch
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DispatchMode {
    /// Static dispatch - monomorphized call, direct function invocation
    /// Used when there's a `bind Interface = ImplType` declaration
    Static,
    /// Dynamic dispatch - vtable lookup at runtime
    /// Default behavior when no binding exists
    Dynamic,
}

impl Default for DispatchMode {
    fn default() -> Self {
        DispatchMode::Dynamic
    }
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
            HirExprKind::MethodCall {
                receiver,
                method,
                args,
                dispatch,
            } => HirExprKind::MethodCall {
                receiver: Box::new(receiver.substitute_local(from_idx, to_idx)),
                method: method.clone(),
                args: args.iter().map(|a| a.substitute_local(from_idx, to_idx)).collect(),
                dispatch: *dispatch,
            },
            HirExprKind::FieldAccess { receiver, field_index } => HirExprKind::FieldAccess {
                receiver: Box::new(receiver.substitute_local(from_idx, to_idx)),
                field_index: *field_index,
            },
            HirExprKind::Index { receiver, index } => HirExprKind::Index {
                receiver: Box::new(receiver.substitute_local(from_idx, to_idx)),
                index: Box::new(index.substitute_local(from_idx, to_idx)),
            },
            HirExprKind::Tuple(elements) => {
                HirExprKind::Tuple(elements.iter().map(|e| e.substitute_local(from_idx, to_idx)).collect())
            }
            HirExprKind::Array(elements) => {
                HirExprKind::Array(elements.iter().map(|e| e.substitute_local(from_idx, to_idx)).collect())
            }
            HirExprKind::StructInit { ty, fields } => HirExprKind::StructInit {
                ty: *ty,
                fields: fields.iter().map(|f| f.substitute_local(from_idx, to_idx)).collect(),
            },
            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => HirExprKind::If {
                condition: Box::new(condition.substitute_local(from_idx, to_idx)),
                then_branch: Box::new(then_branch.substitute_local(from_idx, to_idx)),
                else_branch: else_branch
                    .as_ref()
                    .map(|e| Box::new(e.substitute_local(from_idx, to_idx))),
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
            HirExprKind::ContractOld(inner) => {
                HirExprKind::ContractOld(Box::new(inner.substitute_local(from_idx, to_idx)))
            }
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
            HirExprKind::MethodCall {
                receiver,
                method,
                args,
                dispatch,
            } => HirExprKind::MethodCall {
                receiver: Box::new(receiver.substitute_self_with_result()),
                method: method.clone(),
                args: args.iter().map(|a| a.substitute_self_with_result()).collect(),
                dispatch: *dispatch,
            },
            HirExprKind::FieldAccess { receiver, field_index } => HirExprKind::FieldAccess {
                receiver: Box::new(receiver.substitute_self_with_result()),
                field_index: *field_index,
            },
            HirExprKind::Index { receiver, index } => HirExprKind::Index {
                receiver: Box::new(receiver.substitute_self_with_result()),
                index: Box::new(index.substitute_self_with_result()),
            },
            HirExprKind::Tuple(elements) => {
                HirExprKind::Tuple(elements.iter().map(|e| e.substitute_self_with_result()).collect())
            }
            HirExprKind::Array(elements) => {
                HirExprKind::Array(elements.iter().map(|e| e.substitute_self_with_result()).collect())
            }
            HirExprKind::StructInit { ty, fields } => HirExprKind::StructInit {
                ty: *ty,
                fields: fields.iter().map(|f| f.substitute_self_with_result()).collect(),
            },
            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => HirExprKind::If {
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
    MatMul, // @ operator for matrix multiplication (Simple Math #1930-#1939)
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
    AndSuspend,
    OrSuspend,
    // Bitwise
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
    PipeForward,
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
            simple_parser::BinOp::MatMul => BinOp::MatMul, // Simple Math #1930-#1939
            simple_parser::BinOp::Eq => BinOp::Eq,
            simple_parser::BinOp::NotEq => BinOp::NotEq,
            simple_parser::BinOp::Lt => BinOp::Lt,
            simple_parser::BinOp::Gt => BinOp::Gt,
            simple_parser::BinOp::LtEq => BinOp::LtEq,
            simple_parser::BinOp::GtEq => BinOp::GtEq,
            simple_parser::BinOp::And => BinOp::And,
            simple_parser::BinOp::Or => BinOp::Or,
            simple_parser::BinOp::AndSuspend => BinOp::AndSuspend,
            simple_parser::BinOp::OrSuspend => BinOp::OrSuspend,
            simple_parser::BinOp::BitAnd => BinOp::BitAnd,
            simple_parser::BinOp::BitOr => BinOp::BitOr,
            simple_parser::BinOp::BitXor => BinOp::BitXor,
            simple_parser::BinOp::ShiftLeft => BinOp::ShiftLeft,
            simple_parser::BinOp::ShiftRight => BinOp::ShiftRight,
            simple_parser::BinOp::Is => BinOp::Is,
            simple_parser::BinOp::In => BinOp::In,
            simple_parser::BinOp::PipeForward => BinOp::PipeForward,
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
            simple_parser::UnaryOp::ChannelRecv => UnaryOp::Not, // Handled separately
            simple_parser::UnaryOp::Move => UnaryOp::Not, // Handled separately - move is semantic marker only
        }
    }
}

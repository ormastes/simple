//! AST Node Accessor FFI
//!
//! Provides opaque handle-based access to AST nodes from Simple code.
//! AST nodes are stored in a thread-local registry and accessed via i64 handles.
//! This avoids serializing/deserializing entire AST trees across the FFI boundary.
//!
//! ## Handle Lifecycle
//! - Handles are created when AST nodes are registered (e.g., during parsing or eval)
//! - Simple code uses handles to inspect node structure
//! - Handles are freed explicitly or when the registry is cleared

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use simple_parser::ast::{Argument, BinOp, Block, Expr, FunctionDef, MatchArm, Node, Parameter, Pattern, UnaryOp};
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};

// ============================================================================
// Handle Registry
// ============================================================================

/// Global handle counter (monotonically increasing, never reused)
static NEXT_HANDLE: AtomicI64 = AtomicI64::new(1);

fn next_handle() -> i64 {
    NEXT_HANDLE.fetch_add(1, Ordering::Relaxed)
}

/// Thread-local registry for AST expression handles
thread_local! {
    static EXPR_REGISTRY: RefCell<HashMap<i64, Expr>> = RefCell::new(HashMap::new());
    static NODE_REGISTRY: RefCell<HashMap<i64, Node>> = RefCell::new(HashMap::new());
    static PATTERN_REGISTRY: RefCell<HashMap<i64, Pattern>> = RefCell::new(HashMap::new());
    static BLOCK_REGISTRY: RefCell<HashMap<i64, Block>> = RefCell::new(HashMap::new());
    static FUNCDEF_REGISTRY: RefCell<HashMap<i64, FunctionDef>> = RefCell::new(HashMap::new());
    static MATCHARM_REGISTRY: RefCell<HashMap<i64, MatchArm>> = RefCell::new(HashMap::new());
    static PARAM_REGISTRY: RefCell<HashMap<i64, Parameter>> = RefCell::new(HashMap::new());
    static ARG_REGISTRY: RefCell<HashMap<i64, Argument>> = RefCell::new(HashMap::new());
}

// ============================================================================
// Public API: Register nodes into registry (called from Rust side)
// ============================================================================

/// Register an Expr and return its handle
pub fn register_expr(expr: Expr) -> i64 {
    let handle = next_handle();
    EXPR_REGISTRY.with(|r| r.borrow_mut().insert(handle, expr));
    handle
}

/// Register a Node and return its handle
pub fn register_node(node: Node) -> i64 {
    let handle = next_handle();
    NODE_REGISTRY.with(|r| r.borrow_mut().insert(handle, node));
    handle
}

/// Register a Pattern and return its handle
pub fn register_pattern(pattern: Pattern) -> i64 {
    let handle = next_handle();
    PATTERN_REGISTRY.with(|r| r.borrow_mut().insert(handle, pattern));
    handle
}

/// Register a Block and return its handle
pub fn register_block(block: Block) -> i64 {
    let handle = next_handle();
    BLOCK_REGISTRY.with(|r| r.borrow_mut().insert(handle, block));
    handle
}

/// Register a FunctionDef and return its handle
pub fn register_funcdef(funcdef: FunctionDef) -> i64 {
    let handle = next_handle();
    FUNCDEF_REGISTRY.with(|r| r.borrow_mut().insert(handle, funcdef));
    handle
}

/// Register a MatchArm and return its handle
pub fn register_matcharm(arm: MatchArm) -> i64 {
    let handle = next_handle();
    MATCHARM_REGISTRY.with(|r| r.borrow_mut().insert(handle, arm));
    handle
}

/// Register a Parameter and return its handle
pub fn register_param(param: Parameter) -> i64 {
    let handle = next_handle();
    PARAM_REGISTRY.with(|r| r.borrow_mut().insert(handle, param));
    handle
}

/// Register an Argument and return its handle
pub fn register_arg(arg: Argument) -> i64 {
    let handle = next_handle();
    ARG_REGISTRY.with(|r| r.borrow_mut().insert(handle, arg));
    handle
}

// ============================================================================
// Helper: extract handle from args
// ============================================================================

fn get_handle(args: &[Value], index: usize, name: &str) -> Result<i64, CompileError> {
    args.get(index)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                format!("{} expects argument at index {}", name, index),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()
}

fn get_string_arg(args: &[Value], index: usize, name: &str) -> Result<String, CompileError> {
    match args.get(index) {
        Some(Value::Str(s)) => Ok(s.clone()),
        _ => Err(CompileError::semantic_with_context(
            format!("{} expects string argument at index {}", name, index),
            ErrorContext::new().with_code(codes::TYPE_MISMATCH),
        )),
    }
}

fn invalid_handle(name: &str, handle: i64) -> CompileError {
    CompileError::semantic_with_context(
        format!("{}: invalid handle {}", name, handle),
        ErrorContext::new().with_code(codes::INVALID_OPERATION),
    )
}

// ============================================================================
// Expression Accessors (FFI functions callable from Simple)
// ============================================================================

/// Get the tag/kind of an expression as a string.
/// Returns: "Integer", "Float", "String", "Bool", "Nil", "Identifier", "Binary",
///          "Unary", "Call", "MethodCall", "FieldAccess", "Index", "If", "Match",
///          "Lambda", "Array", "Dict", "Tuple", "StructInit", "Try", "Coalesce",
///          "Range", "Slice", "DoBlock", "FString", etc.
pub fn rt_ast_expr_tag(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_tag")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_tag", handle))?;
        let tag = match expr {
            Expr::Integer(_) => "Integer",
            Expr::Float(_) => "Float",
            Expr::TypedInteger(_, _) => "TypedInteger",
            Expr::TypedFloat(_, _) => "TypedFloat",
            Expr::String(_) => "String",
            Expr::TypedString(_, _) => "TypedString",
            Expr::FString { .. } => "FString",
            Expr::Bool(_) => "Bool",
            Expr::Nil => "Nil",
            Expr::Symbol(_) => "Symbol",
            Expr::Identifier(_) => "Identifier",
            Expr::Path(_) => "Path",
            Expr::Binary { .. } => "Binary",
            Expr::Unary { .. } => "Unary",
            Expr::Call { .. } => "Call",
            Expr::MethodCall { .. } => "MethodCall",
            Expr::FieldAccess { .. } => "FieldAccess",
            Expr::Index { .. } => "Index",
            Expr::TupleIndex { .. } => "TupleIndex",
            Expr::Lambda { .. } => "Lambda",
            Expr::If { .. } => "If",
            Expr::Match { .. } => "Match",
            Expr::Tuple(_) => "Tuple",
            Expr::Array(_) => "Array",
            Expr::ArrayRepeat { .. } => "ArrayRepeat",
            Expr::Dict(_) => "Dict",
            Expr::ListComprehension { .. } => "ListComprehension",
            Expr::DictComprehension { .. } => "DictComprehension",
            Expr::Slice { .. } => "Slice",
            Expr::Spread(_) => "Spread",
            Expr::DictSpread(_) => "DictSpread",
            Expr::StructInit { .. } => "StructInit",
            Expr::Spawn(_) => "Spawn",
            Expr::Go { .. } => "Go",
            Expr::Await(_) => "Await",
            Expr::Yield(_) => "Yield",
            Expr::New { .. } => "New",
            Expr::Cast { .. } => "Cast",
            Expr::Range { .. } => "Range",
            Expr::FunctionalUpdate { .. } => "FunctionalUpdate",
            Expr::MacroInvocation { .. } => "MacroInvocation",
            Expr::Try(_) => "Try",
            Expr::ExistsCheck(_) => "ExistsCheck",
            Expr::UnwrapOr { .. } => "UnwrapOr",
            Expr::UnwrapElse { .. } => "UnwrapElse",
            Expr::UnwrapOrReturn(_) => "UnwrapOrReturn",
            Expr::CastOr { .. } => "CastOr",
            Expr::CastElse { .. } => "CastElse",
            Expr::CastOrReturn { .. } => "CastOrReturn",
            Expr::Coalesce { .. } => "Coalesce",
            Expr::OptionalChain { .. } => "OptionalChain",
            Expr::OptionalMethodCall { .. } => "OptionalMethodCall",
            Expr::ContractResult => "ContractResult",
            Expr::ContractOld(_) => "ContractOld",
            Expr::Forall { .. } => "Forall",
            Expr::Exists { .. } => "Exists",
            Expr::DoBlock(_) => "DoBlock",
            Expr::I18nString { .. } => "I18nString",
            Expr::I18nTemplate { .. } => "I18nTemplate",
            Expr::I18nRef(_) => "I18nRef",
            Expr::VecLiteral(_) => "VecLiteral",
            Expr::GridLiteral { .. } => "GridLiteral",
            Expr::TensorLiteral { .. } => "TensorLiteral",
            Expr::BlockExpr { .. } => "BlockExpr",
            Expr::Atom(_) => "Atom",
            Expr::VolatileAccess { .. } => "VolatileAccess",
            _ => "UnknownExpr",
        };
        Ok(Value::Str(tag.to_string()))
    })
}

/// Get the i64 value from an Integer expression
pub fn rt_ast_expr_int_value(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_int_value")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_int_value", handle))?;
        match expr {
            Expr::Integer(i) => Ok(Value::Int(*i)),
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_int_value: not an Integer expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the f64 value from a Float expression
pub fn rt_ast_expr_float_value(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_float_value")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_float_value", handle))?;
        match expr {
            Expr::Float(f) => Ok(Value::Float(*f)),
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_float_value: not a Float expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the string value from a String expression
pub fn rt_ast_expr_string_value(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_string_value")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_string_value", handle))?;
        match expr {
            Expr::String(s) => Ok(Value::Str(s.clone())),
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_string_value: not a String expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the bool value from a Bool expression
pub fn rt_ast_expr_bool_value(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_bool_value")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_bool_value", handle))?;
        match expr {
            Expr::Bool(b) => Ok(Value::Bool(*b)),
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_bool_value: not a Bool expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the identifier name from an Identifier expression
pub fn rt_ast_expr_ident_name(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_ident_name")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_ident_name", handle))?;
        match expr {
            Expr::Identifier(name) => Ok(Value::Str(name.clone())),
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_ident_name: not an Identifier expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the operator string from a Binary expression.
/// Returns: "+", "-", "*", "/", "%", "**", "==", "!=", "<", ">", "<=", ">=",
///          "and", "or", "&", "|", "^", "<<", ">>", "is", "in", "not_in", "|>", "//"
pub fn rt_ast_expr_binary_op(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_binary_op")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_binary_op", handle))?;
        match expr {
            Expr::Binary { op, .. } => {
                let s = match op {
                    BinOp::Add => "+",
                    BinOp::Sub => "-",
                    BinOp::Mul => "*",
                    BinOp::Div => "/",
                    BinOp::Mod => "%",
                    BinOp::Pow => "**",
                    BinOp::MatMul => "@",
                    BinOp::Eq => "==",
                    BinOp::NotEq => "!=",
                    BinOp::Lt => "<",
                    BinOp::Gt => ">",
                    BinOp::LtEq => "<=",
                    BinOp::GtEq => ">=",
                    BinOp::And => "and",
                    BinOp::Or => "or",
                    BinOp::AndSuspend => "and_suspend",
                    BinOp::OrSuspend => "or_suspend",
                    BinOp::BitAnd => "&",
                    BinOp::BitOr => "|",
                    BinOp::BitXor => "^",
                    BinOp::ShiftLeft => "<<",
                    BinOp::ShiftRight => ">>",
                    BinOp::Is => "is",
                    BinOp::In => "in",
                    BinOp::NotIn => "not_in",
                    BinOp::PipeForward => "|>",
                    BinOp::Parallel => "//",
                };
                Ok(Value::Str(s.to_string()))
            }
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_binary_op: not a Binary expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the left operand of a Binary expression (returns handle to child expr)
pub fn rt_ast_expr_binary_left(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_binary_left")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_binary_left", handle))?;
        match expr {
            Expr::Binary { left, .. } => {
                let child_handle = register_expr(*left.clone());
                Ok(Value::Int(child_handle))
            }
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_binary_left: not a Binary expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the right operand of a Binary expression (returns handle to child expr)
pub fn rt_ast_expr_binary_right(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_binary_right")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_binary_right", handle))?;
        match expr {
            Expr::Binary { right, .. } => {
                let child_handle = register_expr(*right.clone());
                Ok(Value::Int(child_handle))
            }
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_binary_right: not a Binary expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the unary operator string from a Unary expression
pub fn rt_ast_expr_unary_op(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_unary_op")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_unary_op", handle))?;
        match expr {
            Expr::Unary { op, .. } => {
                let s = match op {
                    UnaryOp::Neg => "-",
                    UnaryOp::Not => "not",
                    UnaryOp::BitNot => "~",
                    UnaryOp::Ref => "&",
                    UnaryOp::RefMut => "&mut",
                    UnaryOp::Deref => "*",
                    UnaryOp::ChannelRecv => "<-",
                    UnaryOp::Move => "move",
                };
                Ok(Value::Str(s.to_string()))
            }
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_unary_op: not a Unary expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the operand of a Unary expression (returns handle)
pub fn rt_ast_expr_unary_operand(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_unary_operand")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_unary_operand", handle))?;
        match expr {
            Expr::Unary { operand, .. } => {
                let child_handle = register_expr(*operand.clone());
                Ok(Value::Int(child_handle))
            }
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_unary_operand: not a Unary expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the callee of a Call expression (returns handle to callee expr)
pub fn rt_ast_expr_call_callee(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_call_callee")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_call_callee", handle))?;
        match expr {
            Expr::Call { callee, .. } => {
                let child_handle = register_expr(*callee.clone());
                Ok(Value::Int(child_handle))
            }
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_call_callee: not a Call expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the number of arguments in a Call expression
pub fn rt_ast_expr_call_arg_count(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_call_arg_count")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_call_arg_count", handle))?;
        match expr {
            Expr::Call { args: call_args, .. } => Ok(Value::Int(call_args.len() as i64)),
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_call_arg_count: not a Call expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the i-th argument of a Call expression (returns handle to Argument)
pub fn rt_ast_expr_call_arg(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_call_arg")?;
    let index = get_handle(args, 1, "rt_ast_expr_call_arg")? as usize;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_call_arg", handle))?;
        match expr {
            Expr::Call { args: call_args, .. } => {
                let arg = call_args.get(index).ok_or_else(|| {
                    CompileError::semantic_with_context(
                        format!(
                            "rt_ast_expr_call_arg: index {} out of bounds ({})",
                            index,
                            call_args.len()
                        ),
                        ErrorContext::new().with_code(codes::INDEX_OUT_OF_BOUNDS),
                    )
                })?;
                let arg_handle = register_arg(arg.clone());
                Ok(Value::Int(arg_handle))
            }
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_call_arg: not a Call expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the value expression from an Argument handle (returns handle to expr)
pub fn rt_ast_arg_value(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_arg_value")?;
    ARG_REGISTRY.with(|r| {
        let reg = r.borrow();
        let arg = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_arg_value", handle))?;
        let expr_handle = register_expr(arg.value.clone());
        Ok(Value::Int(expr_handle))
    })
}

/// Get the optional name from an Argument handle (returns string or nil)
pub fn rt_ast_arg_name(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_arg_name")?;
    ARG_REGISTRY.with(|r| {
        let reg = r.borrow();
        let arg = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_arg_name", handle))?;
        match &arg.name {
            Some(name) => Ok(Value::Str(name.clone())),
            None => Ok(Value::Nil),
        }
    })
}

/// Get receiver of a MethodCall expression (returns handle)
pub fn rt_ast_expr_method_receiver(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_method_receiver")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_method_receiver", handle))?;
        match expr {
            Expr::MethodCall { receiver, .. } => {
                let child_handle = register_expr(*receiver.clone());
                Ok(Value::Int(child_handle))
            }
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_method_receiver: not a MethodCall expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get method name of a MethodCall expression
pub fn rt_ast_expr_method_name(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_method_name")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_method_name", handle))?;
        match expr {
            Expr::MethodCall { method, .. } => Ok(Value::Str(method.clone())),
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_method_name: not a MethodCall expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get arg count of a MethodCall expression
pub fn rt_ast_expr_method_arg_count(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_method_arg_count")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_method_arg_count", handle))?;
        match expr {
            Expr::MethodCall { args: method_args, .. } => Ok(Value::Int(method_args.len() as i64)),
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_method_arg_count: not a MethodCall expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the i-th arg of a MethodCall expression (returns Argument handle)
pub fn rt_ast_expr_method_arg(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_method_arg")?;
    let index = get_handle(args, 1, "rt_ast_expr_method_arg")? as usize;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_method_arg", handle))?;
        match expr {
            Expr::MethodCall { args: method_args, .. } => {
                let arg = method_args.get(index).ok_or_else(|| {
                    CompileError::semantic_with_context(
                        format!("rt_ast_expr_method_arg: index {} out of bounds", index),
                        ErrorContext::new().with_code(codes::INDEX_OUT_OF_BOUNDS),
                    )
                })?;
                let arg_handle = register_arg(arg.clone());
                Ok(Value::Int(arg_handle))
            }
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_method_arg: not a MethodCall expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get receiver and field name of a FieldAccess expression
pub fn rt_ast_expr_field_receiver(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_field_receiver")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_field_receiver", handle))?;
        match expr {
            Expr::FieldAccess { receiver, .. } => {
                let child_handle = register_expr(*receiver.clone());
                Ok(Value::Int(child_handle))
            }
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_field_receiver: not a FieldAccess expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

pub fn rt_ast_expr_field_name(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_field_name")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_field_name", handle))?;
        match expr {
            Expr::FieldAccess { field, .. } => Ok(Value::Str(field.clone())),
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_field_name: not a FieldAccess expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get number of elements in an Array expression
pub fn rt_ast_expr_array_len(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_array_len")?;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_array_len", handle))?;
        match expr {
            Expr::Array(elems) => Ok(Value::Int(elems.len() as i64)),
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_array_len: not an Array expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Get the i-th element of an Array expression (returns handle)
pub fn rt_ast_expr_array_get(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_array_get")?;
    let index = get_handle(args, 1, "rt_ast_expr_array_get")? as usize;
    EXPR_REGISTRY.with(|r| {
        let reg = r.borrow();
        let expr = reg
            .get(&handle)
            .ok_or_else(|| invalid_handle("rt_ast_expr_array_get", handle))?;
        match expr {
            Expr::Array(elems) => {
                let elem = elems.get(index).ok_or_else(|| {
                    CompileError::semantic_with_context(
                        format!("rt_ast_expr_array_get: index {} out of bounds", index),
                        ErrorContext::new().with_code(codes::INDEX_OUT_OF_BOUNDS),
                    )
                })?;
                let child_handle = register_expr(elem.clone());
                Ok(Value::Int(child_handle))
            }
            _ => Err(CompileError::semantic_with_context(
                "rt_ast_expr_array_get: not an Array expression".to_string(),
                ErrorContext::new().with_code(codes::TYPE_MISMATCH),
            )),
        }
    })
}

/// Free an expression handle from the registry
pub fn rt_ast_expr_free(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_expr_free")?;
    EXPR_REGISTRY.with(|r| {
        r.borrow_mut().remove(&handle);
    });
    Ok(Value::Nil)
}

/// Free a node handle
pub fn rt_ast_node_free(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_node_free")?;
    NODE_REGISTRY.with(|r| {
        r.borrow_mut().remove(&handle);
    });
    Ok(Value::Nil)
}

/// Free an argument handle
pub fn rt_ast_arg_free(args: &[Value]) -> Result<Value, CompileError> {
    let handle = get_handle(args, 0, "rt_ast_arg_free")?;
    ARG_REGISTRY.with(|r| {
        r.borrow_mut().remove(&handle);
    });
    Ok(Value::Nil)
}

/// Clear all registries (useful for cleanup between runs)
pub fn rt_ast_registry_clear(_args: &[Value]) -> Result<Value, CompileError> {
    EXPR_REGISTRY.with(|r| r.borrow_mut().clear());
    NODE_REGISTRY.with(|r| r.borrow_mut().clear());
    PATTERN_REGISTRY.with(|r| r.borrow_mut().clear());
    BLOCK_REGISTRY.with(|r| r.borrow_mut().clear());
    FUNCDEF_REGISTRY.with(|r| r.borrow_mut().clear());
    MATCHARM_REGISTRY.with(|r| r.borrow_mut().clear());
    PARAM_REGISTRY.with(|r| r.borrow_mut().clear());
    ARG_REGISTRY.with(|r| r.borrow_mut().clear());
    Ok(Value::Nil)
}

/// Get count of live handles (for debugging/diagnostics)
pub fn rt_ast_registry_count(_args: &[Value]) -> Result<Value, CompileError> {
    let count = EXPR_REGISTRY.with(|r| r.borrow().len())
        + NODE_REGISTRY.with(|r| r.borrow().len())
        + PATTERN_REGISTRY.with(|r| r.borrow().len())
        + BLOCK_REGISTRY.with(|r| r.borrow().len())
        + FUNCDEF_REGISTRY.with(|r| r.borrow().len())
        + MATCHARM_REGISTRY.with(|r| r.borrow().len())
        + PARAM_REGISTRY.with(|r| r.borrow().len())
        + ARG_REGISTRY.with(|r| r.borrow().len());
    Ok(Value::Int(count as i64))
}

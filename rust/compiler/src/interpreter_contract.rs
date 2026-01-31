//! Contract checking support for the tree-walking interpreter
//!
//! This module provides runtime contract validation for the interpreter,
//! including preconditions, postconditions, invariants, and old() value capture.
//!
//! ## AST-level Contract Checking
//!
//! The interpreter works with AST nodes, not HIR. This module provides:
//! - `AstOldValueCapture`: Storage for old() values captured at function entry
//! - `ast_capture_old_values`: Scans contract for old() expressions and captures values
//! - `ast_check_entry_contracts`: Checks preconditions and entry invariants
//! - `ast_check_exit_contracts`: Checks postconditions with return value binding

use crate::error::CompileError;
use crate::hir::{HirContract, HirContractClause, HirExpr};
use crate::value::{Env, Value};
use simple_parser::ast::{BinOp, ContractBlock, ContractClause, Expr, FunctionDef, ClassDef, EnumDef, UnaryOp};
use std::collections::HashMap;
use std::sync::Arc;

/// Storage for captured old() values at function entry
#[derive(Debug, Clone, Default)]
pub struct OldValueCapture {
    /// Maps old() expression index to captured value
    captures: HashMap<usize, Value>,
}

impl OldValueCapture {
    /// Create a new empty capture storage
    pub fn new() -> Self {
        Self {
            captures: HashMap::new(),
        }
    }

    /// Capture a value at the given index
    pub fn capture(&mut self, index: usize, value: Value) {
        self.captures.insert(index, value);
    }

    /// Retrieve a captured value by index
    pub fn get(&self, index: usize) -> Option<&Value> {
        self.captures.get(&index)
    }
}

/// Check a contract condition and panic if it fails
///
/// # Arguments
/// * `condition` - The boolean result of evaluating the contract condition
/// * `kind` - Type of contract (e.g., "Precondition", "Postcondition")
/// * `func_name` - Name of the function being checked
/// * `message` - Optional custom error message
///
/// # Panics
/// Panics with a detailed message if the condition is false
pub fn check_contract(condition: bool, kind: &str, func_name: &str, message: Option<&str>) {
    if !condition {
        let msg = if let Some(custom_msg) = message {
            format!(
                "{} violation in function '{}': {} (contract condition failed)",
                kind, func_name, custom_msg
            )
        } else {
            format!(
                "{} violation in function '{}': contract condition failed",
                kind, func_name
            )
        };
        panic!("{}", msg);
    }
}

/// Evaluate a single contract clause and check the result
///
/// # Arguments
/// * `clause` - The contract clause to evaluate
/// * `eval_fn` - Function to evaluate HIR expressions in the current environment
/// * `kind` - Type of contract for error messages
/// * `func_name` - Function name for error messages
///
/// # Returns
/// Ok(()) if the condition passes, Err with message if evaluation fails
///
/// # Panics
/// Panics if the contract condition evaluates to false
pub fn eval_contract_clause<F>(
    clause: &HirContractClause,
    mut eval_fn: F,
    kind: &str,
    func_name: &str,
) -> Result<(), String>
where
    F: FnMut(&HirExpr) -> Result<Value, String>,
{
    // Evaluate the condition expression
    let result = eval_fn(&clause.condition)?;

    // Check if result is a boolean
    let is_true = match result {
        Value::Bool(b) => b,
        _ => return Err(format!("Contract condition must evaluate to boolean, got {:?}", result)),
    };

    // Check the condition and panic if it fails
    check_contract(is_true, kind, func_name, clause.message.as_deref());

    Ok(())
}

/// Capture old() values for a contract
///
/// # Arguments
/// * `contract` - The contract containing old() expressions
/// * `eval_fn` - Function to evaluate HIR expressions
///
/// # Returns
/// OldValueCapture with all old() values evaluated and stored
pub fn capture_old_values<F>(contract: &HirContract, mut eval_fn: F) -> Result<OldValueCapture, String>
where
    F: FnMut(&HirExpr) -> Result<Value, String>,
{
    let mut captures = OldValueCapture::new();

    for (idx, expr) in &contract.old_values {
        let value = eval_fn(expr)?;
        captures.capture(*idx, value);
    }

    Ok(captures)
}

/// Check entry contracts: preconditions and entry invariants
///
/// # Arguments
/// * `contract` - The function contract to check
/// * `eval_fn` - Function to evaluate expressions
/// * `func_name` - Function name for error messages
pub fn check_entry_contracts<F>(contract: &HirContract, eval_fn: F, func_name: &str) -> Result<(), String>
where
    F: FnMut(&HirExpr) -> Result<Value, String> + Clone,
{
    // 1. Check preconditions
    for precond in &contract.preconditions {
        eval_contract_clause(precond, eval_fn.clone(), "Precondition", func_name)?;
    }

    // 2. Check entry invariants
    for inv in &contract.invariants {
        eval_contract_clause(inv, eval_fn.clone(), "Entry invariant", func_name)?;
    }

    Ok(())
}

/// Check exit contracts: exit invariants and postconditions
///
/// # Arguments
/// * `contract` - The function contract to check
/// * `eval_fn` - Function to evaluate expressions
/// * `func_name` - Function name for error messages
pub fn check_exit_contracts<F>(contract: &HirContract, eval_fn: F, func_name: &str) -> Result<(), String>
where
    F: FnMut(&HirExpr) -> Result<Value, String> + Clone,
{
    // 1. Check exit invariants
    for inv in &contract.invariants {
        eval_contract_clause(inv, eval_fn.clone(), "Exit invariant", func_name)?;
    }

    // 2. Check postconditions
    for postcond in &contract.postconditions {
        eval_contract_clause(postcond, eval_fn.clone(), "Postcondition", func_name)?;
    }

    Ok(())
}

//==============================================================================
// AST-level Contract Checking for the Interpreter
//==============================================================================

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

/// Storage for captured old() values at function entry (AST version)
#[derive(Debug, Clone, Default)]
pub struct AstOldValueCapture {
    /// Maps old() expression (by identity via Debug string) to captured value
    captures: HashMap<String, Value>,
}

impl AstOldValueCapture {
    /// Create a new empty capture storage
    pub fn new() -> Self {
        Self {
            captures: HashMap::new(),
        }
    }

    /// Capture a value for an expression
    pub fn capture(&mut self, expr: &Expr, value: Value) {
        self.captures.insert(format!("{:?}", expr), value);
    }

    /// Retrieve a captured value by expression
    pub fn get(&self, expr: &Expr) -> Option<&Value> {
        self.captures.get(&format!("{:?}", expr))
    }
}

/// Visitor to find all old() expressions in a contract expression
fn collect_old_expressions(expr: &Expr, out: &mut Vec<Expr>) {
    match expr {
        Expr::ContractOld(inner) => {
            out.push((**inner).clone());
        }
        // Recursively visit sub-expressions
        Expr::Binary { left, right, .. } => {
            collect_old_expressions(left, out);
            collect_old_expressions(right, out);
        }
        Expr::Unary { operand, .. } => {
            collect_old_expressions(operand, out);
        }
        Expr::Call { callee, args, .. } => {
            collect_old_expressions(callee, out);
            for arg in args {
                collect_old_expressions(&arg.value, out);
            }
        }
        Expr::FieldAccess { receiver, .. } => {
            collect_old_expressions(receiver, out);
        }
        Expr::Index { receiver, index, .. } => {
            collect_old_expressions(receiver, out);
            collect_old_expressions(index, out);
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            collect_old_expressions(condition, out);
            collect_old_expressions(then_branch, out);
            if let Some(else_expr) = else_branch {
                collect_old_expressions(else_expr, out);
            }
        }
        Expr::Tuple(items) => {
            for item in items {
                collect_old_expressions(item, out);
            }
        }
        Expr::Array(items) => {
            for item in items {
                collect_old_expressions(item, out);
            }
        }
        Expr::Lambda { body, .. } => {
            // Lambda bodies are expressions in the new AST
            collect_old_expressions(body, out);
        }
        Expr::MethodCall { receiver, args, .. } => {
            collect_old_expressions(receiver, out);
            for arg in args {
                collect_old_expressions(&arg.value, out);
            }
        }
        Expr::TupleIndex { receiver, .. } => {
            collect_old_expressions(receiver, out);
        }
        // Terminal expressions - no children
        _ => {}
    }
}

/// Capture old() values from a contract block
///
/// Scans the contract's postconditions for old() expressions and evaluates them
/// at function entry.
pub fn ast_capture_old_values<F>(contract: &ContractBlock, mut eval_fn: F) -> Result<AstOldValueCapture, CompileError>
where
    F: FnMut(&Expr) -> Result<Value, CompileError>,
{
    let mut captures = AstOldValueCapture::new();
    let mut old_exprs = Vec::new();

    // Collect old() expressions from postconditions
    for clause in &contract.postconditions {
        collect_old_expressions(&clause.condition, &mut old_exprs);
    }

    // Collect from error postconditions too
    for clause in &contract.error_postconditions {
        collect_old_expressions(&clause.condition, &mut old_exprs);
    }

    // Evaluate and capture each old() expression
    for expr in old_exprs {
        let value = eval_fn(&expr)?;
        captures.capture(&expr, value);
    }

    Ok(captures)
}

/// Evaluate an expression in contract context
///
/// This function handles special contract expressions like ContractOld and ContractResult
/// by substituting captured values.
pub fn ast_eval_in_contract_context<F>(
    expr: &Expr,
    mut eval_fn: F,
    old_captures: &AstOldValueCapture,
    result_value: Option<&Value>,
    result_binding: &str,
    env: &mut Env,
) -> Result<Value, CompileError>
where
    F: FnMut(&Expr, &mut Env) -> Result<Value, CompileError>,
{
    match expr {
        Expr::ContractOld(inner) => {
            // Look up captured value
            if let Some(val) = old_captures.get(inner) {
                Ok(val.clone())
            } else {
                Err(CompileError::runtime(format!(
                    "old() expression not captured: {:?}",
                    inner
                )))
            }
        }
        Expr::ContractResult => {
            // Return the result value
            if let Some(val) = result_value {
                Ok(val.clone())
            } else {
                Err(CompileError::runtime(
                    "contract 'result' used but no return value available".to_string(),
                ))
            }
        }
        Expr::Identifier(name) if name == result_binding => {
            // Return value bound to custom name
            if let Some(val) = result_value {
                Ok(val.clone())
            } else {
                Err(CompileError::runtime(format!(
                    "contract binding '{}' used but no return value available",
                    name
                )))
            }
        }
        // For compound expressions, recursively evaluate
        Expr::Binary { left, op, right, .. } => {
            let l = ast_eval_in_contract_context(
                left,
                |e, env| eval_fn(e, env),
                old_captures,
                result_value,
                result_binding,
                env,
            )?;
            let r = ast_eval_in_contract_context(
                right,
                |e, env| eval_fn(e, env),
                old_captures,
                result_value,
                result_binding,
                env,
            )?;
            // Re-construct and evaluate the binary op with evaluated values
            // We need to pass through to regular evaluation
            eval_binary_op(&l, op, &r)
        }
        Expr::Unary { op, operand, .. } => {
            let val = ast_eval_in_contract_context(
                operand,
                |e, env| eval_fn(e, env),
                old_captures,
                result_value,
                result_binding,
                env,
            )?;
            eval_unary_op(op, &val)
        }
        // For other expressions, delegate to normal evaluation
        _ => eval_fn(expr, env),
    }
}

/// Evaluate binary operation on values
fn eval_binary_op(left: &Value, op: &BinOp, right: &Value) -> Result<Value, CompileError> {
    match (left, op, right) {
        // Integer operations
        (Value::Int(l), BinOp::Add, Value::Int(r)) => Ok(Value::Int(l + r)),
        (Value::Int(l), BinOp::Sub, Value::Int(r)) => Ok(Value::Int(l - r)),
        (Value::Int(l), BinOp::Mul, Value::Int(r)) => Ok(Value::Int(l * r)),
        (Value::Int(l), BinOp::Div, Value::Int(r)) => {
            if *r == 0 {
                Err(CompileError::runtime("division by zero".to_string()))
            } else {
                Ok(Value::Int(l / r))
            }
        }
        (Value::Int(l), BinOp::Mod, Value::Int(r)) => Ok(Value::Int(l % r)),
        // Comparisons
        (Value::Int(l), BinOp::Eq, Value::Int(r)) => Ok(Value::Bool(l == r)),
        (Value::Int(l), BinOp::NotEq, Value::Int(r)) => Ok(Value::Bool(l != r)),
        (Value::Int(l), BinOp::Lt, Value::Int(r)) => Ok(Value::Bool(l < r)),
        (Value::Int(l), BinOp::LtEq, Value::Int(r)) => Ok(Value::Bool(l <= r)),
        (Value::Int(l), BinOp::Gt, Value::Int(r)) => Ok(Value::Bool(l > r)),
        (Value::Int(l), BinOp::GtEq, Value::Int(r)) => Ok(Value::Bool(l >= r)),
        // Boolean operations
        (Value::Bool(l), BinOp::And, Value::Bool(r)) => Ok(Value::Bool(*l && *r)),
        (Value::Bool(l), BinOp::Or, Value::Bool(r)) => Ok(Value::Bool(*l || *r)),
        (Value::Bool(l), BinOp::Eq, Value::Bool(r)) => Ok(Value::Bool(l == r)),
        (Value::Bool(l), BinOp::NotEq, Value::Bool(r)) => Ok(Value::Bool(l != r)),
        // Float operations
        (Value::Float(l), BinOp::Add, Value::Float(r)) => Ok(Value::Float(l + r)),
        (Value::Float(l), BinOp::Sub, Value::Float(r)) => Ok(Value::Float(l - r)),
        (Value::Float(l), BinOp::Mul, Value::Float(r)) => Ok(Value::Float(l * r)),
        (Value::Float(l), BinOp::Div, Value::Float(r)) => Ok(Value::Float(l / r)),
        (Value::Float(l), BinOp::Eq, Value::Float(r)) => Ok(Value::Bool(l == r)),
        (Value::Float(l), BinOp::Lt, Value::Float(r)) => Ok(Value::Bool(l < r)),
        (Value::Float(l), BinOp::Gt, Value::Float(r)) => Ok(Value::Bool(l > r)),
        (Value::Float(l), BinOp::LtEq, Value::Float(r)) => Ok(Value::Bool(l <= r)),
        (Value::Float(l), BinOp::GtEq, Value::Float(r)) => Ok(Value::Bool(l >= r)),
        // String operations
        (Value::Str(l), BinOp::Add, Value::Str(r)) => Ok(Value::Str(format!("{}{}", l, r))),
        (Value::Str(l), BinOp::Eq, Value::Str(r)) => Ok(Value::Bool(l == r)),
        (Value::Str(l), BinOp::NotEq, Value::Str(r)) => Ok(Value::Bool(l != r)),
        _ => Err(CompileError::runtime(format!(
            "unsupported binary operation: {:?} {:?} {:?}",
            left, op, right
        ))),
    }
}

/// Evaluate unary operation on value
fn eval_unary_op(op: &UnaryOp, val: &Value) -> Result<Value, CompileError> {
    match (op, val) {
        (UnaryOp::Not, Value::Bool(b)) => Ok(Value::Bool(!b)),
        (UnaryOp::Neg, Value::Int(n)) => Ok(Value::Int(-n)),
        (UnaryOp::Neg, Value::Float(f)) => Ok(Value::Float(-f)),
        _ => Err(CompileError::runtime(format!(
            "unsupported unary operation: {:?} {:?}",
            op, val
        ))),
    }
}

/// Check AST-level contract clause
fn ast_check_clause<F>(clause: &ContractClause, mut eval_fn: F, kind: &str, func_name: &str) -> Result<(), CompileError>
where
    F: FnMut(&Expr) -> Result<Value, CompileError>,
{
    let result = eval_fn(&clause.condition)?;
    let is_true = match result {
        Value::Bool(b) => b,
        _ => {
            return Err(CompileError::runtime(format!(
                "Contract condition must evaluate to boolean, got {:?}",
                result
            )))
        }
    };

    if !is_true {
        let msg = if let Some(ref custom_msg) = clause.message {
            format!(
                "{} violation in function '{}': {} (contract condition failed)",
                kind, func_name, custom_msg
            )
        } else {
            format!(
                "{} violation in function '{}': contract condition failed",
                kind, func_name
            )
        };
        return Err(CompileError::contract_violation(msg));
    }

    Ok(())
}

/// Check entry contracts (preconditions and entry invariants) using AST
pub fn ast_check_entry_contracts<F>(contract: &ContractBlock, eval_fn: F, func_name: &str) -> Result<(), CompileError>
where
    F: FnMut(&Expr) -> Result<Value, CompileError> + Clone,
{
    // Check preconditions
    for clause in &contract.preconditions {
        ast_check_clause(clause, eval_fn.clone(), "Precondition", func_name)?;
    }

    // Check entry invariants
    for clause in &contract.invariants {
        ast_check_clause(clause, eval_fn.clone(), "Entry invariant", func_name)?;
    }

    Ok(())
}

/// Check exit contracts (postconditions and exit invariants) using AST
///
/// This function handles postconditions that may use old() expressions and
/// return value bindings.
pub fn ast_check_exit_contracts<F>(
    contract: &ContractBlock,
    mut eval_fn: F,
    func_name: &str,
    return_value: &Value,
    old_captures: &AstOldValueCapture,
    env: &mut Env,
) -> Result<(), CompileError>
where
    F: FnMut(&Expr, &mut Env) -> Result<Value, CompileError> + Clone,
{
    // Get the postcondition binding name (default: "ret")
    let result_binding = contract.postcondition_binding.as_deref().unwrap_or("ret");

    // Check exit invariants (no special context needed)
    for clause in &contract.invariants {
        let result = eval_fn(&clause.condition, env)?;
        let is_true = match result {
            Value::Bool(b) => b,
            _ => {
                return Err(CompileError::runtime(format!(
                    "Invariant condition must evaluate to boolean, got {:?}",
                    result
                )))
            }
        };
        if !is_true {
            return Err(CompileError::contract_violation(format!(
                "Exit invariant violation in function '{}'",
                func_name
            )));
        }
    }

    // Check postconditions with contract context (old(), result binding)
    for clause in &contract.postconditions {
        let result = ast_eval_in_contract_context(
            &clause.condition,
            |e, env| eval_fn(e, env),
            old_captures,
            Some(return_value),
            result_binding,
            env,
        )?;

        let is_true = match result {
            Value::Bool(b) => b,
            _ => {
                return Err(CompileError::runtime(format!(
                    "Postcondition must evaluate to boolean, got {:?}",
                    result
                )))
            }
        };

        if !is_true {
            let msg = if let Some(ref custom_msg) = clause.message {
                format!("Postcondition violation in function '{}': {}", func_name, custom_msg)
            } else {
                format!("Postcondition violation in function '{}'", func_name)
            };
            return Err(CompileError::contract_violation(msg));
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_check_contract_passes() {
        // Should not panic when condition is true
        check_contract(true, "Test", "test_func", None);
    }

    #[test]
    #[should_panic(expected = "Precondition violation")]
    fn test_check_contract_fails() {
        check_contract(false, "Precondition", "test_func", None);
    }

    #[test]
    #[should_panic(expected = "custom message")]
    fn test_check_contract_with_message() {
        check_contract(false, "Test", "test_func", Some("custom message"));
    }

    #[test]
    fn test_old_value_capture() {
        let mut capture = OldValueCapture::new();
        capture.capture(0, Value::Int(42));
        capture.capture(1, Value::Bool(true));

        assert!(matches!(capture.get(0), Some(Value::Int(42))));
        assert!(matches!(capture.get(1), Some(Value::Bool(true))));
        assert!(capture.get(2).is_none());
    }

    #[test]
    fn test_ast_old_value_capture() {
        let mut capture = AstOldValueCapture::new();
        let expr = Expr::Identifier("x".to_string());
        capture.capture(&expr, Value::Int(42));

        assert!(matches!(capture.get(&expr), Some(Value::Int(42))));
    }
}

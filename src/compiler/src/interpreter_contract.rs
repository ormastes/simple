//! Contract checking support for the tree-walking interpreter
//!
//! This module provides runtime contract validation for the interpreter,
//! including preconditions, postconditions, invariants, and old() value capture.

use crate::hir::{HirContract, HirContractClause, HirExpr};
use crate::value::{Env, Value};
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
        _ => {
            return Err(format!(
                "Contract condition must evaluate to boolean, got {:?}",
                result
            ))
        }
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
pub fn capture_old_values<F>(
    contract: &HirContract,
    mut eval_fn: F,
) -> Result<OldValueCapture, String>
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
pub fn check_entry_contracts<F>(
    contract: &HirContract,
    eval_fn: F,
    func_name: &str,
) -> Result<(), String>
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
pub fn check_exit_contracts<F>(
    contract: &HirContract,
    eval_fn: F,
    func_name: &str,
) -> Result<(), String>
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
}

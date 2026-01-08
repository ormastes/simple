use simple_parser::ast::{BinOp, UnaryOp};

use crate::error::CompileError;
use crate::interpreter::UNIT_SUFFIX_TO_FAMILY;
use crate::interpreter_unit::decompose_si_prefix;
use crate::value::Value;


/// Look up the family name for a unit suffix from the thread-local registry
pub(super) fn lookup_unit_family(suffix: &str) -> Option<String> {
    // First try direct lookup
    if let Some(family) = UNIT_SUFFIX_TO_FAMILY.with(|cell| cell.borrow().get(suffix).cloned()) {
        return Some(family);
    }
    // Try SI prefix decomposition
    if let Some((_multiplier, _base, family)) = decompose_si_prefix(suffix) {
        return Some(family);
    }
    None
}

/// Look up unit family with SI prefix info
/// Returns (family_name, si_multiplier, base_suffix) if SI prefix was used
pub(super) fn lookup_unit_family_with_si(
    suffix: &str,
) -> (Option<String>, Option<f64>, Option<String>) {
    // First try direct lookup
    if let Some(family) = UNIT_SUFFIX_TO_FAMILY.with(|cell| cell.borrow().get(suffix).cloned()) {
        return (Some(family), None, None);
    }
    // Try SI prefix decomposition
    if let Some((multiplier, base, family)) = decompose_si_prefix(suffix) {
        return (Some(family), Some(multiplier), Some(base));
    }
    (None, None, None)
}

/// Perform a binary operation on the inner values of two units
pub(super) fn evaluate_unit_binary_inner(
    left: &Value,
    right: &Value,
    op: BinOp,
) -> Result<Value, CompileError> {
    match op {
        BinOp::Add => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l + r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Float(l + r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Float(*l as f64 + r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Float(l + *r as f64)),
            _ => Err(CompileError::Semantic(format!(
                "cannot add unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        BinOp::Sub => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l - r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Float(l - r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Float(*l as f64 - r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Float(l - *r as f64)),
            _ => Err(CompileError::Semantic(format!(
                "cannot subtract unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        BinOp::Mul => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l * r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Float(l * r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Float(*l as f64 * r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Float(l * *r as f64)),
            // String repetition: "a" * 3 -> "aaa"
            (Value::Str(s), Value::Int(n)) => {
                if *n <= 0 {
                    Ok(Value::Str(String::new()))
                } else {
                    Ok(Value::Str(s.repeat(*n as usize)))
                }
            }
            // String repetition: 3 * "a" -> "aaa"
            (Value::Int(n), Value::Str(s)) => {
                if *n <= 0 {
                    Ok(Value::Str(String::new()))
                } else {
                    Ok(Value::Str(s.repeat(*n as usize)))
                }
            }
            _ => Err(CompileError::Semantic(format!(
                "cannot multiply values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        BinOp::Div => match (left, right) {
            (Value::Int(l), Value::Int(r)) => {
                if *r == 0 {
                    Err(CompileError::Semantic("division by zero".into()))
                } else {
                    Ok(Value::Int(l / r))
                }
            }
            (Value::Float(l), Value::Float(r)) => {
                if *r == 0.0 {
                    Err(CompileError::Semantic("division by zero".into()))
                } else {
                    Ok(Value::Float(l / r))
                }
            }
            (Value::Int(l), Value::Float(r)) => {
                if *r == 0.0 {
                    Err(CompileError::Semantic("division by zero".into()))
                } else {
                    Ok(Value::Float(*l as f64 / r))
                }
            }
            (Value::Float(l), Value::Int(r)) => {
                if *r == 0 {
                    Err(CompileError::Semantic("division by zero".into()))
                } else {
                    Ok(Value::Float(l / *r as f64))
                }
            }
            _ => Err(CompileError::Semantic(format!(
                "cannot divide unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        BinOp::Mod => match (left, right) {
            (Value::Int(l), Value::Int(r)) => {
                if *r == 0 {
                    Err(CompileError::Semantic("modulo by zero".into()))
                } else {
                    Ok(Value::Int(l % r))
                }
            }
            _ => Err(CompileError::Semantic(format!(
                "modulo only supported for integer unit values, got {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        // Comparison operations return bool, not unit
        BinOp::Eq => Ok(Value::Bool(left == right)),
        BinOp::NotEq => Ok(Value::Bool(left != right)),
        BinOp::Lt => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l < r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l < r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Bool((*l as f64) < *r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Bool(*l < (*r as f64))),
            _ => Err(CompileError::Semantic(format!(
                "cannot compare unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        BinOp::Gt => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l > r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l > r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Bool((*l as f64) > *r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Bool(*l > (*r as f64))),
            _ => Err(CompileError::Semantic(format!(
                "cannot compare unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        BinOp::LtEq => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l <= r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l <= r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Bool((*l as f64) <= *r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Bool(*l <= (*r as f64))),
            _ => Err(CompileError::Semantic(format!(
                "cannot compare unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        BinOp::GtEq => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l >= r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l >= r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Bool((*l as f64) >= *r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Bool(*l >= (*r as f64))),
            _ => Err(CompileError::Semantic(format!(
                "cannot compare unit values of types {} and {}",
                left.type_name(),
                right.type_name()
            ))),
        },
        _ => Err(CompileError::Semantic(format!(
            "unsupported binary operation {:?} on unit values",
            op
        ))),
    }
}

/// Perform a unary operation on the inner value of a unit
pub(super) fn evaluate_unit_unary_inner(
    value: &Value,
    op: UnaryOp,
) -> Result<Value, CompileError> {
    match op {
        UnaryOp::Neg => match value {
            Value::Int(v) => Ok(Value::Int(-v)),
            Value::Float(v) => Ok(Value::Float(-v)),
            _ => Err(CompileError::Semantic(format!(
                "cannot negate unit value of type {}",
                value.type_name()
            ))),
        },
        UnaryOp::Not => Err(CompileError::Semantic(
            "cannot apply logical NOT to unit value".into(),
        )),
        UnaryOp::BitNot => Err(CompileError::Semantic(
            "cannot apply bitwise NOT to unit value".into(),
        )),
        _ => Err(CompileError::Semantic(format!(
            "unsupported unary operation {:?} on unit value",
            op
        ))),
    }
}

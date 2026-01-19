use simple_parser::ast::{BinOp, UnaryOp};

use crate::error::{codes, CompileError, ErrorContext};
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
pub(super) fn lookup_unit_family_with_si(suffix: &str) -> (Option<String>, Option<f64>, Option<String>) {
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
pub(super) fn evaluate_unit_binary_inner(left: &Value, right: &Value, op: BinOp) -> Result<Value, CompileError> {
    match op {
        BinOp::Add => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l + r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Float(l + r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Float(*l as f64 + r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Float(l + *r as f64)),
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("addition is only supported for int, float, or string unit values");
                Err(CompileError::semantic_with_context(
                    format!("invalid operation: cannot add unit values of types {} and {}",
                        left.type_name(), right.type_name()),
                    ctx,
                ))
            },
        },
        BinOp::Sub => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Int(l - r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Float(l - r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Float(*l as f64 - r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Float(l - *r as f64)),
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("subtraction is only supported for int or float unit values");
                Err(CompileError::semantic_with_context(
                    format!("invalid operation: cannot subtract unit values of types {} and {}",
                        left.type_name(), right.type_name()),
                    ctx,
                ))
            },
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
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("multiplication is supported for numeric types or string repetition");
                Err(CompileError::semantic_with_context(
                    format!("invalid operation: cannot multiply values of types {} and {}",
                        left.type_name(), right.type_name()),
                    ctx,
                ))
            },
        },
        BinOp::Div => match (left, right) {
            (Value::Int(l), Value::Int(r)) => {
                if *r == 0 {
                    // E3001 - Division By Zero
                    let ctx = ErrorContext::new()
                        .with_code(codes::DIVISION_BY_ZERO)
                        .with_help("cannot divide by zero")
                        .with_note("check that the divisor is not zero before division");
                    Err(CompileError::semantic_with_context(
                        "division by zero".to_string(),
                        ctx,
                    ))
                } else {
                    Ok(Value::Int(l / r))
                }
            }
            (Value::Float(l), Value::Float(r)) => {
                if *r == 0.0 {
                    // E3001 - Division By Zero
                    let ctx = ErrorContext::new()
                        .with_code(codes::DIVISION_BY_ZERO)
                        .with_help("cannot divide by zero")
                        .with_note("check that the divisor is not zero before division");
                    Err(CompileError::semantic_with_context(
                        "division by zero".to_string(),
                        ctx,
                    ))
                } else {
                    Ok(Value::Float(l / r))
                }
            }
            (Value::Int(l), Value::Float(r)) => {
                if *r == 0.0 {
                    // E3001 - Division By Zero
                    let ctx = ErrorContext::new()
                        .with_code(codes::DIVISION_BY_ZERO)
                        .with_help("cannot divide by zero")
                        .with_note("check that the divisor is not zero before division");
                    Err(CompileError::semantic_with_context(
                        "division by zero".to_string(),
                        ctx,
                    ))
                } else {
                    Ok(Value::Float(*l as f64 / r))
                }
            }
            (Value::Float(l), Value::Int(r)) => {
                if *r == 0 {
                    // E3001 - Division By Zero
                    let ctx = ErrorContext::new()
                        .with_code(codes::DIVISION_BY_ZERO)
                        .with_help("cannot divide by zero")
                        .with_note("check that the divisor is not zero before division");
                    Err(CompileError::semantic_with_context(
                        "division by zero".to_string(),
                        ctx,
                    ))
                } else {
                    Ok(Value::Float(l / *r as f64))
                }
            }
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("division is only supported for int or float unit values");
                Err(CompileError::semantic_with_context(
                    format!("invalid operation: cannot divide unit values of types {} and {}",
                        left.type_name(), right.type_name()),
                    ctx,
                ))
            },
        },
        BinOp::Mod => match (left, right) {
            (Value::Int(l), Value::Int(r)) => {
                if *r == 0 {
                    // E3001 - Division By Zero (includes modulo)
                    let ctx = ErrorContext::new()
                        .with_code(codes::DIVISION_BY_ZERO)
                        .with_help("cannot perform modulo by zero")
                        .with_note("check that the divisor is not zero before modulo operation");
                    Err(CompileError::semantic_with_context(
                        "modulo by zero".to_string(),
                        ctx,
                    ))
                } else {
                    Ok(Value::Int(l % r))
                }
            }
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("modulo is only supported for integer unit values");
                Err(CompileError::semantic_with_context(
                    format!("invalid operation: modulo only supported for integer unit values, got {} and {}",
                        left.type_name(), right.type_name()),
                    ctx,
                ))
            },
        },
        // Comparison operations return bool, not unit
        BinOp::Eq => Ok(Value::Bool(left == right)),
        BinOp::NotEq => Ok(Value::Bool(left != right)),
        BinOp::Lt => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l < r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l < r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Bool((*l as f64) < *r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Bool(*l < (*r as f64))),
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("comparison is only supported for numeric unit values");
                Err(CompileError::semantic_with_context(
                    format!("invalid operation: cannot compare unit values of types {} and {}",
                        left.type_name(), right.type_name()),
                    ctx,
                ))
            },
        },
        BinOp::Gt => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l > r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l > r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Bool((*l as f64) > *r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Bool(*l > (*r as f64))),
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("comparison is only supported for numeric unit values");
                Err(CompileError::semantic_with_context(
                    format!("invalid operation: cannot compare unit values of types {} and {}",
                        left.type_name(), right.type_name()),
                    ctx,
                ))
            },
        },
        BinOp::LtEq => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l <= r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l <= r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Bool((*l as f64) <= *r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Bool(*l <= (*r as f64))),
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("comparison is only supported for numeric unit values");
                Err(CompileError::semantic_with_context(
                    format!("invalid operation: cannot compare unit values of types {} and {}",
                        left.type_name(), right.type_name()),
                    ctx,
                ))
            },
        },
        BinOp::GtEq => match (left, right) {
            (Value::Int(l), Value::Int(r)) => Ok(Value::Bool(l >= r)),
            (Value::Float(l), Value::Float(r)) => Ok(Value::Bool(l >= r)),
            (Value::Int(l), Value::Float(r)) => Ok(Value::Bool((*l as f64) >= *r)),
            (Value::Float(l), Value::Int(r)) => Ok(Value::Bool(*l >= (*r as f64))),
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("comparison is only supported for numeric unit values");
                Err(CompileError::semantic_with_context(
                    format!("invalid operation: cannot compare unit values of types {} and {}",
                        left.type_name(), right.type_name()),
                    ctx,
                ))
            },
        },
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("check that the operation is supported on unit values");
            Err(CompileError::semantic_with_context(
                format!("invalid operation: unsupported binary operation {:?} on unit values", op),
                ctx,
            ))
        },
    }
}

/// Perform a unary operation on the inner value of a unit
pub(super) fn evaluate_unit_unary_inner(value: &Value, op: UnaryOp) -> Result<Value, CompileError> {
    match op {
        UnaryOp::Neg => match value {
            Value::Int(v) => Ok(Value::Int(-v)),
            Value::Float(v) => Ok(Value::Float(-v)),
            _ => {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("negation is only supported for numeric unit values");
                Err(CompileError::semantic_with_context(
                    format!("invalid operation: cannot negate unit value of type {}", value.type_name()),
                    ctx,
                ))
            },
        },
        UnaryOp::Not => {
            // E1041 - Invalid Unary Op
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_UNARY_OP)
                .with_help("operator `!` cannot be applied to unit values");
            Err(CompileError::semantic_with_context(
                "cannot apply operator `!` to unit value type".to_string(),
                ctx,
            ))
        }
        UnaryOp::BitNot => {
            // E1041 - Invalid Unary Op
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_UNARY_OP)
                .with_help("operator `~` cannot be applied to unit values");
            Err(CompileError::semantic_with_context(
                "cannot apply operator `~` to unit value type".to_string(),
                ctx,
            ))
        }
        _ => {
            // E1041 - Invalid Unary Op
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_UNARY_OP)
                .with_help("this operator cannot be applied to unit values");
            Err(CompileError::semantic_with_context(
                format!("unsupported unary operation on unit value"),
                ctx,
            ))
        }
    }
}

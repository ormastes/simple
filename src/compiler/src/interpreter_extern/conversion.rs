//! Type conversion extern functions
//!
//! Provides conversion between Simple language types (int, string, bool).

use crate::error::CompileError;
use crate::value::Value;

/// Convert a value to string representation
///
/// Callable from Simple as: `to_string(value)`
///
/// # Arguments
/// * `args` - Evaluated arguments [value]
///
/// # Returns
/// * String representation of the value
pub fn to_string(args: &[Value]) -> Result<Value, CompileError> {
    let val = args
        .first()
        .ok_or_else(|| CompileError::Semantic("to_string expects 1 argument".into()))?;
    Ok(Value::Str(val.to_display_string()))
}

/// Convert a value to integer
///
/// Callable from Simple as: `to_int(value)`
///
/// Supports conversion from:
/// - Int → Int (identity)
/// - String → Int (parse)
/// - Bool → Int (true=1, false=0)
///
/// # Arguments
/// * `args` - Evaluated arguments [value]
///
/// # Returns
/// * Integer representation of the value
pub fn to_int(args: &[Value]) -> Result<Value, CompileError> {
    let val = args
        .first()
        .ok_or_else(|| CompileError::Semantic("to_int expects 1 argument".into()))?;
    match val {
        Value::Int(i) => Ok(Value::Int(*i)),
        Value::Str(s) => s
            .parse::<i64>()
            .map(Value::Int)
            .map_err(|_| crate::error::factory::cannot_convert(s, "int")),
        Value::Bool(b) => Ok(Value::Int(if *b { 1 } else { 0 })),
        _ => Err(CompileError::Semantic("to_int expects string, int, or bool".into())),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_string() {
        assert_eq!(to_string(&[Value::Int(42)]).unwrap(), Value::Str("42".to_string()));
        assert_eq!(to_string(&[Value::Bool(true)]).unwrap(), Value::Str("true".to_string()));
    }

    #[test]
    fn test_to_int_from_int() {
        assert_eq!(to_int(&[Value::Int(42)]).unwrap(), Value::Int(42));
    }

    #[test]
    fn test_to_int_from_string() {
        assert_eq!(to_int(&[Value::Str("123".to_string())]).unwrap(), Value::Int(123));
        assert!(to_int(&[Value::Str("abc".to_string())]).is_err());
    }

    #[test]
    fn test_to_int_from_bool() {
        assert_eq!(to_int(&[Value::Bool(true)]).unwrap(), Value::Int(1));
        assert_eq!(to_int(&[Value::Bool(false)]).unwrap(), Value::Int(0));
    }
}

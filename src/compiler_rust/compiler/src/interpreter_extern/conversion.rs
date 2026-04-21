//! Type conversion extern functions
//!
//! Provides conversion between Simple language types (int, string, bool).

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use std::sync::Arc;

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
    let val = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("to_string expects exactly 1 argument");
        CompileError::semantic_with_context("to_string expects 1 argument", ctx)
    })?;
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
    let val = args.first().ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("to_int expects exactly 1 argument");
        CompileError::semantic_with_context("to_int expects 1 argument", ctx)
    })?;
    match val {
        Value::Int(i) => Ok(Value::Int(*i)),
        Value::Str(s) => s
            .parse::<i64>()
            .map(Value::Int)
            .map_err(|_| crate::error::factory::cannot_convert(s, "int")),
        Value::Bool(b) => Ok(Value::Int(if *b { 1 } else { 0 })),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("to_int expects string, int, or bool");
            Err(CompileError::semantic_with_context(
                "to_int expects string, int, or bool",
                ctx,
            ))
        }
    }
}

/// Hash a text string and return as i64
///
/// Callable from Simple as: `rt_hash_text(s)`
///
/// # Arguments
/// * `args` - Evaluated arguments [text]
///
/// # Returns
/// * i64 hash of the string
pub fn rt_hash_text(args: &[Value]) -> Result<Value, CompileError> {
    let text = match args.first() {
        Some(Value::Str(s)) => s.as_str(),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("rt_hash_text expects a text argument");
            return Err(CompileError::semantic_with_context(
                "rt_hash_text expects text argument",
                ctx,
            ));
        }
    };

    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut hasher = DefaultHasher::new();
    text.hash(&mut hasher);
    let hash = hasher.finish() as i64;

    Ok(Value::Int(hash))
}

/// Convert text to a byte array
///
/// Callable from Simple as: `rt_text_to_bytes(text)`
pub fn rt_text_to_bytes_fn(args: &[Value]) -> Result<Value, CompileError> {
    let text = match args.first() {
        Some(Value::Str(s)) => s.as_str(),
        _ => "",
    };
    let bytes: Vec<Value> = text.as_bytes().iter().map(|b| Value::Int(*b as i64)).collect();
    Ok(Value::Array(std::sync::Arc::new(bytes)))
}

/// Convert a byte array to text
///
/// Callable from Simple as: `rt_bytes_to_text(bytes)`
pub fn rt_bytes_to_text_fn(args: &[Value]) -> Result<Value, CompileError> {
    match args.first() {
        Some(Value::Array(arr)) => {
            let bytes: Vec<u8> = arr
                .iter()
                .filter_map(|v| match v {
                    Value::Int(i) => Some(*i as u8),
                    _ => None,
                })
                .collect();
            let text = String::from_utf8_lossy(&bytes).into_owned();
            Ok(Value::Str(text))
        }
        _ => Ok(Value::Str(String::new())),
    }
}

/// Provide a simple 8x16 bitmap glyph for source-mode font rendering.
pub fn rt_gui_get_glyph_8x16_fn(args: &[Value]) -> Result<Value, CompileError> {
    let codepoint = match args.first() {
        Some(Value::Int(i)) => *i as i32,
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("rt_gui_get_glyph_8x16 expects an integer codepoint");
            return Err(CompileError::semantic_with_context(
                "rt_gui_get_glyph_8x16 expects integer codepoint",
                ctx,
            ));
        }
    };

    let glyph = glyph_8x16(codepoint);
    let rows: Vec<Value> = glyph.into_iter().map(|b| Value::Int(b as i64)).collect();
    Ok(Value::Array(Arc::new(rows)))
}

pub(crate) fn glyph_8x16(codepoint: i32) -> [u8; 16] {
    if codepoint <= 0 || codepoint == 32 {
        return [0; 16];
    }

    let ch = if (0x20..=0x7e).contains(&codepoint) {
        codepoint as u8
    } else {
        b'?'
    };

    let mut rows = [0u8; 16];
    rows[1] = 0x7E;
    rows[2] = 0x42;
    rows[13] = 0x42;
    rows[14] = 0x7E;

    let mut row = 3usize;
    while row <= 12 {
        let rotate = ((row - 3) % 8) as u32;
        let inner = (ch.rotate_left(rotate) >> 1) & 0x3C;
        rows[row] = 0x42 | inner;
        row += 1;
    }

    rows
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

    #[test]
    fn test_rt_gui_get_glyph_8x16_returns_16_rows() {
        let glyph = rt_gui_get_glyph_8x16_fn(&[Value::Int('A' as i64)]).unwrap();
        match glyph {
            Value::Array(rows) => assert_eq!(rows.len(), 16),
            other => panic!("expected array, got {:?}", other),
        }
    }
}

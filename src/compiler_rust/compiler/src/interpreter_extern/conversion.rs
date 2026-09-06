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
    Ok(Value::text(val.to_display_string()))
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

    let mut hash = 5381u64;
    for byte in text.as_bytes() {
        hash = hash.wrapping_mul(33).wrapping_add(*byte as u64);
    }

    Ok(Value::Int(hash as i64))
}

/// Convert text to a byte array
///
/// Callable from Simple as: `rt_text_to_bytes(text)`
pub fn rt_text_to_bytes_fn(args: &[Value]) -> Result<Value, CompileError> {
    let text = match args.first() {
        Some(Value::Str(s)) => s.as_str(),
        _ => "",
    };
    Ok(Value::byte_array(text.as_bytes().to_vec()))
}

/// Read the raw BYTE at a BYTE index of `text`.
///
/// Callable from Simple as: `rt_string_byte_at(text, index) -> i64`
///
/// O(1) counterpart to reading through `rt_text_to_bytes`, which materializes
/// the entire byte array on every call and turned a
/// `while i < s.len(): s.byte_at(i)` scan into O(n^2) -- the same quadratic
/// trap `char_code_at` was already fixed for.
///
/// Semantics match the seed's `byte_at` method arm and the compiled lane
/// exactly: byte-indexed (NOT character-indexed), and out-of-range or
/// negative indices yield 0.
pub fn rt_string_byte_at_fn(args: &[Value]) -> Result<Value, CompileError> {
    let text = match args.first() {
        Some(Value::Str(s)) => s.as_str(),
        _ => "",
    };
    let idx = args.get(1).map(|v| v.as_int().unwrap_or(0)).unwrap_or(0);
    if idx < 0 {
        return Ok(Value::Int(0));
    }
    Ok(Value::Int(text.as_bytes().get(idx as usize).map_or(0, |b| *b as i64)))
}

/// Convert a single byte value to a one-character text string.
///
/// Callable from Simple as: `rt_byte_char(v: i64) -> text`
pub fn rt_byte_char_fn(args: &[Value]) -> Result<Value, CompileError> {
    let byte_val = match args.first() {
        Some(Value::Int(v)) => *v as u8,
        _ => 0u8,
    };
    Ok(Value::text(String::from(byte_val as char)))
}

/// Convert a Unicode scalar value to one-character text.
///
/// Callable from Simple as: `rt_char_from_code(code: i64) -> text`
pub fn rt_char_from_code_fn(args: &[Value]) -> Result<Value, CompileError> {
    let code = match args.first() {
        Some(Value::Int(value)) => *value,
        _ => return Ok(Value::text(String::new())),
    };
    let text = u32::try_from(code)
        .ok()
        .and_then(char::from_u32)
        .map(|value| value.to_string())
        .unwrap_or_default();
    Ok(Value::text(text))
}

/// Convert a byte array to text
///
/// Callable from Simple as: `rt_bytes_to_text(bytes)`
pub fn rt_bytes_to_text_fn(args: &[Value]) -> Result<Value, CompileError> {
    match args.first() {
        Some(value) => {
            // `[u8]` array literals (e.g. `111u8`) evaluate to
            // `Value::UInt { .. }`, not `Value::Int`. A match on `Value::Int`
            // alone silently filtered every element out of a `[u8]` array,
            // so `rt_bytes_to_text([111u8, 107u8])` returned "" instead of
            // "ok" (T-07, x25519mlkem768 campaign: this masked-empty body
            // broke `H1Client.build_request_bytes` once the unrelated
            // `i64.to_char()` dispatch bug was fixed and this became
            // reachable). `Value::as_int()` already handles both `Int` and
            // `UInt` uniformly; use it instead of a manual match.
            let Some(bytes) = value.try_array_bytes() else {
                return Ok(Value::text(String::new()));
            };
            let text = String::from_utf8_lossy(&bytes).into_owned();
            Ok(Value::text(text))
        }
        _ => Ok(Value::text(String::new())),
    }
}

/// Assemble two bytes into a u16 (little-endian).
///
/// Callable from Simple as: `bytes_to_u16_le(b0, b1)`
pub fn bytes_to_u16_le_fn(args: &[Value]) -> Result<Value, CompileError> {
    let b0 = match args.first() {
        Some(Value::Int(i)) => *i as u64,
        _ => 0,
    };
    let b1 = match args.get(1) {
        Some(Value::Int(i)) => *i as u64,
        _ => 0,
    };
    let result = (b0 & 0xFF) | ((b1 & 0xFF) << 8);
    Ok(Value::Int(result as i64))
}

/// Assemble two bytes into a u16 (big-endian).
///
/// Callable from Simple as: `bytes_to_u16_be(b0, b1)`
pub fn bytes_to_u16_be_fn(args: &[Value]) -> Result<Value, CompileError> {
    let b0 = match args.first() {
        Some(Value::Int(i)) => *i as u64,
        _ => 0,
    };
    let b1 = match args.get(1) {
        Some(Value::Int(i)) => *i as u64,
        _ => 0,
    };
    let result = ((b0 & 0xFF) << 8) | (b1 & 0xFF);
    Ok(Value::Int(result as i64))
}

/// Extract a u8 from a Value, defaulting to 0.
fn extract_byte(v: &Value) -> u64 {
    match v {
        Value::Int(i) => (*i as u64) & 0xFF,
        _ => 0,
    }
}

/// Assemble a [u8] array into a u32 (little-endian).
///
/// Callable from Simple as: `bytes_to_u32_le(bytes)`
pub fn bytes_to_u32_le_fn(args: &[Value]) -> Result<Value, CompileError> {
    let bytes: Option<Vec<u64>> = match args.first() {
        Some(Value::Tuple(arr)) => Some(arr.iter().map(extract_byte).collect()),
        Some(value) => value
            .try_array_bytes()
            .map(|bytes| bytes.into_iter().map(u64::from).collect()),
        None => None,
    };
    let Some(items) = bytes else {
        return Ok(Value::Int(0));
    };
    if items.len() < 4 {
        return Ok(Value::Int(0));
    }
    let result = items[0] | (items[1] << 8) | (items[2] << 16) | (items[3] << 24);
    Ok(Value::Int(result as i64))
}

/// Get element `index` from a tuple (or array), returning the element `Value`.
///
/// Callable from Simple as: `rt_tuple_get(tuple, index)`. The `.spl` extern
/// declares i64 params/return (SFFI handle convention), but the interpreter
/// passes the real `Value::Tuple` and returns the element `Value` directly.
/// This is registered on the native codegen side (codegen/instr/pattern.rs,
/// common_backend.rs, methods.rs) but was missing here, so every `native-build`
/// failed with "unknown extern function: rt_tuple_get" — native-build interprets
/// the compiler, whose HIR lowering (20.hir/hir_lowering/statements.spl) calls it.
pub fn rt_tuple_get_fn(args: &[Value]) -> Result<Value, CompileError> {
    let items: &[Value] = match args.first() {
        Some(Value::Tuple(arr)) => arr,
        Some(Value::LabeledTuple { values, .. }) => values,
        Some(Value::Array(arr)) => arr.as_ref(),
        Some(Value::FrozenArray(arr)) => arr.as_ref(),
        _ => return Ok(Value::Nil),
    };
    let idx = match args.get(1) {
        Some(Value::Int(i)) => *i,
        _ => return Ok(Value::Nil),
    };
    if idx < 0 || idx as usize >= items.len() {
        return Ok(Value::Nil);
    }
    Ok(items[idx as usize].clone())
}

/// Assemble a [u8] array into a u32 (big-endian).
///
/// Callable from Simple as: `bytes_to_u32_be(bytes)`
pub fn bytes_to_u32_be_fn(args: &[Value]) -> Result<Value, CompileError> {
    let items: Vec<u64> = match args.first() {
        Some(Value::Tuple(arr)) => arr.iter().map(extract_byte).collect(),
        Some(value) => match value.try_array_bytes() {
            Some(bytes) => bytes.into_iter().map(u64::from).collect(),
            None => return Ok(Value::Int(0)),
        },
        None => return Ok(Value::Int(0)),
    };
    if items.len() < 4 {
        return Ok(Value::Int(0));
    }
    let result = (items[0] << 24) | (items[1] << 16) | (items[2] << 8) | items[3];
    Ok(Value::Int(result as i64))
}

/// Assemble a [u8] array into a u64 (little-endian).
///
/// Callable from Simple as: `bytes_to_u64_le(bytes)`
pub fn bytes_to_u64_le_fn(args: &[Value]) -> Result<Value, CompileError> {
    let items: Vec<u64> = match args.first() {
        Some(Value::Tuple(arr)) => arr.iter().map(extract_byte).collect(),
        Some(value) => match value.try_array_bytes() {
            Some(bytes) => bytes.into_iter().map(u64::from).collect(),
            None => return Ok(Value::Int(0)),
        },
        None => return Ok(Value::Int(0)),
    };
    if items.len() < 8 {
        return Ok(Value::Int(0));
    }
    let result = items[0]
        | (items[1] << 8)
        | (items[2] << 16)
        | (items[3] << 24)
        | (items[4] << 32)
        | (items[5] << 40)
        | (items[6] << 48)
        | (items[7] << 56);
    Ok(Value::Int(result as i64))
}

/// Assemble a [u8] array into a u64 (big-endian).
///
/// Callable from Simple as: `bytes_to_u64_be(bytes)`
pub fn bytes_to_u64_be_fn(args: &[Value]) -> Result<Value, CompileError> {
    let items: Vec<u64> = match args.first() {
        Some(Value::Tuple(arr)) => arr.iter().map(extract_byte).collect(),
        Some(value) => match value.try_array_bytes() {
            Some(bytes) => bytes.into_iter().map(u64::from).collect(),
            None => return Ok(Value::Int(0)),
        },
        None => return Ok(Value::Int(0)),
    };
    if items.len() < 8 {
        return Ok(Value::Int(0));
    }
    let result = (items[0] << 56)
        | (items[1] << 48)
        | (items[2] << 40)
        | (items[3] << 32)
        | (items[4] << 24)
        | (items[5] << 16)
        | (items[6] << 8)
        | items[7];
    Ok(Value::Int(result as i64))
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
        (codepoint as u8).to_ascii_uppercase()
    } else {
        b'?'
    };

    let pattern = glyph_5x7_ascii(ch);
    let mut rows = [0u8; 16];

    for (src_row, bits) in pattern.iter().enumerate() {
        let mut expanded = 0u8;
        for col in 0..5 {
            if bits & (0b10000 >> col) != 0 {
                expanded |= 0x40 >> col;
            }
        }
        let row = 1 + src_row * 2;
        rows[row] = expanded;
        rows[row + 1] = expanded;
    }

    rows
}

fn glyph_5x7_ascii(ch: u8) -> [u8; 7] {
    match ch {
        b'A' => [0b01110, 0b10001, 0b10001, 0b11111, 0b10001, 0b10001, 0b10001],
        b'B' => [0b11110, 0b10001, 0b10001, 0b11110, 0b10001, 0b10001, 0b11110],
        b'C' => [0b01111, 0b10000, 0b10000, 0b10000, 0b10000, 0b10000, 0b01111],
        b'D' => [0b11110, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b11110],
        b'E' => [0b11111, 0b10000, 0b10000, 0b11110, 0b10000, 0b10000, 0b11111],
        b'F' => [0b11111, 0b10000, 0b10000, 0b11110, 0b10000, 0b10000, 0b10000],
        b'G' => [0b01111, 0b10000, 0b10000, 0b10111, 0b10001, 0b10001, 0b01111],
        b'H' => [0b10001, 0b10001, 0b10001, 0b11111, 0b10001, 0b10001, 0b10001],
        b'I' => [0b11111, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0b11111],
        b'J' => [0b00001, 0b00001, 0b00001, 0b00001, 0b10001, 0b10001, 0b01110],
        b'K' => [0b10001, 0b10010, 0b10100, 0b11000, 0b10100, 0b10010, 0b10001],
        b'L' => [0b10000, 0b10000, 0b10000, 0b10000, 0b10000, 0b10000, 0b11111],
        b'M' => [0b10001, 0b11011, 0b10101, 0b10101, 0b10001, 0b10001, 0b10001],
        b'N' => [0b10001, 0b11001, 0b10101, 0b10011, 0b10001, 0b10001, 0b10001],
        b'O' => [0b01110, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b01110],
        b'P' => [0b11110, 0b10001, 0b10001, 0b11110, 0b10000, 0b10000, 0b10000],
        b'Q' => [0b01110, 0b10001, 0b10001, 0b10001, 0b10101, 0b10010, 0b01101],
        b'R' => [0b11110, 0b10001, 0b10001, 0b11110, 0b10100, 0b10010, 0b10001],
        b'S' => [0b01111, 0b10000, 0b10000, 0b01110, 0b00001, 0b00001, 0b11110],
        b'T' => [0b11111, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100, 0b00100],
        b'U' => [0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b01110],
        b'V' => [0b10001, 0b10001, 0b10001, 0b10001, 0b10001, 0b01010, 0b00100],
        b'W' => [0b10001, 0b10001, 0b10001, 0b10101, 0b10101, 0b10101, 0b01010],
        b'X' => [0b10001, 0b10001, 0b01010, 0b00100, 0b01010, 0b10001, 0b10001],
        b'Y' => [0b10001, 0b10001, 0b01010, 0b00100, 0b00100, 0b00100, 0b00100],
        b'Z' => [0b11111, 0b00001, 0b00010, 0b00100, 0b01000, 0b10000, 0b11111],
        b'0' => [0b01110, 0b10001, 0b10011, 0b10101, 0b11001, 0b10001, 0b01110],
        b'1' => [0b00100, 0b01100, 0b00100, 0b00100, 0b00100, 0b00100, 0b01110],
        b'2' => [0b01110, 0b10001, 0b00001, 0b00010, 0b00100, 0b01000, 0b11111],
        b'3' => [0b11110, 0b00001, 0b00001, 0b01110, 0b00001, 0b00001, 0b11110],
        b'4' => [0b00010, 0b00110, 0b01010, 0b10010, 0b11111, 0b00010, 0b00010],
        b'5' => [0b11111, 0b10000, 0b10000, 0b11110, 0b00001, 0b00001, 0b11110],
        b'6' => [0b01110, 0b10000, 0b10000, 0b11110, 0b10001, 0b10001, 0b01110],
        b'7' => [0b11111, 0b00001, 0b00010, 0b00100, 0b01000, 0b01000, 0b01000],
        b'8' => [0b01110, 0b10001, 0b10001, 0b01110, 0b10001, 0b10001, 0b01110],
        b'9' => [0b01110, 0b10001, 0b10001, 0b01111, 0b00001, 0b00001, 0b01110],
        b':' => [0b00000, 0b00100, 0b00100, 0b00000, 0b00100, 0b00100, 0b00000],
        b'.' => [0b00000, 0b00000, 0b00000, 0b00000, 0b00000, 0b01100, 0b01100],
        b'/' => [0b00001, 0b00010, 0b00010, 0b00100, 0b01000, 0b01000, 0b10000],
        b'-' => [0b00000, 0b00000, 0b00000, 0b11111, 0b00000, 0b00000, 0b00000],
        b'_' => [0b00000, 0b00000, 0b00000, 0b00000, 0b00000, 0b00000, 0b11111],
        b'$' => [0b00100, 0b01111, 0b10100, 0b01110, 0b00101, 0b11110, 0b00100],
        b'>' => [0b10000, 0b01000, 0b00100, 0b00010, 0b00100, 0b01000, 0b10000],
        b'<' => [0b00001, 0b00010, 0b00100, 0b01000, 0b00100, 0b00010, 0b00001],
        b'=' => [0b00000, 0b00000, 0b11111, 0b00000, 0b11111, 0b00000, 0b00000],
        b'?' => [0b01110, 0b10001, 0b00001, 0b00010, 0b00100, 0b00000, 0b00100],
        _ => [0b11111, 0b00001, 0b00010, 0b00100, 0b00100, 0b00000, 0b00100],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_to_string() {
        assert_eq!(to_string(&[Value::Int(42)]).unwrap(), Value::text("42".to_string()));
        assert_eq!(
            to_string(&[Value::Bool(true)]).unwrap(),
            Value::text("true".to_string())
        );
    }

    #[test]
    fn test_to_int_from_int() {
        assert_eq!(to_int(&[Value::Int(42)]).unwrap(), Value::Int(42));
    }

    #[test]
    fn test_to_int_from_string() {
        assert_eq!(to_int(&[Value::text("123".to_string())]).unwrap(), Value::Int(123));
        assert!(to_int(&[Value::text("abc".to_string())]).is_err());
    }

    #[test]
    fn test_to_int_from_bool() {
        assert_eq!(to_int(&[Value::Bool(true)]).unwrap(), Value::Int(1));
        assert_eq!(to_int(&[Value::Bool(false)]).unwrap(), Value::Int(0));
    }

    #[test]
    fn test_rt_hash_text_uses_stable_byte_hash() {
        assert_eq!(rt_hash_text(&[Value::text("".to_string())]).unwrap(), Value::Int(5381));
        assert_eq!(
            rt_hash_text(&[Value::text("abc".to_string())]).unwrap(),
            Value::Int(193485963)
        );
        assert_eq!(
            rt_hash_text(&[Value::text("key_7".to_string())]).unwrap(),
            Value::Int(210718207876)
        );
    }

    #[test]
    fn test_rt_char_from_code_matches_native_scalar_policy() {
        assert_eq!(
            rt_char_from_code_fn(&[Value::Int(65)]).unwrap(),
            Value::text("A".to_string())
        );
        assert_eq!(
            rt_char_from_code_fn(&[Value::Int(0x1f642)]).unwrap(),
            Value::text("\u{1f642}".to_string())
        );
        assert_eq!(
            rt_char_from_code_fn(&[Value::Int(0xd800)]).unwrap(),
            Value::text(String::new())
        );
        assert_eq!(
            rt_char_from_code_fn(&[Value::Int(-1)]).unwrap(),
            Value::text(String::new())
        );
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

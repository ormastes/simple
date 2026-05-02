//! SIMD capability extern functions for interpreter mode.
//!
//! These bridge `std.simd` host-profile queries directly to the Rust runtime
//! so interpreter-mode specs can exercise the same public APIs as compiled code.

use crate::error::CompileError;
use crate::value::Value;
use crate::value_bridge::{runtime_to_value, value_to_runtime};
use simple_runtime::value::aes::{decrypt_block_with_expanded_bytes, encrypt_block_with_expanded_bytes};
use simple_runtime::value::simd::{
    rt_simd_detect_profile as ffi_detect_profile, rt_simd_has_avx as ffi_has_avx, rt_simd_has_avx2 as ffi_has_avx2,
    rt_simd_has_neon as ffi_has_neon, rt_simd_has_rvv as ffi_has_rvv, rt_simd_has_sse as ffi_has_sse,
    rt_simd_profile_name as ffi_profile_name,
};
use simple_runtime::value::simd_int_ops::{
    and_i32x4 as ffi_and_i32x4, and_i32x8 as ffi_and_i32x8, or_i32x4 as ffi_or_i32x4, or_i32x8 as ffi_or_i32x8,
    shl_i32x4 as ffi_shl_i32x4, shl_i32x8 as ffi_shl_i32x8, shr_i32x4 as ffi_shr_i32x4, shr_i32x8 as ffi_shr_i32x8,
    xor_i32x4 as ffi_xor_i32x4, xor_i32x8 as ffi_xor_i32x8,
};
use simple_runtime::value::{
    rt_text_count_codepoints as ffi_text_count_codepoints, rt_utf8_count_codepoints as ffi_utf8_count_codepoints,
    rt_utf8_find_invalid as ffi_utf8_find_invalid, rt_utf8_validate as ffi_utf8_validate,
};
use std::collections::HashMap;
use std::sync::Arc;

fn expect_no_args(name: &str, args: &[Value]) -> Result<(), CompileError> {
    if args.is_empty() {
        Ok(())
    } else {
        Err(CompileError::runtime(format!("{name} expects 0 arguments")))
    }
}

fn expect_byte_array(name: &str, value: &Value) -> Result<Vec<u8>, CompileError> {
    match value {
        Value::Array(items) => items
            .iter()
            .map(|item| match item {
                Value::Int(byte) if (0..=255).contains(byte) => Ok(*byte as u8),
                Value::Int(_) => Err(CompileError::runtime(format!("{name} expects byte values in 0..255"))),
                _ => Err(CompileError::runtime(format!("{name} expects an array of integers"))),
            })
            .collect(),
        _ => Err(CompileError::runtime(format!("{name} expects an array argument"))),
    }
}

pub fn rt_simd_has_sse(args: &[Value]) -> Result<Value, CompileError> {
    expect_no_args("rt_simd_has_sse", args)?;
    Ok(Value::Bool(ffi_has_sse()))
}

pub fn rt_simd_has_avx(args: &[Value]) -> Result<Value, CompileError> {
    expect_no_args("rt_simd_has_avx", args)?;
    Ok(Value::Bool(ffi_has_avx()))
}

pub fn rt_simd_has_avx2(args: &[Value]) -> Result<Value, CompileError> {
    expect_no_args("rt_simd_has_avx2", args)?;
    Ok(Value::Bool(ffi_has_avx2()))
}

pub fn rt_simd_has_neon(args: &[Value]) -> Result<Value, CompileError> {
    expect_no_args("rt_simd_has_neon", args)?;
    Ok(Value::Bool(ffi_has_neon()))
}

pub fn rt_simd_has_rvv(args: &[Value]) -> Result<Value, CompileError> {
    expect_no_args("rt_simd_has_rvv", args)?;
    Ok(Value::Bool(ffi_has_rvv()))
}

pub fn rt_simd_detect_profile(args: &[Value]) -> Result<Value, CompileError> {
    expect_no_args("rt_simd_detect_profile", args)?;
    Ok(Value::Int(ffi_detect_profile()))
}

pub fn rt_simd_profile_name(args: &[Value]) -> Result<Value, CompileError> {
    expect_no_args("rt_simd_profile_name", args)?;
    Ok(runtime_to_value(ffi_profile_name()))
}

pub fn rt_utf8_count_codepoints(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_utf8_count_codepoints expects 1 argument".to_string(),
        ));
    }
    Ok(Value::Int(ffi_utf8_count_codepoints(value_to_runtime(&args[0]))))
}

pub fn rt_utf8_validate(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime("rt_utf8_validate expects 1 argument".to_string()));
    }
    Ok(Value::Bool(ffi_utf8_validate(value_to_runtime(&args[0]))))
}

pub fn rt_utf8_find_invalid(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_utf8_find_invalid expects 1 argument".to_string(),
        ));
    }
    Ok(Value::Int(ffi_utf8_find_invalid(value_to_runtime(&args[0]))))
}

pub fn rt_text_count_codepoints(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::runtime(
            "rt_text_count_codepoints expects 1 argument".to_string(),
        ));
    }
    Ok(Value::Int(ffi_text_count_codepoints(value_to_runtime(&args[0]))))
}

pub fn rt_aes_encrypt_block_with_expanded(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::runtime(
            "rt_aes_encrypt_block_with_expanded expects 3 arguments".to_string(),
        ));
    }

    let block = expect_byte_array("rt_aes_encrypt_block_with_expanded", &args[0])?;
    let expanded = expect_byte_array("rt_aes_encrypt_block_with_expanded", &args[1])?;
    let rounds = match args.get(2) {
        Some(Value::Int(rounds)) => *rounds,
        _ => {
            return Err(CompileError::runtime(
                "rt_aes_encrypt_block_with_expanded expects integer rounds".to_string(),
            ))
        }
    };
    let output = encrypt_block_with_expanded_bytes(&block, &expanded, rounds).unwrap_or([0; 16]);
    Ok(Value::array(
        output.into_iter().map(|byte| Value::Int(byte as i64)).collect(),
    ))
}

pub fn rt_aes_decrypt_block_with_expanded(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 3 {
        return Err(CompileError::runtime(
            "rt_aes_decrypt_block_with_expanded expects 3 arguments".to_string(),
        ));
    }

    let block = expect_byte_array("rt_aes_decrypt_block_with_expanded", &args[0])?;
    let expanded = expect_byte_array("rt_aes_decrypt_block_with_expanded", &args[1])?;
    let rounds = match args.get(2) {
        Some(Value::Int(rounds)) => *rounds,
        _ => {
            return Err(CompileError::runtime(
                "rt_aes_decrypt_block_with_expanded expects integer rounds".to_string(),
            ))
        }
    };
    let output = decrypt_block_with_expanded_bytes(&block, &expanded, rounds).unwrap_or([0; 16]);
    Ok(Value::array(
        output.into_iter().map(|byte| Value::Int(byte as i64)).collect(),
    ))
}

// ============================================================================
// Phase 1 SIMD int bitwise / shift externs (i32x4 + i32x8).
//
// Vec4i is a Simple record `struct Vec4i { x, y, z, w: i32 }`; Vec8i is
// `struct Vec8i { e0..e7: i32 }`. In interpreter mode they arrive as
// `Value::Object { class, fields }`. We unpack to lane arrays, run the kernel,
// and repack.
// ============================================================================

fn require_i32_field(name: &str, fields: &HashMap<String, Value>, field: &str) -> Result<i32, CompileError> {
    match fields.get(field) {
        Some(Value::Int(n)) => Ok(*n as i32),
        Some(other) => Err(CompileError::runtime(format!(
            "{name}: field {field} must be an integer, got {:?}",
            other
        ))),
        None => Err(CompileError::runtime(format!(
            "{name}: missing field {field}"
        ))),
    }
}

fn unpack_vec4i(name: &str, value: &Value) -> Result<[i32; 4], CompileError> {
    match value {
        Value::Object { class, fields } => {
            if class != "Vec4i" {
                return Err(CompileError::runtime(format!(
                    "{name}: expected Vec4i, got {class}"
                )));
            }
            Ok([
                require_i32_field(name, fields, "x")?,
                require_i32_field(name, fields, "y")?,
                require_i32_field(name, fields, "z")?,
                require_i32_field(name, fields, "w")?,
            ])
        }
        other => Err(CompileError::runtime(format!(
            "{name}: expected Vec4i Object, got {:?}",
            other
        ))),
    }
}

fn pack_vec4i(lanes: [i32; 4]) -> Value {
    let mut fields = HashMap::with_capacity(4);
    fields.insert("x".to_string(), Value::Int(lanes[0] as i64));
    fields.insert("y".to_string(), Value::Int(lanes[1] as i64));
    fields.insert("z".to_string(), Value::Int(lanes[2] as i64));
    fields.insert("w".to_string(), Value::Int(lanes[3] as i64));
    Value::Object {
        class: "Vec4i".to_string(),
        fields: Arc::new(fields),
    }
}

fn unpack_vec8i(name: &str, value: &Value) -> Result<[i32; 8], CompileError> {
    match value {
        Value::Object { class, fields } => {
            if class != "Vec8i" {
                return Err(CompileError::runtime(format!(
                    "{name}: expected Vec8i, got {class}"
                )));
            }
            Ok([
                require_i32_field(name, fields, "e0")?,
                require_i32_field(name, fields, "e1")?,
                require_i32_field(name, fields, "e2")?,
                require_i32_field(name, fields, "e3")?,
                require_i32_field(name, fields, "e4")?,
                require_i32_field(name, fields, "e5")?,
                require_i32_field(name, fields, "e6")?,
                require_i32_field(name, fields, "e7")?,
            ])
        }
        other => Err(CompileError::runtime(format!(
            "{name}: expected Vec8i Object, got {:?}",
            other
        ))),
    }
}

fn pack_vec8i(lanes: [i32; 8]) -> Value {
    let mut fields = HashMap::with_capacity(8);
    for (i, lane) in lanes.iter().enumerate() {
        fields.insert(format!("e{}", i), Value::Int(*lane as i64));
    }
    Value::Object {
        class: "Vec8i".to_string(),
        fields: Arc::new(fields),
    }
}

fn require_int_arg(name: &str, value: &Value) -> Result<i64, CompileError> {
    match value {
        Value::Int(n) => Ok(*n),
        other => Err(CompileError::runtime(format!(
            "{name}: expected integer shift count, got {:?}",
            other
        ))),
    }
}

fn binop_i32x4<F>(name: &str, args: &[Value], op: F) -> Result<Value, CompileError>
where
    F: Fn([i32; 4], [i32; 4]) -> [i32; 4],
{
    if args.len() != 2 {
        return Err(CompileError::runtime(format!("{name} expects 2 arguments")));
    }
    let a = unpack_vec4i(name, &args[0])?;
    let b = unpack_vec4i(name, &args[1])?;
    Ok(pack_vec4i(op(a, b)))
}

fn binop_i32x8<F>(name: &str, args: &[Value], op: F) -> Result<Value, CompileError>
where
    F: Fn([i32; 8], [i32; 8]) -> [i32; 8],
{
    if args.len() != 2 {
        return Err(CompileError::runtime(format!("{name} expects 2 arguments")));
    }
    let a = unpack_vec8i(name, &args[0])?;
    let b = unpack_vec8i(name, &args[1])?;
    Ok(pack_vec8i(op(a, b)))
}

fn shift_i32x4<F>(name: &str, args: &[Value], op: F) -> Result<Value, CompileError>
where
    F: Fn([i32; 4], i64) -> [i32; 4],
{
    if args.len() != 2 {
        return Err(CompileError::runtime(format!("{name} expects 2 arguments")));
    }
    let a = unpack_vec4i(name, &args[0])?;
    let n = require_int_arg(name, &args[1])?;
    Ok(pack_vec4i(op(a, n)))
}

fn shift_i32x8<F>(name: &str, args: &[Value], op: F) -> Result<Value, CompileError>
where
    F: Fn([i32; 8], i64) -> [i32; 8],
{
    if args.len() != 2 {
        return Err(CompileError::runtime(format!("{name} expects 2 arguments")));
    }
    let a = unpack_vec8i(name, &args[0])?;
    let n = require_int_arg(name, &args[1])?;
    Ok(pack_vec8i(op(a, n)))
}

pub fn rt_simd_xor_i32x4(args: &[Value]) -> Result<Value, CompileError> {
    binop_i32x4("rt_simd_xor_i32x4", args, ffi_xor_i32x4)
}

pub fn rt_simd_and_i32x4(args: &[Value]) -> Result<Value, CompileError> {
    binop_i32x4("rt_simd_and_i32x4", args, ffi_and_i32x4)
}

pub fn rt_simd_or_i32x4(args: &[Value]) -> Result<Value, CompileError> {
    binop_i32x4("rt_simd_or_i32x4", args, ffi_or_i32x4)
}

pub fn rt_simd_shl_i32x4(args: &[Value]) -> Result<Value, CompileError> {
    shift_i32x4("rt_simd_shl_i32x4", args, ffi_shl_i32x4)
}

pub fn rt_simd_shr_i32x4(args: &[Value]) -> Result<Value, CompileError> {
    shift_i32x4("rt_simd_shr_i32x4", args, ffi_shr_i32x4)
}

pub fn rt_simd_xor_i32x8(args: &[Value]) -> Result<Value, CompileError> {
    binop_i32x8("rt_simd_xor_i32x8", args, ffi_xor_i32x8)
}

pub fn rt_simd_and_i32x8(args: &[Value]) -> Result<Value, CompileError> {
    binop_i32x8("rt_simd_and_i32x8", args, ffi_and_i32x8)
}

pub fn rt_simd_or_i32x8(args: &[Value]) -> Result<Value, CompileError> {
    binop_i32x8("rt_simd_or_i32x8", args, ffi_or_i32x8)
}

pub fn rt_simd_shl_i32x8(args: &[Value]) -> Result<Value, CompileError> {
    shift_i32x8("rt_simd_shl_i32x8", args, ffi_shl_i32x8)
}

pub fn rt_simd_shr_i32x8(args: &[Value]) -> Result<Value, CompileError> {
    shift_i32x8("rt_simd_shr_i32x8", args, ffi_shr_i32x8)
}

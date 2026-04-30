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
use simple_runtime::value::{
    rt_text_count_codepoints as ffi_text_count_codepoints, rt_utf8_count_codepoints as ffi_utf8_count_codepoints,
    rt_utf8_find_invalid as ffi_utf8_find_invalid, rt_utf8_validate as ffi_utf8_validate,
};

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

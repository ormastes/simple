//! Cranelift SFFI functions for the Simple language interpreter
//!
//! These functions allow Simple code to call Cranelift code generation functions.
//! This enables the self-hosting compiler to generate native code.

use crate::error::CompileError;
use crate::value::Value;
use simple_runtime::RuntimeValue;

// Import the actual Cranelift SFFI implementations
use crate::codegen::cranelift_sffi;

/// Helper to convert Value::Str to RuntimeValue for SFFI
fn value_to_runtime_string(val: &Value, symbol: &str) -> Result<RuntimeValue, CompileError> {
    match val {
        Value::Str(s) => Ok(simple_runtime::value::rt_string_new(s.as_ptr(), s.len() as u64)),
        _ => Err(CompileError::runtime(format!("{symbol}: expected text argument"))),
    }
}

/// Convert a runtime string without fabricating empty text from a corrupt
/// positive-length/null-data descriptor.
fn runtime_string_to_value(rv: RuntimeValue, symbol: &str) -> Result<Value, CompileError> {
    let len = simple_runtime::value::rt_string_len(rv);
    if len <= 0 {
        return Ok(Value::text(String::new()));
    }
    let data = simple_runtime::value::rt_string_data(rv);
    unsafe { runtime_string_parts_to_value(data, len, symbol) }
}

unsafe fn runtime_string_parts_to_value(data: *const u8, len: i64, symbol: &str) -> Result<Value, CompileError> {
    if len <= 0 {
        return Ok(Value::text(String::new()));
    }
    if data.is_null() {
        return Err(CompileError::runtime(format!(
            "{symbol}: foreign text contract returned null with length {len}"
        )));
    }
    unsafe {
        let slice = std::slice::from_raw_parts(data, len as usize);
        Ok(Value::text(String::from_utf8_lossy(slice).to_string()))
    }
}

#[inline]
fn expect_i64(args: &[Value], index: usize, symbol: &str) -> Result<i64, CompileError> {
    match args.get(index) {
        Some(Value::Int(value)) => Ok(*value),
        _ => Err(CompileError::runtime(format!(
            "{symbol}: argument {index} must be an integer"
        ))),
    }
}

#[inline]
fn validate_raw_span(ptr: i64, len: i64, symbol: &str) -> Result<(), CompileError> {
    if len < 0 || (len > 0 && ptr == 0) {
        return Err(CompileError::runtime(format!(
            "{symbol}: invalid raw span (pointer {ptr}, length {len})"
        )));
    }
    Ok(())
}

#[inline]
fn expect_f64(args: &[Value], index: usize, symbol: &str) -> Result<f64, CompileError> {
    match args.get(index) {
        Some(Value::Float(value)) => Ok(*value),
        Some(Value::Float32(value)) => Ok(f64::from(*value)),
        Some(Value::Int(value)) => Ok(*value as f64),
        _ => Err(CompileError::runtime(format!(
            "{symbol}: argument {index} must be numeric"
        ))),
    }
}

#[inline]
fn expect_bool(args: &[Value], index: usize, symbol: &str) -> Result<bool, CompileError> {
    match args.get(index) {
        Some(Value::Bool(value)) => Ok(*value),
        Some(Value::Int(value)) => Ok(*value != 0),
        _ => Err(CompileError::runtime(format!(
            "{symbol}: argument {index} must be boolean"
        ))),
    }
}

unsafe fn interpreter_cranelift_arg_handles(ptr: i64, len: i64) -> Result<Vec<i64>, CompileError> {
    if len < 0 || (len > 0 && ptr == 0) {
        return Err(CompileError::semantic("invalid Cranelift argument vector".to_string()));
    }
    if len == 0 {
        return Ok(Vec::new());
    }
    std::slice::from_raw_parts(ptr as *const Value, len as usize)
        .iter()
        .map(|value| match value {
            Value::Int(handle) => Ok(*handle),
            _ => Err(CompileError::semantic(
                "Cranelift argument handle must be an integer".to_string(),
            )),
        })
        .collect()
}

// ============================================================================
// Module Management
// ============================================================================

/// Create a new JIT/AOT module (RuntimeValue version)
/// Args: name (text), target (i64)
/// Returns: module handle (i64)
pub fn rt_cranelift_module_new(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_cranelift_module_new: expected 2 arguments".to_string(),
        ));
    }
    let name = value_to_runtime_string(&args[0], "rt_cranelift_module_new")?;
    let target = expect_i64(args, 1, "rt_cranelift_module_new")?;
    let handle = cranelift_sffi::rt_cranelift_module_new(name, target);
    Ok(Value::Int(handle))
}

/// Create a new JIT module (raw pointer version)
/// Args: name_ptr (i64), name_len (i64), target (i64)
/// Returns: module handle (i64)
pub fn rt_cranelift_new_module(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime(
            "rt_cranelift_new_module: expected 3 arguments".to_string(),
        ));
    }
    let name_ptr = expect_i64(args, 0, "rt_cranelift_new_module")?;
    let name_len = expect_i64(args, 1, "rt_cranelift_new_module")?;
    let target = expect_i64(args, 2, "rt_cranelift_new_module")?;
    validate_raw_span(name_ptr, name_len, "rt_cranelift_new_module")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_new_module(name_ptr, name_len, target) };
    Ok(Value::Int(handle))
}

/// Create a new AOT module (raw pointer version)
/// Args: name_ptr (i64), name_len (i64), target (i64)
/// Returns: module handle (i64)
pub fn rt_cranelift_new_aot_module(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime(
            "rt_cranelift_new_aot_module: expected 3 arguments".to_string(),
        ));
    }
    let name_ptr = expect_i64(args, 0, "rt_cranelift_new_aot_module")?;
    let name_len = expect_i64(args, 1, "rt_cranelift_new_aot_module")?;
    let target = expect_i64(args, 2, "rt_cranelift_new_aot_module")?;
    validate_raw_span(name_ptr, name_len, "rt_cranelift_new_aot_module")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_new_aot_module(name_ptr, name_len, target) };
    Ok(Value::Int(handle))
}

/// Create a new AOT module for an exact target triple.
pub fn rt_cranelift_new_aot_module_triple(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 4 {
        return Err(CompileError::runtime(
            "rt_cranelift_new_aot_module_triple: expected 4 arguments".to_string(),
        ));
    }
    let name_ptr = expect_i64(args, 0, "rt_cranelift_new_aot_module_triple")?;
    let name_len = expect_i64(args, 1, "rt_cranelift_new_aot_module_triple")?;
    let target_ptr = expect_i64(args, 2, "rt_cranelift_new_aot_module_triple")?;
    let target_len = expect_i64(args, 3, "rt_cranelift_new_aot_module_triple")?;
    validate_raw_span(name_ptr, name_len, "rt_cranelift_new_aot_module_triple name")?;
    validate_raw_span(target_ptr, target_len, "rt_cranelift_new_aot_module_triple target")?;
    let handle =
        unsafe { cranelift_sffi::rt_cranelift_new_aot_module_triple(name_ptr, name_len, target_ptr, target_len) };
    Ok(Value::Int(handle))
}

/// Finalize module (JIT: compile; AOT: finalize)
pub fn rt_cranelift_finalize_module(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime(
            "rt_cranelift_finalize_module: expected 1 argument".to_string(),
        ));
    }
    let module = expect_i64(args, 0, "rt_cranelift_finalize_module")?;
    let result = unsafe { cranelift_sffi::rt_cranelift_finalize_module(module) };
    Ok(Value::Int(result))
}

/// Free module resources
pub fn rt_cranelift_free_module(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime(
            "rt_cranelift_free_module: expected 1 argument".to_string(),
        ));
    }
    let module = expect_i64(args, 0, "rt_cranelift_free_module")?;
    unsafe { cranelift_sffi::rt_cranelift_free_module(module) };
    Ok(Value::Nil)
}

/// Emit AOT module to object file
/// Args: module (i64), path (text)
pub fn rt_cranelift_emit_object(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime(
            "rt_cranelift_emit_object: expected 2 arguments".to_string(),
        ));
    }
    let module = expect_i64(args, 0, "rt_cranelift_emit_object")?;
    let path = value_to_runtime_string(&args[1], "rt_cranelift_emit_object")?;
    let result = unsafe { cranelift_sffi::rt_cranelift_emit_object(module, path) };
    Ok(Value::Bool(result))
}

/// Emit AOT module to object file using a raw string slice.
/// Args: module (i64), path_ptr (i64), path_len (i64)
pub fn rt_cranelift_emit_object_raw(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime(
            "rt_cranelift_emit_object_raw: expected 3 arguments".to_string(),
        ));
    }
    let module = expect_i64(args, 0, "rt_cranelift_emit_object_raw")?;
    let path_ptr = expect_i64(args, 1, "rt_cranelift_emit_object_raw")?;
    let path_len = expect_i64(args, 2, "rt_cranelift_emit_object_raw")?;
    validate_raw_span(path_ptr, path_len, "rt_cranelift_emit_object_raw")?;
    let result = unsafe { cranelift_sffi::rt_cranelift_emit_object_raw(module, path_ptr, path_len) };
    Ok(Value::Bool(result))
}

/// Declare a function in a Cranelift module.
/// Args: module (i64), name_ptr (i64), name_len (i64), sig (i64), linkage (i64)
pub fn rt_cranelift_declare_function(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 5 {
        return Err(CompileError::runtime(
            "rt_cranelift_declare_function: expected 5 arguments".to_string(),
        ));
    }
    let module = expect_i64(args, 0, "rt_cranelift_declare_function")?;
    let name_ptr = expect_i64(args, 1, "rt_cranelift_declare_function")?;
    let name_len = expect_i64(args, 2, "rt_cranelift_declare_function")?;
    let sig = expect_i64(args, 3, "rt_cranelift_declare_function")?;
    let linkage = expect_i64(args, 4, "rt_cranelift_declare_function")?;
    validate_raw_span(name_ptr, name_len, "rt_cranelift_declare_function")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_declare_function(module, name_ptr, name_len, sig, linkage) };
    Ok(Value::Int(handle))
}

/// Declare (and define) a read-only rodata blob holding the given raw bytes.
/// Args: module (i64), bytes_ptr (i64), bytes_len (i64)
/// Returns: data handle (i64), or 0 on failure.
pub fn rt_cranelift_declare_string_data(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Err(CompileError::runtime(
            "rt_cranelift_declare_string_data: expected 3 arguments".to_string(),
        ));
    }
    let module = expect_i64(args, 0, "rt_cranelift_declare_string_data")?;
    let bytes_ptr = expect_i64(args, 1, "rt_cranelift_declare_string_data")?;
    let bytes_len = expect_i64(args, 2, "rt_cranelift_declare_string_data")?;
    validate_raw_span(bytes_ptr, bytes_len, "rt_cranelift_declare_string_data")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_declare_string_data(module, bytes_ptr, bytes_len) };
    Ok(Value::Int(handle))
}

pub fn rt_cranelift_declare_global_data(args: &[Value]) -> Result<Value, CompileError> {
    let module = expect_i64(args, 0, "rt_cranelift_declare_global_data")?;
    let name_ptr = expect_i64(args, 1, "rt_cranelift_declare_global_data")?;
    let name_len = expect_i64(args, 2, "rt_cranelift_declare_global_data")?;
    let writable = expect_i64(args, 3, "rt_cranelift_declare_global_data")?;
    let tls = expect_i64(args, 4, "rt_cranelift_declare_global_data")?;
    validate_raw_span(name_ptr, name_len, "rt_cranelift_declare_global_data")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_declare_global_data(module, name_ptr, name_len, writable, tls) };
    Ok(Value::Int(handle))
}

/// Materialize a previously-declared data object's address as an SSA value
/// in the function currently being built.
/// Args: ctx (i64), data_handle (i64)
/// Returns: value handle (i64), or 0 on failure.
pub fn rt_cranelift_data_addr_in_func(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_data_addr_in_func")?;
    let data_handle = expect_i64(args, 1, "rt_cranelift_data_addr_in_func")?;
    let value = unsafe { cranelift_sffi::rt_cranelift_data_addr_in_func(ctx, data_handle) };
    Ok(Value::Int(value))
}

pub fn rt_cranelift_function_addr_in_func(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_function_addr_in_func")?;
    let func_handle = expect_i64(args, 1, "rt_cranelift_function_addr_in_func")?;
    let colocated = expect_i64(args, 2, "rt_cranelift_function_addr_in_func")?;
    let value = unsafe { cranelift_sffi::rt_cranelift_function_addr_in_func(ctx, func_handle, colocated) };
    Ok(Value::Int(value))
}

/// Import a declared function into the active function builder.
/// Args: ctx (i64), func_handle (i64)
pub fn rt_cranelift_import_function(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_import_function")?;
    let func_handle = expect_i64(args, 1, "rt_cranelift_import_function")?;
    let func_ref = unsafe { cranelift_sffi::rt_cranelift_import_function(ctx, func_handle) };
    Ok(Value::Int(func_ref))
}

/// Append function parameters as block params.
/// Args: ctx (i64), block (i64)
pub fn rt_cranelift_append_func_params(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_append_func_params")?;
    let block = expect_i64(args, 1, "rt_cranelift_append_func_params")?;
    unsafe { cranelift_sffi::rt_cranelift_append_func_params(ctx, block) };
    Ok(Value::Nil)
}

/// Define a finished function in an AOT module.
/// Args: module (i64), name_ptr (i64), name_len (i64), ctx (i64)
pub fn rt_cranelift_aot_define_function(args: &[Value]) -> Result<Value, CompileError> {
    let module = expect_i64(args, 0, "rt_cranelift_aot_define_function")?;
    let name_ptr = expect_i64(args, 1, "rt_cranelift_aot_define_function")?;
    let name_len = expect_i64(args, 2, "rt_cranelift_aot_define_function")?;
    let ctx = expect_i64(args, 3, "rt_cranelift_aot_define_function")?;
    validate_raw_span(name_ptr, name_len, "rt_cranelift_aot_define_function")?;
    let defined = unsafe { cranelift_sffi::rt_cranelift_aot_define_function(module, name_ptr, name_len, ctx) };
    Ok(Value::Bool(defined))
}

// ============================================================================
// Signature Management
// ============================================================================

/// Create a new function signature
/// Args: call_conv (i64)
pub fn rt_cranelift_new_signature(args: &[Value]) -> Result<Value, CompileError> {
    let call_conv = expect_i64(args, 0, "rt_cranelift_new_signature")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_new_signature(call_conv) };
    Ok(Value::Int(handle))
}

/// Add parameter to signature
/// Args: sig (i64), type_ (i64)
pub fn rt_cranelift_sig_add_param(args: &[Value]) -> Result<Value, CompileError> {
    let sig = expect_i64(args, 0, "rt_cranelift_sig_add_param")?;
    let type_code = expect_i64(args, 1, "rt_cranelift_sig_add_param")?;
    unsafe { cranelift_sffi::rt_cranelift_sig_add_param(sig, type_code) };
    Ok(Value::Nil)
}

/// Set return type of signature
/// Args: sig (i64), type_ (i64)
pub fn rt_cranelift_sig_set_return(args: &[Value]) -> Result<Value, CompileError> {
    let sig = expect_i64(args, 0, "rt_cranelift_sig_set_return")?;
    let type_code = expect_i64(args, 1, "rt_cranelift_sig_set_return")?;
    unsafe { cranelift_sffi::rt_cranelift_sig_set_return(sig, type_code) };
    Ok(Value::Nil)
}

// ============================================================================
// Function Building
// ============================================================================

/// Begin building a function
/// Args: module (i64), name_ptr (i64), name_len (i64), sig (i64)
pub fn rt_cranelift_begin_function(args: &[Value]) -> Result<Value, CompileError> {
    let module = expect_i64(args, 0, "rt_cranelift_begin_function")?;
    let name_ptr = expect_i64(args, 1, "rt_cranelift_begin_function")?;
    let name_len = expect_i64(args, 2, "rt_cranelift_begin_function")?;
    let sig = expect_i64(args, 3, "rt_cranelift_begin_function")?;
    validate_raw_span(name_ptr, name_len, "rt_cranelift_begin_function")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_begin_function(module, name_ptr, name_len, sig) };
    Ok(Value::Int(handle))
}

/// End function building
/// Args: ctx (i64)
pub fn rt_cranelift_end_function(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_end_function")?;
    let result = unsafe { cranelift_sffi::rt_cranelift_end_function(ctx) };
    Ok(Value::Int(result))
}

/// Define function in module
/// Args: module (i64), func_id (i64), ctx (i64)
pub fn rt_cranelift_define_function(args: &[Value]) -> Result<Value, CompileError> {
    let module = expect_i64(args, 0, "rt_cranelift_define_function")?;
    let func_id = expect_i64(args, 1, "rt_cranelift_define_function")?;
    let ctx = expect_i64(args, 2, "rt_cranelift_define_function")?;
    let result = unsafe { cranelift_sffi::rt_cranelift_define_function(module, func_id, ctx) };
    Ok(Value::Bool(result))
}

// ============================================================================
// Block Management
// ============================================================================

/// Create a new block
/// Args: ctx (i64)
pub fn rt_cranelift_create_block(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_create_block")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_create_block(ctx) };
    Ok(Value::Int(handle))
}

/// Switch to a block
/// Args: ctx (i64), block (i64)
pub fn rt_cranelift_switch_to_block(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_switch_to_block")?;
    let block = expect_i64(args, 1, "rt_cranelift_switch_to_block")?;
    unsafe { cranelift_sffi::rt_cranelift_switch_to_block(ctx, block) };
    Ok(Value::Nil)
}

/// Seal a block
/// Args: ctx (i64), block (i64)
pub fn rt_cranelift_seal_block(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_seal_block")?;
    let block = expect_i64(args, 1, "rt_cranelift_seal_block")?;
    unsafe { cranelift_sffi::rt_cranelift_seal_block(ctx, block) };
    Ok(Value::Nil)
}

/// Seal all blocks
/// Args: ctx (i64)
pub fn rt_cranelift_seal_all_blocks(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_seal_all_blocks")?;
    unsafe { cranelift_sffi::rt_cranelift_seal_all_blocks(ctx) };
    Ok(Value::Nil)
}

/// Append a block parameter
/// Args: ctx (i64), block (i64), type_ (i64)
pub fn rt_cranelift_append_block_param(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_append_block_param")?;
    let block = expect_i64(args, 1, "rt_cranelift_append_block_param")?;
    let type_ = expect_i64(args, 2, "rt_cranelift_append_block_param")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_append_block_param(ctx, block, type_) };
    Ok(Value::Int(handle))
}

/// Get a block parameter value
/// Args: ctx (i64), block (i64), index (i64)
pub fn rt_cranelift_block_param(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_block_param")?;
    let block = expect_i64(args, 1, "rt_cranelift_block_param")?;
    let index = expect_i64(args, 2, "rt_cranelift_block_param")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_block_param(ctx, block, index) };
    Ok(Value::Int(handle))
}

// ============================================================================
// Constants
// ============================================================================

/// Create an integer constant
/// Args: ctx (i64), type_ (i64), value (i64)
pub fn rt_cranelift_iconst(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_iconst")?;
    let type_ = expect_i64(args, 1, "rt_cranelift_iconst")?;
    let val = expect_i64(args, 2, "rt_cranelift_iconst")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_iconst(ctx, type_, val) };
    Ok(Value::Int(handle))
}

/// Create a float constant
/// Args: ctx (i64), type_ (i64), value (f64)
pub fn rt_cranelift_fconst(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_fconst")?;
    let type_ = expect_i64(args, 1, "rt_cranelift_fconst")?;
    let val = expect_f64(args, 2, "rt_cranelift_fconst")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_fconst(ctx, type_, val) };
    Ok(Value::Int(handle))
}

/// Create a boolean constant
/// Args: ctx (i64), value (bool)
pub fn rt_cranelift_bconst(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_bconst")?;
    let val = expect_bool(args, 1, "rt_cranelift_bconst")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_bconst(ctx, val) };
    Ok(Value::Int(handle))
}

/// Create a null pointer constant
/// Args: ctx (i64), type_ (i64)
pub fn rt_cranelift_null(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_null")?;
    let type_ = expect_i64(args, 1, "rt_cranelift_null")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_null(ctx, type_) };
    Ok(Value::Int(handle))
}

// ============================================================================
// Arithmetic Operations (binary)
// ============================================================================

macro_rules! impl_binop_wrapper {
    ($wrapper_name:ident, $sffi_name:ident) => {
        pub fn $wrapper_name(args: &[Value]) -> Result<Value, CompileError> {
            let symbol = stringify!($wrapper_name);
            let ctx = expect_i64(args, 0, symbol)?;
            let a = expect_i64(args, 1, symbol)?;
            let b = expect_i64(args, 2, symbol)?;
            let handle = unsafe { cranelift_sffi::$sffi_name(ctx, a, b) };
            Ok(Value::Int(handle))
        }
    };
}

impl_binop_wrapper!(rt_cranelift_iadd, rt_cranelift_iadd);
impl_binop_wrapper!(rt_cranelift_isub, rt_cranelift_isub);
impl_binop_wrapper!(rt_cranelift_imul, rt_cranelift_imul);
impl_binop_wrapper!(rt_cranelift_sdiv, rt_cranelift_sdiv);
impl_binop_wrapper!(rt_cranelift_udiv, rt_cranelift_udiv);
impl_binop_wrapper!(rt_cranelift_srem, rt_cranelift_srem);
impl_binop_wrapper!(rt_cranelift_urem, rt_cranelift_urem);
impl_binop_wrapper!(rt_cranelift_fadd, rt_cranelift_fadd);
impl_binop_wrapper!(rt_cranelift_fsub, rt_cranelift_fsub);
impl_binop_wrapper!(rt_cranelift_fmul, rt_cranelift_fmul);
impl_binop_wrapper!(rt_cranelift_fdiv, rt_cranelift_fdiv);
impl_binop_wrapper!(rt_cranelift_band, rt_cranelift_band);
impl_binop_wrapper!(rt_cranelift_bor, rt_cranelift_bor);
impl_binop_wrapper!(rt_cranelift_bxor, rt_cranelift_bxor);
impl_binop_wrapper!(rt_cranelift_ishl, rt_cranelift_ishl);
impl_binop_wrapper!(rt_cranelift_sshr, rt_cranelift_sshr);
impl_binop_wrapper!(rt_cranelift_ushr, rt_cranelift_ushr);

/// Bitwise NOT
/// Args: ctx (i64), a (i64)
pub fn rt_cranelift_bnot(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_bnot")?;
    let a = expect_i64(args, 1, "rt_cranelift_bnot")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_bnot(ctx, a) };
    Ok(Value::Int(handle))
}

// ============================================================================
// Comparison Operations
// ============================================================================

/// Integer comparison
/// Args: ctx (i64), cond (i64), a (i64), b (i64)
pub fn rt_cranelift_icmp(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_icmp")?;
    let cond = expect_i64(args, 1, "rt_cranelift_icmp")?;
    let a = expect_i64(args, 2, "rt_cranelift_icmp")?;
    let b = expect_i64(args, 3, "rt_cranelift_icmp")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_icmp(ctx, cond, a, b) };
    Ok(Value::Int(handle))
}

/// Float comparison
/// Args: ctx (i64), cond (i64), a (i64), b (i64)
pub fn rt_cranelift_fcmp(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_fcmp")?;
    let cond = expect_i64(args, 1, "rt_cranelift_fcmp")?;
    let a = expect_i64(args, 2, "rt_cranelift_fcmp")?;
    let b = expect_i64(args, 3, "rt_cranelift_fcmp")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_fcmp(ctx, cond, a, b) };
    Ok(Value::Int(handle))
}

// ============================================================================
// Memory Operations
// ============================================================================

/// Load from memory
/// Args: ctx (i64), type_ (i64), addr (i64), offset (i64)
pub fn rt_cranelift_load(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_load")?;
    let type_ = expect_i64(args, 1, "rt_cranelift_load")?;
    let addr = expect_i64(args, 2, "rt_cranelift_load")?;
    let offset = expect_i64(args, 3, "rt_cranelift_load")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_load(ctx, type_, addr, offset) };
    Ok(Value::Int(handle))
}

/// Store to memory
/// Args: ctx (i64), value (i64), addr (i64), offset (i64)
pub fn rt_cranelift_store(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_store")?;
    let val = expect_i64(args, 1, "rt_cranelift_store")?;
    let addr = expect_i64(args, 2, "rt_cranelift_store")?;
    let offset = expect_i64(args, 3, "rt_cranelift_store")?;
    unsafe { cranelift_sffi::rt_cranelift_store(ctx, val, addr, offset) };
    Ok(Value::Nil)
}

/// Allocate stack slot
/// Args: ctx (i64), size (i64), align (i64)
pub fn rt_cranelift_stack_slot(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_stack_slot")?;
    let size = expect_i64(args, 1, "rt_cranelift_stack_slot")?;
    let align = expect_i64(args, 2, "rt_cranelift_stack_slot")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_stack_slot(ctx, size, align) };
    Ok(Value::Int(handle))
}

/// Get stack slot address
/// Args: ctx (i64), slot (i64), offset (i64)
pub fn rt_cranelift_stack_addr(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_stack_addr")?;
    let slot = expect_i64(args, 1, "rt_cranelift_stack_addr")?;
    let offset = expect_i64(args, 2, "rt_cranelift_stack_addr")?;
    let handle = unsafe { cranelift_sffi::rt_cranelift_stack_addr(ctx, slot, offset) };
    Ok(Value::Int(handle))
}

// ============================================================================
// Control Flow
// ============================================================================

/// Unconditional jump
/// Args: ctx (i64), block (i64)
pub fn rt_cranelift_jump(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_jump")?;
    let block = expect_i64(args, 1, "rt_cranelift_jump")?;
    unsafe { cranelift_sffi::rt_cranelift_jump(ctx, block) };
    Ok(Value::Nil)
}

/// Conditional branch
/// Args: ctx (i64), cond (i64), then_block (i64), else_block (i64)
pub fn rt_cranelift_brif(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_brif")?;
    let cond = expect_i64(args, 1, "rt_cranelift_brif")?;
    let then_block = expect_i64(args, 2, "rt_cranelift_brif")?;
    let else_block = expect_i64(args, 3, "rt_cranelift_brif")?;
    unsafe { cranelift_sffi::rt_cranelift_brif(ctx, cond, then_block, else_block) };
    Ok(Value::Nil)
}

/// Return with value
/// Args: ctx (i64), value (i64)
pub fn rt_cranelift_return(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_return")?;
    let val = expect_i64(args, 1, "rt_cranelift_return")?;
    unsafe { cranelift_sffi::rt_cranelift_return(ctx, val) };
    Ok(Value::Nil)
}

/// Return void
/// Args: ctx (i64)
pub fn rt_cranelift_return_void(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_return_void")?;
    unsafe { cranelift_sffi::rt_cranelift_return_void(ctx) };
    Ok(Value::Nil)
}

/// Trap (unreachable)
/// Args: ctx (i64), code (i64)
pub fn rt_cranelift_trap(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_trap")?;
    let code = expect_i64(args, 1, "rt_cranelift_trap")?;
    unsafe { cranelift_sffi::rt_cranelift_trap(ctx, code) };
    Ok(Value::Nil)
}

// ============================================================================
// Function Calls
// ============================================================================

pub fn rt_cranelift_call_args_clear(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_call_args_clear")?;
    cranelift_sffi::rt_cranelift_call_args_clear(ctx);
    Ok(Value::Nil)
}

pub fn rt_cranelift_call_arg(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_call_arg")?;
    let value = expect_i64(args, 1, "rt_cranelift_call_arg")?;
    Ok(Value::Bool(cranelift_sffi::rt_cranelift_call_arg(ctx, value)))
}

/// Call a function
/// Args: ctx (i64), func (i64), args_ptr (i64), args_len (i64)
pub fn rt_cranelift_call(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_call")?;
    let func = expect_i64(args, 1, "rt_cranelift_call")?;
    let raw_args = expect_i64(args, 2, "rt_cranelift_call")?;
    let raw_len = expect_i64(args, 3, "rt_cranelift_call")?;
    let handles = unsafe { interpreter_cranelift_arg_handles(raw_args, raw_len)? };
    let (args_ptr, args_len) = if handles.is_empty() {
        (0, 0)
    } else {
        (handles.as_ptr() as i64, handles.len() as i64)
    };
    let handle = unsafe { cranelift_sffi::rt_cranelift_call(ctx, func, args_ptr, args_len) };
    Ok(Value::Int(handle))
}

/// Call indirect (through function pointer)
/// Args: ctx (i64), sig (i64), callee (i64), args_ptr (i64), args_len (i64)
pub fn rt_cranelift_call_indirect(args: &[Value]) -> Result<Value, CompileError> {
    let ctx = expect_i64(args, 0, "rt_cranelift_call_indirect")?;
    let sig = expect_i64(args, 1, "rt_cranelift_call_indirect")?;
    let callee = expect_i64(args, 2, "rt_cranelift_call_indirect")?;
    let raw_args = expect_i64(args, 3, "rt_cranelift_call_indirect")?;
    let raw_len = expect_i64(args, 4, "rt_cranelift_call_indirect")?;
    let handles = unsafe { interpreter_cranelift_arg_handles(raw_args, raw_len)? };
    let (args_ptr, args_len) = if handles.is_empty() {
        (0, 0)
    } else {
        (handles.as_ptr() as i64, handles.len() as i64)
    };
    let handle = unsafe { cranelift_sffi::rt_cranelift_call_indirect(ctx, sig, callee, args_ptr, args_len) };
    Ok(Value::Int(handle))
}

// ============================================================================
// Type Conversions
// ============================================================================

macro_rules! impl_conv_wrapper {
    ($wrapper_name:ident, $sffi_name:ident) => {
        pub fn $wrapper_name(args: &[Value]) -> Result<Value, CompileError> {
            let symbol = stringify!($wrapper_name);
            let ctx = expect_i64(args, 0, symbol)?;
            let to_type = expect_i64(args, 1, symbol)?;
            let value = expect_i64(args, 2, symbol)?;
            let handle = unsafe { cranelift_sffi::$sffi_name(ctx, to_type, value) };
            Ok(Value::Int(handle))
        }
    };
}

impl_conv_wrapper!(rt_cranelift_sextend, rt_cranelift_sextend);
impl_conv_wrapper!(rt_cranelift_uextend, rt_cranelift_uextend);
impl_conv_wrapper!(rt_cranelift_ireduce, rt_cranelift_ireduce);
impl_conv_wrapper!(rt_cranelift_fcvt_to_sint, rt_cranelift_fcvt_to_sint);
impl_conv_wrapper!(rt_cranelift_fcvt_to_uint, rt_cranelift_fcvt_to_uint);
impl_conv_wrapper!(rt_cranelift_fcvt_from_sint, rt_cranelift_fcvt_from_sint);
impl_conv_wrapper!(rt_cranelift_fcvt_from_uint, rt_cranelift_fcvt_from_uint);
impl_conv_wrapper!(rt_cranelift_fpromote, rt_cranelift_fpromote);
impl_conv_wrapper!(rt_cranelift_fdemote, rt_cranelift_fdemote);
impl_conv_wrapper!(rt_cranelift_bitcast, rt_cranelift_bitcast);

// ============================================================================
// JIT Execution
// ============================================================================

/// Get JIT function pointer
/// Args: module (i64), name_ptr (i64), name_len (i64)
pub fn rt_cranelift_get_function_ptr(args: &[Value]) -> Result<Value, CompileError> {
    let module = expect_i64(args, 0, "rt_cranelift_get_function_ptr")?;
    let name_ptr = expect_i64(args, 1, "rt_cranelift_get_function_ptr")?;
    let name_len = expect_i64(args, 2, "rt_cranelift_get_function_ptr")?;
    validate_raw_span(name_ptr, name_len, "rt_cranelift_get_function_ptr")?;
    let ptr = unsafe { cranelift_sffi::rt_cranelift_get_function_ptr(module, name_ptr, name_len) };
    Ok(Value::Int(ptr))
}

/// Call JIT function pointer
/// Args: func_ptr (i64), args_ptr (i64), args_len (i64)
pub fn rt_cranelift_call_function_ptr(args: &[Value]) -> Result<Value, CompileError> {
    let func_ptr = expect_i64(args, 0, "rt_cranelift_call_function_ptr")?;
    if func_ptr == 0 {
        return Err(CompileError::runtime(
            "rt_cranelift_call_function_ptr: null function pointer".to_string(),
        ));
    }
    let args_ptr = expect_i64(args, 1, "rt_cranelift_call_function_ptr")?;
    let args_len = expect_i64(args, 2, "rt_cranelift_call_function_ptr")?;
    validate_raw_span(args_ptr, args_len, "rt_cranelift_call_function_ptr")?;
    let result = unsafe { cranelift_sffi::rt_cranelift_call_function_ptr(func_ptr, args_ptr, args_len) };
    Ok(Value::Int(result))
}

// ============================================================================
// Bootstrap Test SFFI
// ============================================================================

/// Execute shell command
pub fn rt_exec(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_exec: expected 1 argument".to_string()));
    }
    let cmd = value_to_runtime_string(&args[0], "rt_exec")?;
    let result = simple_runtime::value::cli_sffi::rt_exec(cmd);
    Ok(Value::Int(result as i64))
}

/// Get file hash
pub fn rt_file_hash(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Err(CompileError::runtime("rt_file_hash: expected 1 argument".to_string()));
    }
    let path = value_to_runtime_string(&args[0], "rt_file_hash")?;
    let result = simple_runtime::value::cli_sffi::rt_file_hash(path);
    runtime_string_to_value(result, "rt_file_hash")
}

/// Write file
pub fn rt_write_file(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Err(CompileError::runtime("rt_write_file: expected 2 arguments".to_string()));
    }
    let path = value_to_runtime_string(&args[0], "rt_write_file")?;
    let content = value_to_runtime_string(&args[1], "rt_write_file")?;
    let result = simple_runtime::value::cli_sffi::rt_write_file(path, content);
    Ok(Value::Bool(result))
}

#[cfg(test)]
mod tests {
    use super::{interpreter_cranelift_arg_handles, rt_cranelift_emit_object_raw, runtime_string_parts_to_value};
    use crate::value::Value;

    #[test]
    fn interpreter_cranelift_argument_handles_are_validated() {
        let values = vec![Value::Int(7), Value::Int(11)];
        assert_eq!(
            unsafe { interpreter_cranelift_arg_handles(values.as_ptr() as i64, values.len() as i64) }.unwrap(),
            vec![7, 11]
        );
        assert!(unsafe { interpreter_cranelift_arg_handles(0, 0) }.unwrap().is_empty());
        assert!(unsafe { interpreter_cranelift_arg_handles(0, 1) }.is_err());
        assert!(unsafe { interpreter_cranelift_arg_handles(0, -1) }.is_err());
        let invalid = vec![Value::Bool(false)];
        assert!(unsafe { interpreter_cranelift_arg_handles(invalid.as_ptr() as i64, 1) }.is_err());
    }

    #[test]
    fn interpreter_cranelift_emit_object_raw_validates_arity() {
        assert!(rt_cranelift_emit_object_raw(&[]).is_err());
        assert!(rt_cranelift_emit_object_raw(&[Value::Int(1), Value::Int(0), Value::Int(4),]).is_err());
        assert!(rt_cranelift_emit_object_raw(&[Value::Int(1), Value::Int(1), Value::Int(-1),]).is_err());
        assert!(rt_cranelift_emit_object_raw(&[Value::Int(1), Value::Bool(false), Value::Int(0),]).is_err());
    }

    #[test]
    fn text_sffi_rejects_missing_or_wrong_typed_arguments() {
        assert!(super::rt_cranelift_module_new(&[]).is_err());
        assert!(super::rt_cranelift_module_new(&[Value::Int(1), Value::Int(0)]).is_err());
        assert!(super::rt_exec(&[]).is_err());
        assert!(super::rt_exec(&[Value::Nil]).is_err());
        assert!(super::rt_file_hash(&[]).is_err());
        assert!(super::rt_file_hash(&[Value::Bool(false)]).is_err());
        assert!(super::rt_write_file(&[Value::text("path")]).is_err());
        assert!(super::rt_write_file(&[Value::text("path"), Value::Int(0)]).is_err());
    }

    #[test]
    fn declaration_and_context_sffi_reject_fabricated_handles_and_spans() {
        assert!(super::rt_cranelift_declare_global_data(&[]).is_err());
        assert!(super::rt_cranelift_declare_global_data(&[
            Value::Int(1),
            Value::Int(0),
            Value::Int(4),
            Value::Int(0),
            Value::Int(0),
        ])
        .is_err());
        assert!(super::rt_cranelift_data_addr_in_func(&[Value::Nil, Value::Int(1)]).is_err());
        assert!(super::rt_cranelift_aot_define_function(&[
            Value::Int(1),
            Value::Int(1),
            Value::Int(-1),
            Value::Int(1),
        ])
        .is_err());
        assert!(super::rt_cranelift_new_signature(&[]).is_err());
        assert!(super::rt_cranelift_sig_add_param(&[Value::Int(1), Value::Bool(false)]).is_err());
        assert!(
            super::rt_cranelift_begin_function(&[Value::Int(1), Value::Int(0), Value::Int(2), Value::Int(1),]).is_err()
        );
        assert!(super::rt_cranelift_define_function(&[Value::Int(1)]).is_err());
        assert!(super::rt_cranelift_create_block(&[]).is_err());
    }

    #[test]
    fn block_constant_and_binary_sffi_reject_fabricated_operands() {
        assert!(super::rt_cranelift_switch_to_block(&[Value::Int(1)]).is_err());
        assert!(super::rt_cranelift_append_block_param(&[Value::Int(1), Value::Int(2), Value::Nil,]).is_err());
        assert!(super::rt_cranelift_iconst(&[Value::Int(1), Value::Int(2)]).is_err());
        assert!(super::rt_cranelift_fconst(&[Value::Int(1), Value::Int(2), Value::Bool(false),]).is_err());
        assert!(super::rt_cranelift_bconst(&[Value::Int(1), Value::text("false")]).is_err());
        assert!(super::rt_cranelift_iadd(&[Value::Int(1), Value::Int(2), Value::Nil]).is_err());
    }

    #[test]
    fn memory_control_call_and_conversion_sffi_fail_closed() {
        assert!(super::rt_cranelift_icmp(&[Value::Int(1), Value::Int(2), Value::Int(3)]).is_err());
        assert!(super::rt_cranelift_load(&[Value::Int(1), Value::Int(2), Value::Nil, Value::Int(0),]).is_err());
        assert!(super::rt_cranelift_jump(&[]).is_err());
        assert!(super::rt_cranelift_call_arg(&[Value::Int(1), Value::Bool(false)]).is_err());
        assert!(super::rt_cranelift_call(&[Value::Int(1), Value::Int(2), Value::Int(0), Value::Int(1),]).is_err());
        assert!(super::rt_cranelift_sextend(&[Value::Int(1), Value::Int(2), Value::Nil]).is_err());
        assert!(super::rt_cranelift_get_function_ptr(&[Value::Int(1), Value::Int(0), Value::Int(4),]).is_err());
        assert!(super::rt_cranelift_call_function_ptr(&[Value::Int(0), Value::Int(0), Value::Int(0),]).is_err());
    }

    #[test]
    fn runtime_string_null_positive_length_is_a_contract_error() {
        let result = unsafe { runtime_string_parts_to_value(std::ptr::null(), 1, "rt_file_hash") };
        assert!(result.is_err(), "null foreign text must never become empty text");
    }

    #[test]
    fn runtime_string_zero_length_remains_valid_empty_text() {
        let result = unsafe { runtime_string_parts_to_value(std::ptr::null(), 0, "rt_file_hash") };
        assert!(result.is_ok(), "zero-length text may use a null data pointer");
    }
}

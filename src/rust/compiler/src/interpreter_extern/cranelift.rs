//! Cranelift FFI functions for the Simple language interpreter
//!
//! These functions allow Simple code to call Cranelift code generation functions.
//! This enables the self-hosting compiler to generate native code.

use crate::error::CompileError;
use crate::value::Value;
use simple_runtime::RuntimeValue;

// Import the actual Cranelift FFI implementations
use crate::codegen::cranelift_ffi;

/// Helper to convert Value::Str to RuntimeValue for FFI
fn value_to_runtime_string(val: &Value) -> RuntimeValue {
    match val {
        Value::Str(s) => simple_runtime::value::rt_string_new(s.as_ptr(), s.len() as u64),
        _ => RuntimeValue::NIL,
    }
}

/// Helper to convert RuntimeValue string back to Value::Str
fn runtime_string_to_value(rv: RuntimeValue) -> Value {
    let len = simple_runtime::value::rt_string_len(rv);
    if len <= 0 {
        return Value::Str(String::new());
    }
    let data = simple_runtime::value::rt_string_data(rv);
    if data.is_null() {
        return Value::Str(String::new());
    }
    unsafe {
        let slice = std::slice::from_raw_parts(data, len as usize);
        Value::Str(String::from_utf8_lossy(slice).to_string())
    }
}

/// Helper to get i64 from Value
fn value_to_i64(val: &Value) -> i64 {
    match val {
        Value::Int(i) => *i,
        _ => 0,
    }
}

/// Helper to get f64 from Value
fn value_to_f64(val: &Value) -> f64 {
    match val {
        Value::Float(f) => *f,
        Value::Int(i) => *i as f64,
        _ => 0.0,
    }
}

/// Helper to get bool from Value
fn value_to_bool(val: &Value) -> bool {
    match val {
        Value::Bool(b) => *b,
        Value::Int(i) => *i != 0,
        _ => false,
    }
}

// ============================================================================
// Module Management
// ============================================================================

/// Create a new JIT/AOT module (RuntimeValue version)
/// Args: name (text), target (i64)
/// Returns: module handle (i64)
pub fn rt_cranelift_module_new(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Int(0));
    }
    let name = value_to_runtime_string(&args[0]);
    let target = value_to_i64(&args[1]);
    let handle = cranelift_ffi::rt_cranelift_module_new(name, target);
    Ok(Value::Int(handle))
}

/// Create a new JIT module (raw pointer version)
/// Args: name_ptr (i64), name_len (i64), target (i64)
/// Returns: module handle (i64)
pub fn rt_cranelift_new_module(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Ok(Value::Int(0));
    }
    let name_ptr = value_to_i64(&args[0]);
    let name_len = value_to_i64(&args[1]);
    let target = value_to_i64(&args[2]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_new_module(name_ptr, name_len, target) };
    Ok(Value::Int(handle))
}

/// Finalize module (JIT: compile; AOT: finalize)
pub fn rt_cranelift_finalize_module(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Ok(Value::Int(0));
    }
    let module = value_to_i64(&args[0]);
    let result = unsafe { cranelift_ffi::rt_cranelift_finalize_module(module) };
    Ok(Value::Int(result))
}

/// Free module resources
pub fn rt_cranelift_free_module(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Ok(Value::Nil);
    }
    let module = value_to_i64(&args[0]);
    unsafe { cranelift_ffi::rt_cranelift_free_module(module) };
    Ok(Value::Nil)
}

/// Emit AOT module to object file
/// Args: module (i64), path_ptr (i64), path_len (i64)
pub fn rt_cranelift_emit_object(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Ok(Value::Bool(false));
    }
    let module = value_to_i64(&args[0]);
    let path_ptr = value_to_i64(&args[1]);
    let path_len = value_to_i64(&args[2]);
    let result = unsafe { cranelift_ffi::rt_cranelift_emit_object(module, path_ptr, path_len) };
    Ok(Value::Bool(result))
}

// ============================================================================
// Signature Management
// ============================================================================

/// Create a new function signature
/// Args: call_conv (i64)
pub fn rt_cranelift_new_signature(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Ok(Value::Int(0));
    }
    let call_conv = value_to_i64(&args[0]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_new_signature(call_conv) };
    Ok(Value::Int(handle))
}

/// Add parameter to signature
/// Args: sig (i64), type_ (i64)
pub fn rt_cranelift_sig_add_param(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Nil);
    }
    let sig = value_to_i64(&args[0]);
    let type_code = value_to_i64(&args[1]);
    unsafe { cranelift_ffi::rt_cranelift_sig_add_param(sig, type_code) };
    Ok(Value::Nil)
}

/// Set return type of signature
/// Args: sig (i64), type_ (i64)
pub fn rt_cranelift_sig_set_return(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Nil);
    }
    let sig = value_to_i64(&args[0]);
    let type_code = value_to_i64(&args[1]);
    unsafe { cranelift_ffi::rt_cranelift_sig_set_return(sig, type_code) };
    Ok(Value::Nil)
}

// ============================================================================
// Function Building
// ============================================================================

/// Begin building a function
/// Args: module (i64), name_ptr (i64), name_len (i64), sig (i64)
pub fn rt_cranelift_begin_function(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 4 {
        return Ok(Value::Int(0));
    }
    let module = value_to_i64(&args[0]);
    let name_ptr = value_to_i64(&args[1]);
    let name_len = value_to_i64(&args[2]);
    let sig = value_to_i64(&args[3]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_begin_function(module, name_ptr, name_len, sig) };
    Ok(Value::Int(handle))
}

/// End function building
/// Args: ctx (i64)
pub fn rt_cranelift_end_function(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let result = unsafe { cranelift_ffi::rt_cranelift_end_function(ctx) };
    Ok(Value::Int(result))
}

/// Define function in module
/// Args: module (i64), func_id (i64), ctx (i64)
pub fn rt_cranelift_define_function(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Ok(Value::Bool(false));
    }
    let module = value_to_i64(&args[0]);
    let func_id = value_to_i64(&args[1]);
    let ctx = value_to_i64(&args[2]);
    let result = unsafe { cranelift_ffi::rt_cranelift_define_function(module, func_id, ctx) };
    Ok(Value::Bool(result))
}

// ============================================================================
// Block Management
// ============================================================================

/// Create a new block
/// Args: ctx (i64)
pub fn rt_cranelift_create_block(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_create_block(ctx) };
    Ok(Value::Int(handle))
}

/// Switch to a block
/// Args: ctx (i64), block (i64)
pub fn rt_cranelift_switch_to_block(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Nil);
    }
    let ctx = value_to_i64(&args[0]);
    let block = value_to_i64(&args[1]);
    unsafe { cranelift_ffi::rt_cranelift_switch_to_block(ctx, block) };
    Ok(Value::Nil)
}

/// Seal a block
/// Args: ctx (i64), block (i64)
pub fn rt_cranelift_seal_block(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Nil);
    }
    let ctx = value_to_i64(&args[0]);
    let block = value_to_i64(&args[1]);
    unsafe { cranelift_ffi::rt_cranelift_seal_block(ctx, block) };
    Ok(Value::Nil)
}

/// Seal all blocks
/// Args: ctx (i64)
pub fn rt_cranelift_seal_all_blocks(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Ok(Value::Nil);
    }
    let ctx = value_to_i64(&args[0]);
    unsafe { cranelift_ffi::rt_cranelift_seal_all_blocks(ctx) };
    Ok(Value::Nil)
}

/// Append a block parameter
/// Args: ctx (i64), block (i64), type_ (i64)
pub fn rt_cranelift_append_block_param(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let block = value_to_i64(&args[1]);
    let type_ = value_to_i64(&args[2]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_append_block_param(ctx, block, type_) };
    Ok(Value::Int(handle))
}

/// Get a block parameter value
/// Args: ctx (i64), block (i64), index (i64)
pub fn rt_cranelift_block_param(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let block = value_to_i64(&args[1]);
    let index = value_to_i64(&args[2]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_block_param(ctx, block, index) };
    Ok(Value::Int(handle))
}

// ============================================================================
// Constants
// ============================================================================

/// Create an integer constant
/// Args: ctx (i64), type_ (i64), value (i64)
pub fn rt_cranelift_iconst(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let type_ = value_to_i64(&args[1]);
    let val = value_to_i64(&args[2]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_iconst(ctx, type_, val) };
    Ok(Value::Int(handle))
}

/// Create a float constant
/// Args: ctx (i64), type_ (i64), value (f64)
pub fn rt_cranelift_fconst(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let type_ = value_to_i64(&args[1]);
    let val = value_to_f64(&args[2]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_fconst(ctx, type_, val) };
    Ok(Value::Int(handle))
}

/// Create a boolean constant
/// Args: ctx (i64), value (bool)
pub fn rt_cranelift_bconst(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let val = value_to_bool(&args[1]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_bconst(ctx, val) };
    Ok(Value::Int(handle))
}

/// Create a null pointer constant
/// Args: ctx (i64), type_ (i64)
pub fn rt_cranelift_null(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let type_ = value_to_i64(&args[1]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_null(ctx, type_) };
    Ok(Value::Int(handle))
}

// ============================================================================
// Arithmetic Operations (binary)
// ============================================================================

macro_rules! impl_binop_wrapper {
    ($wrapper_name:ident, $ffi_name:ident) => {
        pub fn $wrapper_name(args: &[Value]) -> Result<Value, CompileError> {
            if args.len() < 3 {
                return Ok(Value::Int(0));
            }
            let ctx = value_to_i64(&args[0]);
            let a = value_to_i64(&args[1]);
            let b = value_to_i64(&args[2]);
            let handle = unsafe { cranelift_ffi::$ffi_name(ctx, a, b) };
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
    if args.len() < 2 {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let a = value_to_i64(&args[1]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_bnot(ctx, a) };
    Ok(Value::Int(handle))
}

// ============================================================================
// Comparison Operations
// ============================================================================

/// Integer comparison
/// Args: ctx (i64), cond (i64), a (i64), b (i64)
pub fn rt_cranelift_icmp(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 4 {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let cond = value_to_i64(&args[1]);
    let a = value_to_i64(&args[2]);
    let b = value_to_i64(&args[3]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_icmp(ctx, cond, a, b) };
    Ok(Value::Int(handle))
}

/// Float comparison
/// Args: ctx (i64), cond (i64), a (i64), b (i64)
pub fn rt_cranelift_fcmp(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 4 {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let cond = value_to_i64(&args[1]);
    let a = value_to_i64(&args[2]);
    let b = value_to_i64(&args[3]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_fcmp(ctx, cond, a, b) };
    Ok(Value::Int(handle))
}

// ============================================================================
// Memory Operations
// ============================================================================

/// Load from memory
/// Args: ctx (i64), type_ (i64), addr (i64), offset (i64)
pub fn rt_cranelift_load(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 4 {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let type_ = value_to_i64(&args[1]);
    let addr = value_to_i64(&args[2]);
    let offset = value_to_i64(&args[3]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_load(ctx, type_, addr, offset) };
    Ok(Value::Int(handle))
}

/// Store to memory
/// Args: ctx (i64), value (i64), addr (i64), offset (i64)
pub fn rt_cranelift_store(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 4 {
        return Ok(Value::Nil);
    }
    let ctx = value_to_i64(&args[0]);
    let val = value_to_i64(&args[1]);
    let addr = value_to_i64(&args[2]);
    let offset = value_to_i64(&args[3]);
    unsafe { cranelift_ffi::rt_cranelift_store(ctx, val, addr, offset) };
    Ok(Value::Nil)
}

/// Allocate stack slot
/// Args: ctx (i64), size (i64), align (i64)
pub fn rt_cranelift_stack_slot(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let size = value_to_i64(&args[1]);
    let align = value_to_i64(&args[2]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_stack_slot(ctx, size, align) };
    Ok(Value::Int(handle))
}

/// Get stack slot address
/// Args: ctx (i64), slot (i64), offset (i64)
pub fn rt_cranelift_stack_addr(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let slot = value_to_i64(&args[1]);
    let offset = value_to_i64(&args[2]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_stack_addr(ctx, slot, offset) };
    Ok(Value::Int(handle))
}

// ============================================================================
// Control Flow
// ============================================================================

/// Unconditional jump
/// Args: ctx (i64), block (i64)
pub fn rt_cranelift_jump(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Nil);
    }
    let ctx = value_to_i64(&args[0]);
    let block = value_to_i64(&args[1]);
    unsafe { cranelift_ffi::rt_cranelift_jump(ctx, block) };
    Ok(Value::Nil)
}

/// Conditional branch
/// Args: ctx (i64), cond (i64), then_block (i64), else_block (i64)
pub fn rt_cranelift_brif(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 4 {
        return Ok(Value::Nil);
    }
    let ctx = value_to_i64(&args[0]);
    let cond = value_to_i64(&args[1]);
    let then_block = value_to_i64(&args[2]);
    let else_block = value_to_i64(&args[3]);
    unsafe { cranelift_ffi::rt_cranelift_brif(ctx, cond, then_block, else_block) };
    Ok(Value::Nil)
}

/// Return with value
/// Args: ctx (i64), value (i64)
pub fn rt_cranelift_return(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Nil);
    }
    let ctx = value_to_i64(&args[0]);
    let val = value_to_i64(&args[1]);
    unsafe { cranelift_ffi::rt_cranelift_return(ctx, val) };
    Ok(Value::Nil)
}

/// Return void
/// Args: ctx (i64)
pub fn rt_cranelift_return_void(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Ok(Value::Nil);
    }
    let ctx = value_to_i64(&args[0]);
    unsafe { cranelift_ffi::rt_cranelift_return_void(ctx) };
    Ok(Value::Nil)
}

/// Trap (unreachable)
/// Args: ctx (i64), code (i64)
pub fn rt_cranelift_trap(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Nil);
    }
    let ctx = value_to_i64(&args[0]);
    let code = value_to_i64(&args[1]);
    unsafe { cranelift_ffi::rt_cranelift_trap(ctx, code) };
    Ok(Value::Nil)
}

// ============================================================================
// Function Calls
// ============================================================================

/// Call a function
/// Args: ctx (i64), func (i64), args_ptr (i64), args_len (i64)
pub fn rt_cranelift_call(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 4 {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let func = value_to_i64(&args[1]);
    let args_ptr = value_to_i64(&args[2]);
    let args_len = value_to_i64(&args[3]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_call(ctx, func, args_ptr, args_len) };
    Ok(Value::Int(handle))
}

/// Call indirect (through function pointer)
/// Args: ctx (i64), sig (i64), callee (i64), args_ptr (i64), args_len (i64)
pub fn rt_cranelift_call_indirect(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 5 {
        return Ok(Value::Int(0));
    }
    let ctx = value_to_i64(&args[0]);
    let sig = value_to_i64(&args[1]);
    let callee = value_to_i64(&args[2]);
    let args_ptr = value_to_i64(&args[3]);
    let args_len = value_to_i64(&args[4]);
    let handle = unsafe { cranelift_ffi::rt_cranelift_call_indirect(ctx, sig, callee, args_ptr, args_len) };
    Ok(Value::Int(handle))
}

// ============================================================================
// Type Conversions
// ============================================================================

macro_rules! impl_conv_wrapper {
    ($wrapper_name:ident, $ffi_name:ident) => {
        pub fn $wrapper_name(args: &[Value]) -> Result<Value, CompileError> {
            if args.len() < 3 {
                return Ok(Value::Int(0));
            }
            let ctx = value_to_i64(&args[0]);
            let to_type = value_to_i64(&args[1]);
            let value = value_to_i64(&args[2]);
            let handle = unsafe { cranelift_ffi::$ffi_name(ctx, to_type, value) };
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
impl_conv_wrapper!(rt_cranelift_bitcast, rt_cranelift_bitcast);

// ============================================================================
// JIT Execution
// ============================================================================

/// Get JIT function pointer
/// Args: module (i64), name_ptr (i64), name_len (i64)
pub fn rt_cranelift_get_function_ptr(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Ok(Value::Int(0));
    }
    let module = value_to_i64(&args[0]);
    let name_ptr = value_to_i64(&args[1]);
    let name_len = value_to_i64(&args[2]);
    let ptr = unsafe { cranelift_ffi::rt_cranelift_get_function_ptr(module, name_ptr, name_len) };
    Ok(Value::Int(ptr))
}

/// Call JIT function pointer
/// Args: func_ptr (i64), args_ptr (i64), args_len (i64)
pub fn rt_cranelift_call_function_ptr(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 3 {
        return Ok(Value::Int(0));
    }
    let func_ptr = value_to_i64(&args[0]);
    let args_ptr = value_to_i64(&args[1]);
    let args_len = value_to_i64(&args[2]);
    let result = unsafe { cranelift_ffi::rt_cranelift_call_function_ptr(func_ptr, args_ptr, args_len) };
    Ok(Value::Int(result))
}

// ============================================================================
// Bootstrap Test FFI
// ============================================================================

/// Execute shell command
pub fn rt_exec(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Ok(Value::Int(-1));
    }
    let cmd = value_to_runtime_string(&args[0]);
    let result = simple_runtime::value::cli_ffi::rt_exec(cmd);
    Ok(Value::Int(result as i64))
}

/// Get file hash
pub fn rt_file_hash(args: &[Value]) -> Result<Value, CompileError> {
    if args.is_empty() {
        return Ok(Value::Str(String::new()));
    }
    let path = value_to_runtime_string(&args[0]);
    let result = simple_runtime::value::cli_ffi::rt_file_hash(path);
    Ok(runtime_string_to_value(result))
}

/// Write file
pub fn rt_write_file(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() < 2 {
        return Ok(Value::Bool(false));
    }
    let path = value_to_runtime_string(&args[0]);
    let content = value_to_runtime_string(&args[1]);
    let result = simple_runtime::value::cli_ffi::rt_write_file(path, content);
    Ok(Value::Bool(result))
}

//! Package management extern functions
//! Provides access to package SFFI operations from Simple code

use crate::error::CompileError;
use crate::value::Value;
use std::os::raw::c_char;

// Import SFFI functions from runtime.
//
// These take Simple `text` as an explicit (ptr, len) pair, matching every
// other text-taking runtime entry point (rt_file_*, rt_dir_*). They used to
// take `*const c_char`, which generated code cannot satisfy: Simple heap
// strings carry no trailing NUL (see runtime alloc_runtime_string), so the
// JIT had no sound way to pass one and the whole family failed closed. See
// doc/08_tracking/bug/rt_package_chmod_family_fails_from_jit_key_left_world_readable_2026-08-08.md
extern "C" {
    // Returns a runtime-owned Simple `text` (RuntimeValue), not a C string.
    // See runtime/src/value/sffi/package.rs::rt_package_sha256.
    fn rt_package_sha256(file_path: *const u8, file_path_len: usize) -> simple_runtime::value::RuntimeValue;
    fn rt_package_create_tarball(
        source_dir: *const u8,
        source_dir_len: usize,
        output_path: *const u8,
        output_path_len: usize,
    ) -> i32;
    fn rt_package_extract_tarball(
        tarball_path: *const u8,
        tarball_path_len: usize,
        dest_dir: *const u8,
        dest_dir_len: usize,
    ) -> i32;
    fn rt_package_file_size(file_path: *const u8, file_path_len: usize) -> i64;
    fn rt_package_copy_file(src_path: *const u8, src_path_len: usize, dst_path: *const u8, dst_path_len: usize) -> i32;
    fn rt_package_mkdir_all(dir_path: *const u8, dir_path_len: usize) -> i32;
    fn rt_package_remove_dir_all(dir_path: *const u8, dir_path_len: usize) -> i32;
    fn rt_package_create_symlink(
        target: *const u8,
        target_len: usize,
        link_path: *const u8,
        link_path_len: usize,
    ) -> i32;
    fn rt_package_chmod(file_path: *const u8, file_path_len: usize, mode: u32) -> i32;
    fn rt_package_exists(path: *const u8, path_len: usize) -> i32;
    fn rt_package_is_dir(path: *const u8, path_len: usize) -> i32;
    fn rt_package_free_string(ptr: *mut c_char);
    // Runtime string accessors, used to read the RuntimeValue text that
    // rt_package_sha256 now returns. Declared as C symbols rather than via
    // `simple_runtime::value::collections::*` because that module is private.
    fn rt_string_data(value: simple_runtime::value::RuntimeValue) -> *const u8;
    fn rt_string_len(value: simple_runtime::value::RuntimeValue) -> u64;
}

/// Borrow a Simple `text` Value as a `&str` for the (ptr, len) runtime ABI.
fn value_to_text(val: &Value) -> Result<&str, CompileError> {
    match val {
        Value::Str(s) => Ok(s.as_str()),
        _ => Err(CompileError::semantic(format!(
            "Expected text, got {}",
            val.type_name()
        ))),
    }
}

/// Convert Value to i32
fn value_to_i32(val: &Value) -> Result<i32, CompileError> {
    match val {
        Value::Int(n) => Ok(*n as i32),
        _ => Err(CompileError::semantic(format!("Expected int, got {}", val.type_name()))),
    }
}

pub fn sha256(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::semantic(format!(
            "rt_package_sha256 expects 1 argument, got {}",
            args.len()
        )));
    }

    let path = value_to_text(&args[0])?;

    unsafe {
        let rv = rt_package_sha256(path.as_ptr(), path.len());
        if rv == simple_runtime::value::RuntimeValue::NIL {
            return Err(CompileError::semantic("Failed to calculate checksum".to_string()));
        }

        // The result is a runtime-owned Simple string: read it through the
        // runtime's own (data, len) accessors. There is deliberately no free
        // call here — the runtime owns the allocation (see the rt_package_sha256
        // doc comment), so freeing it would be a double-free.
        let data = rt_string_data(rv);
        let len = rt_string_len(rv) as usize;
        if data.is_null() {
            return Err(CompileError::semantic("Failed to calculate checksum".to_string()));
        }
        let bytes = std::slice::from_raw_parts(data, len);
        let result = String::from_utf8_lossy(bytes).to_string();

        Ok(Value::text(result))
    }
}

pub fn create_tarball(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::semantic(format!(
            "rt_package_create_tarball expects 2 arguments, got {}",
            args.len()
        )));
    }

    let source = value_to_text(&args[0])?;
    let output = value_to_text(&args[1])?;

    unsafe {
        let result = rt_package_create_tarball(source.as_ptr(), source.len(), output.as_ptr(), output.len());
        Ok(Value::Int(result as i64))
    }
}

pub fn extract_tarball(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::semantic(format!(
            "rt_package_extract_tarball expects 2 arguments, got {}",
            args.len()
        )));
    }

    let tarball = value_to_text(&args[0])?;
    let dest = value_to_text(&args[1])?;

    unsafe {
        let result = rt_package_extract_tarball(tarball.as_ptr(), tarball.len(), dest.as_ptr(), dest.len());
        Ok(Value::Int(result as i64))
    }
}

pub fn file_size(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::semantic(format!(
            "rt_package_file_size expects 1 argument, got {}",
            args.len()
        )));
    }

    let path = value_to_text(&args[0])?;

    unsafe {
        let result = rt_package_file_size(path.as_ptr(), path.len());
        Ok(Value::Int(result))
    }
}

pub fn copy_file(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::semantic(format!(
            "rt_package_copy_file expects 2 arguments, got {}",
            args.len()
        )));
    }

    let src = value_to_text(&args[0])?;
    let dst = value_to_text(&args[1])?;

    unsafe {
        let result = rt_package_copy_file(src.as_ptr(), src.len(), dst.as_ptr(), dst.len());
        Ok(Value::Int(result as i64))
    }
}

pub fn mkdir_all(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::semantic(format!(
            "rt_package_mkdir_all expects 1 argument, got {}",
            args.len()
        )));
    }

    let path = value_to_text(&args[0])?;

    unsafe {
        let result = rt_package_mkdir_all(path.as_ptr(), path.len());
        Ok(Value::Int(result as i64))
    }
}

pub fn remove_dir_all(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::semantic(format!(
            "rt_package_remove_dir_all expects 1 argument, got {}",
            args.len()
        )));
    }

    let path = value_to_text(&args[0])?;

    unsafe {
        let result = rt_package_remove_dir_all(path.as_ptr(), path.len());
        Ok(Value::Int(result as i64))
    }
}

pub fn create_symlink(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::semantic(format!(
            "rt_package_create_symlink expects 2 arguments, got {}",
            args.len()
        )));
    }

    let target = value_to_text(&args[0])?;
    let link = value_to_text(&args[1])?;

    unsafe {
        let result = rt_package_create_symlink(target.as_ptr(), target.len(), link.as_ptr(), link.len());
        Ok(Value::Int(result as i64))
    }
}

pub fn chmod(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::semantic(format!(
            "rt_package_chmod expects 2 arguments, got {}",
            args.len()
        )));
    }

    let path = value_to_text(&args[0])?;
    let mode = value_to_i32(&args[1])?;

    unsafe {
        let result = rt_package_chmod(path.as_ptr(), path.len(), mode as u32);
        Ok(Value::Int(result as i64))
    }
}

pub fn exists(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::semantic(format!(
            "rt_package_exists expects 1 argument, got {}",
            args.len()
        )));
    }

    let path = value_to_text(&args[0])?;

    unsafe {
        let result = rt_package_exists(path.as_ptr(), path.len());
        Ok(Value::Int(result as i64))
    }
}

pub fn is_dir(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::semantic(format!(
            "rt_package_is_dir expects 1 argument, got {}",
            args.len()
        )));
    }

    let path = value_to_text(&args[0])?;

    unsafe {
        let result = rt_package_is_dir(path.as_ptr(), path.len());
        Ok(Value::Int(result as i64))
    }
}

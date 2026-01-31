//! Package management extern functions
//! Provides access to package FFI operations from Simple code

use crate::error::CompileError;
use crate::value::Value;
use std::ffi::CString;
use std::os::raw::c_char;

// Import FFI functions from runtime
extern "C" {
    fn rt_package_sha256(file_path: *const c_char) -> *mut c_char;
    fn rt_package_create_tarball(source_dir: *const c_char, output_path: *const c_char) -> i32;
    fn rt_package_extract_tarball(tarball_path: *const c_char, dest_dir: *const c_char) -> i32;
    fn rt_package_file_size(file_path: *const c_char) -> i64;
    fn rt_package_copy_file(src_path: *const c_char, dst_path: *const c_char) -> i32;
    fn rt_package_mkdir_all(dir_path: *const c_char) -> i32;
    fn rt_package_remove_dir_all(dir_path: *const c_char) -> i32;
    fn rt_package_create_symlink(target: *const c_char, link_path: *const c_char) -> i32;
    fn rt_package_chmod(file_path: *const c_char, mode: u32) -> i32;
    fn rt_package_exists(path: *const c_char) -> i32;
    fn rt_package_is_dir(path: *const c_char) -> i32;
    fn rt_package_free_string(ptr: *mut c_char);
}

/// Convert Value to C string
fn value_to_cstring(val: &Value) -> Result<CString, CompileError> {
    match val {
        Value::Str(s) => CString::new(s.as_str())
            .map_err(|_| CompileError::semantic("Invalid string (contains null byte)".to_string())),
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
        _ => Err(CompileError::semantic(format!(
            "Expected int, got {}",
            val.type_name()
        ))),
    }
}

pub fn sha256(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::semantic(format!(
            "rt_package_sha256 expects 1 argument, got {}",
            args.len()
        )));
    }

    let path = value_to_cstring(&args[0])?;

    unsafe {
        let result_ptr = rt_package_sha256(path.as_ptr());
        if result_ptr.is_null() {
            return Err(CompileError::semantic(
                "Failed to calculate checksum".to_string(),
            ));
        }

        let c_str = std::ffi::CStr::from_ptr(result_ptr);
        let result = c_str.to_string_lossy().to_string();
        rt_package_free_string(result_ptr);

        Ok(Value::Str(result))
    }
}

pub fn create_tarball(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 2 {
        return Err(CompileError::semantic(format!(
            "rt_package_create_tarball expects 2 arguments, got {}",
            args.len()
        )));
    }

    let source = value_to_cstring(&args[0])?;
    let output = value_to_cstring(&args[1])?;

    unsafe {
        let result = rt_package_create_tarball(source.as_ptr(), output.as_ptr());
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

    let tarball = value_to_cstring(&args[0])?;
    let dest = value_to_cstring(&args[1])?;

    unsafe {
        let result = rt_package_extract_tarball(tarball.as_ptr(), dest.as_ptr());
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

    let path = value_to_cstring(&args[0])?;

    unsafe {
        let result = rt_package_file_size(path.as_ptr());
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

    let src = value_to_cstring(&args[0])?;
    let dst = value_to_cstring(&args[1])?;

    unsafe {
        let result = rt_package_copy_file(src.as_ptr(), dst.as_ptr());
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

    let path = value_to_cstring(&args[0])?;

    unsafe {
        let result = rt_package_mkdir_all(path.as_ptr());
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

    let path = value_to_cstring(&args[0])?;

    unsafe {
        let result = rt_package_remove_dir_all(path.as_ptr());
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

    let target = value_to_cstring(&args[0])?;
    let link = value_to_cstring(&args[1])?;

    unsafe {
        let result = rt_package_create_symlink(target.as_ptr(), link.as_ptr());
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

    let path = value_to_cstring(&args[0])?;
    let mode = value_to_i32(&args[1])?;

    unsafe {
        let result = rt_package_chmod(path.as_ptr(), mode as u32);
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

    let path = value_to_cstring(&args[0])?;

    unsafe {
        let result = rt_package_exists(path.as_ptr());
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

    let path = value_to_cstring(&args[0])?;

    unsafe {
        let result = rt_package_is_dir(path.as_ptr());
        Ok(Value::Int(result as i64))
    }
}

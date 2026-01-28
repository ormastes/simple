//! File I/O FFI functions for the interpreter
//!
//! This module provides interpreter implementations for the rt_* file I/O functions
//! that are declared in simple/std_lib/src/infra/file_io.spl.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use std::collections::HashMap;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::Path;

// Helper to create Option::Some(value)
fn make_some(value: Value) -> Value {
    Value::Enum {
        enum_name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: Some(Box::new(value)),
    }
}

// Helper to create Option::None
fn make_none() -> Value {
    Value::Enum {
        enum_name: "Option".to_string(),
        variant: "None".to_string(),
        payload: None,
    }
}

// Helper to extract path from first argument
fn extract_path(args: &[Value], idx: usize) -> Result<String, CompileError> {
    match args.get(idx) {
        Some(Value::Str(s)) => Ok(s.clone()),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("Argument must be a string path");
            Err(CompileError::semantic_with_context(
                format!("file_io: argument {} must be a string path", idx),
                ctx,
            ))
        }
    }
}

// Helper to extract content string
fn extract_content(args: &[Value], idx: usize) -> Result<String, CompileError> {
    match args.get(idx) {
        Some(Value::Str(s)) => Ok(s.clone()),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("Argument must be a string");
            Err(CompileError::semantic_with_context(
                format!("file_io: argument {} must be a string", idx),
                ctx,
            ))
        }
    }
}

// ============================================================================
// File Metadata
// ============================================================================

/// Check if file exists
pub fn rt_file_exists(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    Ok(Value::Bool(Path::new(&path).exists()))
}

/// Get file stat info (simplified - returns size or -1)
pub fn rt_file_stat(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::metadata(&path) {
        Ok(meta) => Ok(Value::Int(meta.len() as i64)),
        Err(_) => Ok(Value::Int(-1)),
    }
}

// ============================================================================
// File Operations
// ============================================================================

/// Canonicalize path
pub fn rt_file_canonicalize(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::canonicalize(&path) {
        Ok(canonical) => Ok(Value::Str(canonical.to_string_lossy().to_string())),
        Err(_) => {
            // Fallback: make absolute
            match std::env::current_dir() {
                Ok(cwd) => {
                    let abs = cwd.join(&path);
                    Ok(Value::Str(abs.to_string_lossy().to_string()))
                }
                Err(_) => Ok(Value::Str(path)),
            }
        }
    }
}

/// Read file as text
pub fn rt_file_read_text(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::read_to_string(&path) {
        Ok(content) => Ok(make_some(Value::Str(content))),
        Err(_) => Ok(make_none()),
    }
}

/// Write text to file
pub fn rt_file_write_text(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let content = extract_content(args, 1)?;
    match fs::write(&path, &content) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Copy file
pub fn rt_file_copy(args: &[Value]) -> Result<Value, CompileError> {
    let src = extract_path(args, 0)?;
    let dest = extract_path(args, 1)?;
    match fs::copy(&src, &dest) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Remove file
pub fn rt_file_remove(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::remove_file(&path) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Rename file
pub fn rt_file_rename(args: &[Value]) -> Result<Value, CompileError> {
    let from = extract_path(args, 0)?;
    let to = extract_path(args, 1)?;
    match fs::rename(&from, &to) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Read file as lines
pub fn rt_file_read_lines(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::read_to_string(&path) {
        Ok(content) => {
            let lines: Vec<Value> = content.lines().map(|l| Value::Str(l.to_string())).collect();
            Ok(make_some(Value::Array(lines)))
        }
        Err(_) => Ok(make_none()),
    }
}

/// Append text to file
pub fn rt_file_append_text(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let content = extract_content(args, 1)?;
    match OpenOptions::new().create(true).append(true).open(&path) {
        Ok(mut file) => match file.write_all(content.as_bytes()) {
            Ok(_) => Ok(Value::Bool(true)),
            Err(_) => Ok(Value::Bool(false)),
        },
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Read file as bytes
pub fn rt_file_read_bytes(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::read(&path) {
        Ok(bytes) => {
            let arr: Vec<Value> = bytes.into_iter().map(|b| Value::Int(b as i64)).collect();
            Ok(make_some(Value::Array(arr)))
        }
        Err(_) => Ok(make_none()),
    }
}

/// Write bytes to file
pub fn rt_file_write_bytes(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let bytes_arr = match args.get(1) {
        Some(Value::Array(arr)) => arr,
        _ => return Ok(Value::Bool(false)),
    };

    let bytes: Vec<u8> = bytes_arr
        .iter()
        .filter_map(|v| match v {
            Value::Int(i) => Some(*i as u8),
            _ => None,
        })
        .collect();

    match fs::write(&path, &bytes) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Move file (works across filesystems)
pub fn rt_file_move(args: &[Value]) -> Result<Value, CompileError> {
    let src = extract_path(args, 0)?;
    let dest = extract_path(args, 1)?;

    // Try rename first
    if fs::rename(&src, &dest).is_ok() {
        return Ok(Value::Bool(true));
    }

    // Fallback: copy + delete
    if fs::copy(&src, &dest).is_ok() {
        if fs::remove_file(&src).is_ok() {
            return Ok(Value::Bool(true));
        }
    }

    Ok(Value::Bool(false))
}

// ============================================================================
// Directory Operations
// ============================================================================

/// Create directory
pub fn rt_dir_create(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::create_dir(&path) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// List directory
pub fn rt_dir_list(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::read_dir(&path) {
        Ok(entries) => {
            let names: Vec<Value> = entries
                .flatten()
                .filter_map(|e| e.file_name().into_string().ok())
                .map(Value::Str)
                .collect();
            Ok(make_some(Value::Array(names)))
        }
        Err(_) => Ok(make_none()),
    }
}

/// Remove directory
pub fn rt_dir_remove(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::remove_dir(&path) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Find files (simplified)
pub fn rt_file_find(args: &[Value]) -> Result<Value, CompileError> {
    let dir = extract_path(args, 0)?;
    let pattern = extract_path(args, 1)?;

    fn matches_pattern(filename: &str, pattern: &str) -> bool {
        if pattern == "*" {
            return true;
        }
        if let Some(ext) = pattern.strip_prefix("*.") {
            return filename.ends_with(&format!(".{}", ext));
        }
        if let Some(prefix) = pattern.strip_suffix('*') {
            return filename.starts_with(prefix);
        }
        if let Some(suffix) = pattern.strip_prefix('*') {
            return filename.ends_with(suffix);
        }
        filename == pattern
    }

    match fs::read_dir(&dir) {
        Ok(entries) => {
            let matches: Vec<Value> = entries
                .flatten()
                .filter_map(|e| {
                    let name = e.file_name().into_string().ok()?;
                    if matches_pattern(&name, &pattern) {
                        Some(Value::Str(e.path().to_string_lossy().to_string()))
                    } else {
                        None
                    }
                })
                .collect();
            Ok(Value::Array(matches))
        }
        Err(_) => Ok(Value::Array(vec![])),
    }
}

/// Glob directory
pub fn rt_dir_glob(args: &[Value]) -> Result<Value, CompileError> {
    rt_file_find(args)
}

/// Create directory with all parents
pub fn rt_dir_create_all(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::create_dir_all(&path) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Walk directory recursively
pub fn rt_dir_walk(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;

    fn walk_recursive(dir: &Path, results: &mut Vec<Value>) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                results.push(Value::Str(path.to_string_lossy().to_string()));
                if path.is_dir() {
                    walk_recursive(&path, results);
                }
            }
        }
    }

    let mut results = Vec::new();
    walk_recursive(Path::new(&path), &mut results);
    Ok(Value::Array(results))
}

/// Get current directory
pub fn rt_current_dir(_args: &[Value]) -> Result<Value, CompileError> {
    match std::env::current_dir() {
        Ok(cwd) => Ok(make_some(Value::Str(cwd.to_string_lossy().to_string()))),
        Err(_) => Ok(make_none()),
    }
}

/// Set current directory
pub fn rt_set_current_dir(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match std::env::set_current_dir(&path) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Protected paths list
const PROTECTED_PATHS: &[&str] = &[
    "/", "/home", "/usr", "/bin", "/sbin", "/etc", "/var", "/tmp", "/opt", "/lib", "/lib64", "/boot", "/dev", "/proc",
    "/sys", "/root",
];

fn is_protected_path(path: &Path) -> bool {
    let components: Vec<_> = path.components().collect();
    if components.len() <= 2 {
        return true;
    }

    let path_str = path.to_string_lossy();
    for protected in PROTECTED_PATHS {
        if path_str.as_ref() == *protected {
            return true;
        }
    }

    if let Some(home) = std::env::var_os("HOME") {
        if path == Path::new(&home) {
            return true;
        }
    }

    false
}

/// Remove directory recursively (with safety)
pub fn rt_dir_remove_all(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let path_obj = Path::new(&path);

    // Canonicalize first
    let canonical = match path_obj.canonicalize() {
        Ok(p) => p,
        Err(_) => return Ok(Value::Bool(false)),
    };

    if is_protected_path(&canonical) {
        eprintln!(
            "rt_dir_remove_all: Refusing to remove protected path: {}",
            canonical.display()
        );
        return Ok(Value::Bool(false));
    }

    match fs::remove_dir_all(&canonical) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

// ============================================================================
// File Descriptor Operations
// ============================================================================

/// Open file
pub fn rt_file_open(args: &[Value]) -> Result<Value, CompileError> {
    let _path = extract_path(args, 0)?;
    // Simplified - return -1 (not implemented for interpreter)
    Ok(Value::Int(-1))
}

/// Get file size
pub fn rt_file_get_size(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(-1))
}

/// Close file
pub fn rt_file_close(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(false))
}

// ============================================================================
// Path Operations
// ============================================================================

/// Get basename
pub fn rt_path_basename(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let basename = Path::new(&path).file_name().and_then(|s| s.to_str()).unwrap_or("");
    Ok(Value::Str(basename.to_string()))
}

/// Get dirname
pub fn rt_path_dirname(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let dirname = Path::new(&path).parent().and_then(|p| p.to_str()).unwrap_or("");
    Ok(Value::Str(dirname.to_string()))
}

/// Get extension
pub fn rt_path_ext(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let ext = Path::new(&path).extension().and_then(|s| s.to_str()).unwrap_or("");
    Ok(Value::Str(ext.to_string()))
}

/// Get absolute path
pub fn rt_path_absolute(args: &[Value]) -> Result<Value, CompileError> {
    rt_file_canonicalize(args)
}

/// Get path separator
pub fn rt_path_separator(_args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(target_os = "windows")]
    return Ok(Value::Str("\\".to_string()));
    #[cfg(not(target_os = "windows"))]
    Ok(Value::Str("/".to_string()))
}

/// Get file stem
pub fn rt_path_stem(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let stem = Path::new(&path).file_stem().and_then(|s| s.to_str()).unwrap_or("");
    Ok(Value::Str(stem.to_string()))
}

/// Get relative path
pub fn rt_path_relative(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let base = extract_path(args, 1)?;

    let path_obj = Path::new(&path);
    let base_obj = Path::new(&base);

    match path_obj.strip_prefix(base_obj) {
        Ok(relative) => Ok(Value::Str(relative.to_string_lossy().to_string())),
        Err(_) => Ok(Value::Str(path)),
    }
}

/// Join paths
pub fn rt_path_join(args: &[Value]) -> Result<Value, CompileError> {
    let path1 = extract_path(args, 0)?;
    let path2 = extract_path(args, 1)?;

    let joined = Path::new(&path1).join(&path2);
    Ok(Value::Str(joined.to_string_lossy().to_string()))
}

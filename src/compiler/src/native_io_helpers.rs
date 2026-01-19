//! Helper functions for native I/O implementations
//!
//! This module provides:
//! - Option/Result value construction helpers
//! - IoError enum construction
//! - Value extraction utilities for function arguments

use std::collections::HashMap;
use std::io::{self, ErrorKind};

use crate::error::CompileError;
use crate::value::Value;

//==============================================================================
// Option Helpers
//==============================================================================

/// Helper to create an Option::Some value
pub fn make_option_some(value: Value) -> Value {
    Value::Enum {
        enum_name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: Some(Box::new(value)),
    }
}

/// Helper to create an Option::None value
pub fn make_option_none() -> Value {
    Value::Enum {
        enum_name: "Option".to_string(),
        variant: "None".to_string(),
        payload: None,
    }
}

/// Helper to create an optional timestamp field from SystemTime
pub fn make_timestamp_option(time_result: io::Result<std::time::SystemTime>) -> Value {
    match time_result {
        Ok(time) => {
            if let Ok(duration) = time.duration_since(std::time::UNIX_EPOCH) {
                make_option_some(Value::Int(duration.as_nanos() as i64))
            } else {
                make_option_none()
            }
        }
        Err(_) => make_option_none(),
    }
}

//==============================================================================
// IoError Helpers
//==============================================================================

fn make_io_error(err: io::Error) -> Value {
    let variant = match err.kind() {
        ErrorKind::NotFound => "NotFound",
        ErrorKind::PermissionDenied => "PermissionDenied",
        ErrorKind::AlreadyExists => "AlreadyExists",
        ErrorKind::InvalidInput => "InvalidPath",
        ErrorKind::IsADirectory => "IsDirectory",
        ErrorKind::NotADirectory => "NotDirectory",
        ErrorKind::DirectoryNotEmpty => "DirectoryNotEmpty",
        ErrorKind::ReadOnlyFilesystem => "ReadOnly",
        ErrorKind::StorageFull => "OutOfSpace",
        ErrorKind::Interrupted => "Interrupted",
        ErrorKind::TimedOut => "TimedOut",
        ErrorKind::ConnectionRefused => "ConnectionRefused",
        ErrorKind::ConnectionReset => "ConnectionReset",
        ErrorKind::BrokenPipe => "BrokenPipe",
        ErrorKind::WouldBlock => "WouldBlock",
        ErrorKind::InvalidData => "InvalidData",
        ErrorKind::UnexpectedEof => "UnexpectedEof",
        _ => {
            return Value::Enum {
                enum_name: "IoError".to_string(),
                variant: "Other".to_string(),
                payload: Some(Box::new(Value::Str(err.to_string()))),
            };
        }
    };

    Value::Enum {
        enum_name: "IoError".to_string(),
        variant: variant.to_string(),
        payload: None,
    }
}

pub fn io_ok(val: Value) -> Value {
    Value::Enum {
        enum_name: "Result".to_string(),
        variant: "Ok".to_string(),
        payload: Some(Box::new(val)),
    }
}

pub fn io_err(err: io::Error) -> Value {
    Value::Enum {
        enum_name: "Result".to_string(),
        variant: "Err".to_string(),
        payload: Some(Box::new(make_io_error(err))),
    }
}

pub fn io_err_msg(msg: &str) -> Value {
    Value::Enum {
        enum_name: "Result".to_string(),
        variant: "Err".to_string(),
        payload: Some(Box::new(Value::Enum {
            enum_name: "IoError".to_string(),
            variant: "Other".to_string(),
            payload: Some(Box::new(Value::Str(msg.to_string()))),
        })),
    }
}

//==============================================================================
// Value Extraction Helpers
//==============================================================================

pub fn extract_path(args: &[Value], idx: usize) -> Result<String, CompileError> {
    args.get(idx)
        .and_then(|v| match v {
            Value::Str(s) => Some(s.clone()),
            Value::Symbol(s) => Some(s.clone()),
            // Unit types and other string-like values
            _ => None,
        })
        .ok_or_else(|| crate::error::factory::argument_must_be(idx, "a path string"))
}

pub fn extract_bytes(args: &[Value], idx: usize) -> Result<Vec<u8>, CompileError> {
    match args.get(idx) {
        Some(Value::Array(arr)) => {
            let mut bytes = Vec::with_capacity(arr.len());
            for v in arr {
                match v {
                    Value::Int(i) => bytes.push(*i as u8),
                    _ => return Err(CompileError::Semantic("byte array must contain integers".into())),
                }
            }
            Ok(bytes)
        }
        Some(Value::Str(s)) => Ok(s.as_bytes().to_vec()),
        _ => Err(crate::error::factory::argument_must_be(idx, "bytes or string")),
    }
}

pub fn extract_bool(args: &[Value], idx: usize) -> bool {
    args.get(idx).map(|v| v.truthy()).unwrap_or(false)
}

pub fn extract_int(args: &[Value], idx: usize) -> Result<i64, CompileError> {
    args.get(idx)
        .and_then(|v| v.as_int().ok())
        .ok_or_else(|| crate::error::factory::argument_must_be(idx, "an integer"))
}

pub fn extract_open_mode(args: &[Value], idx: usize) -> Result<String, CompileError> {
    match args.get(idx) {
        Some(Value::Enum { variant, .. }) => Ok(variant.clone()),
        Some(Value::Str(s)) => Ok(s.clone()),
        _ => Err(crate::error::factory::argument_must_be(idx, "an OpenMode")),
    }
}

//==============================================================================
// FileMetadata and DirEntry creation helpers
//==============================================================================

/// Create a FileMetadata Value from std::fs::Metadata
pub fn create_file_metadata(meta: &std::fs::Metadata) -> Value {
    let mut fields = HashMap::new();
    fields.insert("size".to_string(), Value::Int(meta.len() as i64));
    fields.insert("readonly".to_string(), Value::Bool(meta.permissions().readonly()));

    // File type
    let file_type = if meta.is_file() {
        "File"
    } else if meta.is_dir() {
        "Directory"
    } else if meta.file_type().is_symlink() {
        "Symlink"
    } else {
        "Other"
    };
    fields.insert(
        "file_type".to_string(),
        Value::Enum {
            enum_name: "FileType".to_string(),
            variant: file_type.to_string(),
            payload: None,
        },
    );

    // Timestamps (as Option)
    fields.insert("modified".to_string(), make_timestamp_option(meta.modified()));
    fields.insert("created".to_string(), make_timestamp_option(meta.created()));
    fields.insert("accessed".to_string(), make_timestamp_option(meta.accessed()));

    // Permissions (Unix mode)
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fields.insert("permissions".to_string(), Value::Int(meta.permissions().mode() as i64));
    }
    #[cfg(not(unix))]
    {
        fields.insert("permissions".to_string(), Value::Int(0o644));
    }

    Value::Object {
        class: "FileMetadata".to_string(),
        fields,
    }
}

/// Create a DirEntry Value from std::fs::DirEntry
pub fn create_dir_entry(entry: &std::fs::DirEntry) -> Value {
    let mut fields = HashMap::new();
    fields.insert(
        "path".to_string(),
        Value::Str(entry.path().to_string_lossy().to_string()),
    );
    fields.insert(
        "name".to_string(),
        Value::Str(entry.file_name().to_string_lossy().to_string()),
    );

    // Determine file type
    let ft = entry.file_type().ok();
    let file_type = match ft {
        Some(t) if t.is_file() => "File",
        Some(t) if t.is_dir() => "Directory",
        Some(t) if t.is_symlink() => "Symlink",
        _ => "Other",
    };
    fields.insert(
        "file_type".to_string(),
        Value::Enum {
            enum_name: "FileType".to_string(),
            variant: file_type.to_string(),
            payload: None,
        },
    );

    Value::Object {
        class: "DirEntry".to_string(),
        fields,
    }
}

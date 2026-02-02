//! Regex FFI functions for the interpreter

use crate::error::CompileError;
use crate::value::Value;

/// ffi_regex_is_match(pattern, text) -> bool
pub fn is_match(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    match regex::Regex::new(&pattern) {
        Ok(re) => Ok(Value::Bool(re.is_match(&text))),
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

/// ffi_regex_find(pattern, text) -> [text, start, end] or []
pub fn find(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    match regex::Regex::new(&pattern) {
        Ok(re) => {
            if let Some(m) = re.find(&text) {
                Ok(Value::Array(vec![
                    Value::Str(m.as_str().to_string()),
                    Value::Int(m.start() as i64),
                    Value::Int(m.end() as i64),
                ]))
            } else {
                Ok(Value::Array(vec![]))
            }
        }
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

/// ffi_regex_find_all(pattern, text) -> [[text, start, end], ...]
pub fn find_all(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    match regex::Regex::new(&pattern) {
        Ok(re) => {
            let results: Vec<Value> = re
                .find_iter(&text)
                .map(|m| {
                    Value::Array(vec![
                        Value::Str(m.as_str().to_string()),
                        Value::Int(m.start() as i64),
                        Value::Int(m.end() as i64),
                    ])
                })
                .collect();
            Ok(Value::Array(results))
        }
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

/// ffi_regex_captures(pattern, text) -> [full_match, group1, ...] or []
pub fn captures(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    match regex::Regex::new(&pattern) {
        Ok(re) => {
            if let Some(caps) = re.captures(&text) {
                let results: Vec<Value> = caps
                    .iter()
                    .map(|m| match m {
                        Some(m) => Value::Str(m.as_str().to_string()),
                        None => Value::Nil,
                    })
                    .collect();
                Ok(Value::Array(results))
            } else {
                Ok(Value::Array(vec![]))
            }
        }
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

/// ffi_regex_replace(pattern, text, replacement) -> text
pub fn replace(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    let replacement = args.get(2).map(|v| v.to_display_string()).unwrap_or_default();
    match regex::Regex::new(&pattern) {
        Ok(re) => Ok(Value::Str(re.replace(&text, replacement.as_str()).to_string())),
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

/// ffi_regex_replace_all(pattern, text, replacement) -> text
pub fn replace_all(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    let replacement = args.get(2).map(|v| v.to_display_string()).unwrap_or_default();
    match regex::Regex::new(&pattern) {
        Ok(re) => Ok(Value::Str(re.replace_all(&text, replacement.as_str()).to_string())),
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

/// ffi_regex_split(pattern, text) -> [text]
pub fn split(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    match regex::Regex::new(&pattern) {
        Ok(re) => {
            let parts: Vec<Value> = re.split(&text).map(|s| Value::Str(s.to_string())).collect();
            Ok(Value::Array(parts))
        }
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

/// ffi_regex_split_n(pattern, text, limit) -> [text]
pub fn split_n(args: &[Value]) -> Result<Value, CompileError> {
    let pattern = args.first().map(|v| v.to_display_string()).unwrap_or_default();
    let text = args.get(1).map(|v| v.to_display_string()).unwrap_or_default();
    let limit = args.get(2).and_then(|v| v.as_int().ok()).unwrap_or(0) as usize;
    match regex::Regex::new(&pattern) {
        Ok(re) => {
            let parts: Vec<Value> = re.splitn(&text, limit).map(|s| Value::Str(s.to_string())).collect();
            Ok(Value::Array(parts))
        }
        Err(e) => Err(CompileError::semantic(format!("invalid regex pattern: {}", e))),
    }
}

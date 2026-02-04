//! JSON FFI functions for the interpreter
//!
//! This module provides JSON parsing and serialization using serde_json.
//! Supports the extern functions declared in src/std/json.spl:
//! - json_parse(text) -> Result<JsonValue, SimpleError>
//! - json_serialize(JsonValue) -> text
//! - json_pretty(JsonValue, indent) -> text
//! - parse_int(text) -> i64?

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use serde_json::{Map, Number, Value as JsonValue};
use std::collections::HashMap;

// ============================================================================
// Helper Functions
// ============================================================================

/// Extract string from args at given index
fn extract_string(args: &[Value], idx: usize) -> Result<String, CompileError> {
    match args.get(idx) {
        Some(Value::Str(s)) => Ok(s.clone()),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("Argument must be a string");
            Err(CompileError::semantic_with_context(
                format!("json: argument {} must be a string", idx),
                ctx,
            ))
        }
    }
}

/// Extract integer from args at given index
fn extract_int(args: &[Value], idx: usize) -> Result<i64, CompileError> {
    match args.get(idx) {
        Some(Value::Int(n)) => Ok(*n),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("Argument must be an integer");
            Err(CompileError::semantic_with_context(
                format!("json: argument {} must be an integer", idx),
                ctx,
            ))
        }
    }
}

/// Create Result::Ok(value)
fn make_ok(value: Value) -> Value {
    Value::Enum {
        enum_name: "Result".to_string(),
        variant: "Ok".to_string(),
        payload: Some(Box::new(value)),
    }
}

/// Create Result::Err(SimpleError)
fn make_err(msg: String) -> Value {
    let error = Value::Enum {
        enum_name: "SimpleError".to_string(),
        variant: "ParseError".to_string(),
        payload: Some(Box::new(Value::Str(msg))),
    };
    Value::Enum {
        enum_name: "Result".to_string(),
        variant: "Err".to_string(),
        payload: Some(Box::new(error)),
    }
}

/// Create Option::Some(value)
fn make_some(value: Value) -> Value {
    Value::Enum {
        enum_name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: Some(Box::new(value)),
    }
}

/// Create Option::None
fn make_none() -> Value {
    Value::Enum {
        enum_name: "Option".to_string(),
        variant: "None".to_string(),
        payload: None,
    }
}

// ============================================================================
// JSON <-> Simple Value Conversion
// ============================================================================

/// Convert serde_json::Value to Simple's JsonValue enum
fn json_to_simple(json: JsonValue) -> Value {
    match json {
        JsonValue::Null => Value::Enum {
            enum_name: "JsonValue".to_string(),
            variant: "Null".to_string(),
            payload: None,
        },
        JsonValue::Bool(b) => Value::Enum {
            enum_name: "JsonValue".to_string(),
            variant: "Bool".to_string(),
            payload: Some(Box::new(Value::Bool(b))),
        },
        JsonValue::Number(n) => {
            let f = n.as_f64().unwrap_or(0.0);
            Value::Enum {
                enum_name: "JsonValue".to_string(),
                variant: "Number".to_string(),
                payload: Some(Box::new(Value::Float(f))),
            }
        }
        JsonValue::String(s) => Value::Enum {
            enum_name: "JsonValue".to_string(),
            variant: "String".to_string(),
            payload: Some(Box::new(Value::Str(s))),
        },
        JsonValue::Array(arr) => {
            let items: Vec<Value> = arr.into_iter().map(json_to_simple).collect();
            Value::Enum {
                enum_name: "JsonValue".to_string(),
                variant: "Array".to_string(),
                payload: Some(Box::new(Value::Array(items))),
            }
        }
        JsonValue::Object(obj) => {
            let mut map: HashMap<String, Value> = HashMap::new();
            for (k, v) in obj {
                map.insert(k, json_to_simple(v));
            }
            Value::Enum {
                enum_name: "JsonValue".to_string(),
                variant: "Object".to_string(),
                payload: Some(Box::new(Value::Dict(map))),
            }
        }
    }
}

/// Convert Simple's JsonValue enum back to serde_json::Value
fn simple_to_json(value: &Value) -> JsonValue {
    match value {
        Value::Enum {
            enum_name,
            variant,
            payload,
        } if enum_name == "JsonValue" => match variant.as_str() {
            "Null" => JsonValue::Null,
            "Bool" => {
                if let Some(p) = payload {
                    if let Value::Bool(b) = **p {
                        return JsonValue::Bool(b);
                    }
                }
                JsonValue::Null
            }
            "Number" => {
                if let Some(p) = payload {
                    match **p {
                        Value::Float(f) => {
                            return Number::from_f64(f).map(JsonValue::Number).unwrap_or(JsonValue::Null);
                        }
                        Value::Int(i) => {
                            return JsonValue::Number(Number::from(i));
                        }
                        _ => {}
                    }
                }
                JsonValue::Null
            }
            "String" => {
                if let Some(p) = payload {
                    if let Value::Str(s) = &**p {
                        return JsonValue::String(s.clone());
                    }
                }
                JsonValue::Null
            }
            "Array" => {
                if let Some(p) = payload {
                    if let Value::Array(arr) = &**p {
                        let json_arr: Vec<JsonValue> = arr.iter().map(simple_to_json).collect();
                        return JsonValue::Array(json_arr);
                    }
                }
                JsonValue::Null
            }
            "Object" => {
                if let Some(p) = payload {
                    if let Value::Dict(dict) = &**p {
                        let mut json_obj = Map::new();
                        for (k, v) in dict {
                            json_obj.insert(k.clone(), simple_to_json(v));
                        }
                        return JsonValue::Object(json_obj);
                    }
                }
                JsonValue::Null
            }
            _ => JsonValue::Null,
        },
        _ => JsonValue::Null,
    }
}

// ============================================================================
// FFI Functions
// ============================================================================

/// Parse JSON text to JsonValue
///
/// Args:
///     args[0]: text - JSON string to parse
///
/// Returns:
///     Result<JsonValue, SimpleError>
pub fn json_parse(args: &[Value]) -> Result<Value, CompileError> {
    let text = extract_string(args, 0)?;

    match serde_json::from_str::<JsonValue>(&text) {
        Ok(json) => {
            let json_value = json_to_simple(json);
            Ok(make_ok(json_value))
        }
        Err(e) => {
            let error_msg = format!("JSON parse error: {}", e);
            Ok(make_err(error_msg))
        }
    }
}

/// Serialize JsonValue to compact JSON text
///
/// Args:
///     args[0]: JsonValue - value to serialize
///
/// Returns:
///     text - JSON string
pub fn json_serialize(args: &[Value]) -> Result<Value, CompileError> {
    let value = args.get(0).ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("json_serialize requires 1 argument");
        CompileError::semantic_with_context("json_serialize: missing argument", ctx)
    })?;

    let json_value = simple_to_json(value);
    let json_str = serde_json::to_string(&json_value).unwrap_or_else(|_| "null".to_string());
    Ok(Value::Str(json_str))
}

/// Serialize JsonValue to pretty-printed JSON text
///
/// Args:
///     args[0]: JsonValue - value to serialize
///     args[1]: usize - indentation size (number of spaces)
///
/// Returns:
///     text - Pretty-printed JSON string
pub fn json_pretty(args: &[Value]) -> Result<Value, CompileError> {
    let value = args.get(0).ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::ARGUMENT_COUNT_MISMATCH)
            .with_help("json_pretty requires 2 arguments");
        CompileError::semantic_with_context("json_pretty: missing argument", ctx)
    })?;

    // Note: indent parameter is accepted but serde_json::to_string_pretty
    // uses 2-space indent by default. Could be customized in future.
    let _indent = extract_int(args, 1).unwrap_or(2);

    let json_value = simple_to_json(value);
    let json_str = serde_json::to_string_pretty(&json_value).unwrap_or_else(|_| "null".to_string());
    Ok(Value::Str(json_str))
}

/// Parse integer from text
///
/// Args:
///     args[0]: text - string to parse
///
/// Returns:
///     Option<i64> - Some(number) or None
pub fn parse_int(args: &[Value]) -> Result<Value, CompileError> {
    let text = extract_string(args, 0)?;

    match text.trim().parse::<i64>() {
        Ok(n) => Ok(make_some(Value::Int(n))),
        Err(_) => Ok(make_none()),
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_json_parse_primitives() {
        // Parse null
        let args = vec![Value::Str("null".to_string())];
        let result = json_parse(&args).unwrap();
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Ok"));

        // Parse bool
        let args = vec![Value::Str("true".to_string())];
        let result = json_parse(&args).unwrap();
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Ok"));

        // Parse number
        let args = vec![Value::Str("42".to_string())];
        let result = json_parse(&args).unwrap();
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Ok"));

        // Parse string
        let args = vec![Value::Str(r#""hello""#.to_string())];
        let result = json_parse(&args).unwrap();
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Ok"));
    }

    #[test]
    fn test_json_parse_array() {
        let args = vec![Value::Str(r#"[1, 2, 3]"#.to_string())];
        let result = json_parse(&args).unwrap();
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Ok"));
    }

    #[test]
    fn test_json_parse_object() {
        let args = vec![Value::Str(r#"{"name": "Alice", "age": 30}"#.to_string())];
        let result = json_parse(&args).unwrap();
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Ok"));
    }

    #[test]
    fn test_json_parse_error() {
        let args = vec![Value::Str("{invalid json}".to_string())];
        let result = json_parse(&args).unwrap();
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Err"));
    }

    #[test]
    fn test_parse_int() {
        // Valid integer
        let args = vec![Value::Str("42".to_string())];
        let result = parse_int(&args).unwrap();
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Some"));

        // Invalid integer
        let args = vec![Value::Str("not_a_number".to_string())];
        let result = parse_int(&args).unwrap();
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "None"));
    }
}

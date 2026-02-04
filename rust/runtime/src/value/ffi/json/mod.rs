//! JSON parsing and serialization FFI for Simple runtime.
//!
//! Provides JSON operations using serde_json:
//! - `json_parse` - Parse JSON text to JsonValue (interpreter Value enum)
//! - `json_serialize` - Serialize JsonValue to compact JSON text
//! - `json_pretty` - Serialize JsonValue to pretty-printed JSON
//! - `parse_int` - Parse integer from text

use serde_json::{Map, Number, Value as JsonValue};
use std::collections::HashMap;

// Value is the interpreter's runtime value type
use crate::value::Value;

// ============================================================================
// Helper: Convert serde_json::Value to interpreter Value (JsonValue enum)
// ============================================================================

/// Convert serde_json::Value to Simple's JsonValue enum representation.
///
/// The Simple-side JsonValue enum (in src/std/json.spl) is defined as:
/// ```simple
/// enum JsonValue:
///     Object({text: JsonValue})
///     Array([JsonValue])
///     String(text)
///     Number(f64)
///     Bool(bool)
///     Null
/// ```
///
/// This maps to interpreter Value::Enum with variants.
fn json_to_simple_value(json: JsonValue) -> Value {
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
            let items: Vec<Value> = arr.into_iter().map(json_to_simple_value).collect();
            Value::Enum {
                enum_name: "JsonValue".to_string(),
                variant: "Array".to_string(),
                payload: Some(Box::new(Value::Array(items))),
            }
        }
        JsonValue::Object(obj) => {
            let mut map: HashMap<String, Value> = HashMap::new();
            for (k, v) in obj {
                map.insert(k, json_to_simple_value(v));
            }
            Value::Enum {
                enum_name: "JsonValue".to_string(),
                variant: "Object".to_string(),
                payload: Some(Box::new(Value::Dict(map))),
            }
        }
    }
}

// ============================================================================
// Helper: Convert Simple JsonValue enum to serde_json::Value
// ============================================================================

/// Convert Simple's JsonValue enum back to serde_json::Value.
///
/// Handles the enum structure created by json_parse.
fn simple_value_to_json(value: &Value) -> JsonValue {
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
                    if let Value::Float(f) = **p {
                        return Number::from_f64(f).map(JsonValue::Number).unwrap_or(JsonValue::Null);
                    }
                    if let Value::Int(i) = **p {
                        return JsonValue::Number(Number::from(i));
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
                        let json_arr: Vec<JsonValue> = arr.iter().map(simple_value_to_json).collect();
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
                            json_obj.insert(k.clone(), simple_value_to_json(v));
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

/// Parse JSON text to JsonValue.
///
/// Args:
///     text: JSON string to parse
///
/// Returns:
///     Ok(JsonValue) on success, Err(error message) on parse failure
///
/// Simple signature: `extern fn json_parse(text: text) -> Result<JsonValue, SimpleError>`
#[no_mangle]
pub extern "C" fn json_parse(text: &str) -> Value {
    match serde_json::from_str::<JsonValue>(text) {
        Ok(json) => {
            // Return Ok(JsonValue)
            let json_value = json_to_simple_value(json);
            Value::Enum {
                enum_name: "Result".to_string(),
                variant: "Ok".to_string(),
                payload: Some(Box::new(json_value)),
            }
        }
        Err(e) => {
            // Return Err(SimpleError)
            let error_msg = format!("JSON parse error: {}", e);
            let error = Value::Enum {
                enum_name: "SimpleError".to_string(),
                variant: "ParseError".to_string(),
                payload: Some(Box::new(Value::Str(error_msg))),
            };
            Value::Enum {
                enum_name: "Result".to_string(),
                variant: "Err".to_string(),
                payload: Some(Box::new(error)),
            }
        }
    }
}

/// Serialize JsonValue to compact JSON text.
///
/// Args:
///     value: JsonValue to serialize
///
/// Returns:
///     JSON string (compact, no whitespace)
///
/// Simple signature: `extern fn json_serialize(value: JsonValue) -> text`
#[no_mangle]
pub extern "C" fn json_serialize(value: &Value) -> String {
    let json_value = simple_value_to_json(value);
    serde_json::to_string(&json_value).unwrap_or_else(|_| "null".to_string())
}

/// Serialize JsonValue to pretty-printed JSON text.
///
/// Args:
///     value: JsonValue to serialize
///     indent: Number of spaces for indentation
///
/// Returns:
///     Pretty-printed JSON string
///
/// Simple signature: `extern fn json_pretty(value: JsonValue, indent: usize) -> text`
#[no_mangle]
pub extern "C" fn json_pretty(value: &Value, _indent: usize) -> String {
    // Note: serde_json::to_string_pretty uses 2-space indent by default
    // The indent parameter is accepted for future customization
    let json_value = simple_value_to_json(value);
    serde_json::to_string_pretty(&json_value).unwrap_or_else(|_| "null".to_string())
}

/// Parse integer from text.
///
/// Args:
///     text: String to parse
///
/// Returns:
///     Some(i64) on success, None on parse failure
///
/// Simple signature: `extern fn parse_int(text: text) -> i64?`
#[no_mangle]
pub extern "C" fn parse_int(text: &str) -> Value {
    match text.trim().parse::<i64>() {
        Ok(n) => Value::Enum {
            enum_name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: Some(Box::new(Value::Int(n))),
        },
        Err(_) => Value::Enum {
            enum_name: "Option".to_string(),
            variant: "None".to_string(),
            payload: None,
        },
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
        let result = json_parse("null");
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Ok"));

        // Parse bool
        let result = json_parse("true");
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Ok"));

        // Parse number
        let result = json_parse("42");
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Ok"));

        // Parse string
        let result = json_parse(r#""hello""#);
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Ok"));
    }

    #[test]
    fn test_json_parse_array() {
        let result = json_parse(r#"[1, 2, 3]"#);
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Ok"));
    }

    #[test]
    fn test_json_parse_object() {
        let result = json_parse(r#"{"name": "Alice", "age": 30}"#);
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Ok"));
    }

    #[test]
    fn test_json_parse_error() {
        let result = json_parse("{invalid json}");
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Err"));
    }

    #[test]
    fn test_parse_int() {
        // Valid integer
        let result = parse_int("42");
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "Some"));

        // Invalid integer
        let result = parse_int("not_a_number");
        assert!(matches!(result, Value::Enum { variant, .. } if variant == "None"));
    }
}

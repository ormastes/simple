//! SDN FFI functions for the Simple language interpreter

use crate::error::CompileError;
use crate::value::Value;
use simple_sdn::{SdnDocument, SdnValue};
use std::path::Path;

/// SDN version string
const SDN_VERSION: &str = "sdn 0.1.0";

/// Get SDN version
pub fn rt_sdn_version(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Str(SDN_VERSION.to_string()))
}

/// Check/validate an SDN file
pub fn rt_sdn_check(args: &[Value]) -> Result<Value, CompileError> {
    let path = match args.first() {
        Some(Value::Str(s)) => s.clone(),
        _ => return Ok(Value::Int(1)),
    };

    match simple_sdn::parse_file(Path::new(&path)) {
        Ok(_) => Ok(Value::Int(0)),
        Err(e) => {
            eprintln!("error: Parse error: {}", e);
            Ok(Value::Int(1))
        }
    }
}

/// Convert SDN file to JSON string
pub fn rt_sdn_to_json(args: &[Value]) -> Result<Value, CompileError> {
    let path = match args.first() {
        Some(Value::Str(s)) => s.clone(),
        _ => return Ok(Value::Str(String::new())),
    };

    match SdnDocument::from_file(Path::new(&path)) {
        Ok(doc) => Ok(Value::Str(doc.to_json())),
        Err(e) => {
            eprintln!("error: Parse error: {}", e);
            Ok(Value::Str(String::new()))
        }
    }
}

/// Convert JSON file to SDN string
pub fn rt_sdn_from_json(args: &[Value]) -> Result<Value, CompileError> {
    let path = match args.first() {
        Some(Value::Str(s)) => s.clone(),
        _ => return Ok(Value::Str(String::new())),
    };

    let content = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: Read error: {}", e);
            return Ok(Value::Str(String::new()));
        }
    };

    match serde_json::from_str::<serde_json::Value>(&content) {
        Ok(json) => {
            let sdn = json_to_sdn(&json);
            Ok(Value::Str(format_sdn_value(&sdn)))
        }
        Err(e) => {
            eprintln!("error: JSON parse error: {}", e);
            Ok(Value::Str(String::new()))
        }
    }
}

/// Get value at path from SDN file
pub fn rt_sdn_get(args: &[Value]) -> Result<Value, CompileError> {
    let (path, key) = match (args.first(), args.get(1)) {
        (Some(Value::Str(p)), Some(Value::Str(k))) => (p.clone(), k.clone()),
        _ => return Ok(Value::Str(String::new())),
    };

    match SdnDocument::from_file(Path::new(&path)) {
        Ok(doc) => match doc.get(&key) {
            Some(value) => Ok(Value::Str(format_sdn_value(value))),
            None => Ok(Value::Str(String::new())),
        },
        Err(e) => {
            eprintln!("error: Parse error: {}", e);
            Ok(Value::Str(String::new()))
        }
    }
}

/// Set value at path in SDN file
pub fn rt_sdn_set(args: &[Value]) -> Result<Value, CompileError> {
    let (path, key, value) = match (args.first(), args.get(1), args.get(2)) {
        (Some(Value::Str(p)), Some(Value::Str(k)), Some(Value::Str(v))) => (p.clone(), k.clone(), v.clone()),
        _ => return Ok(Value::Int(1)),
    };

    let mut doc = match SdnDocument::from_file(Path::new(&path)) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("error: Parse error: {}", e);
            return Ok(Value::Int(1));
        }
    };

    let sdn_value = parse_value_string(&value);
    if let Err(e) = doc.set(&key, sdn_value) {
        eprintln!("error: Set error: {}", e);
        return Ok(Value::Int(1));
    }

    if let Err(e) = doc.write_file(Path::new(&path)) {
        eprintln!("error: Write error: {}", e);
        return Ok(Value::Int(1));
    }

    Ok(Value::Int(0))
}

/// Format SDN file
pub fn rt_sdn_fmt(args: &[Value]) -> Result<Value, CompileError> {
    let path = match args.first() {
        Some(Value::Str(s)) => s.clone(),
        _ => return Ok(Value::Int(1)),
    };

    let doc = match SdnDocument::from_file(Path::new(&path)) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("error: Parse error: {}", e);
            return Ok(Value::Int(1));
        }
    };

    if let Err(e) = doc.write_file(Path::new(&path)) {
        eprintln!("error: Write error: {}", e);
        return Ok(Value::Int(1));
    }

    Ok(Value::Int(0))
}

// === Helper functions ===

fn format_sdn_value(value: &SdnValue) -> String {
    match value {
        SdnValue::Null => "null".to_string(),
        SdnValue::Bool(b) => b.to_string(),
        SdnValue::Int(i) => i.to_string(),
        SdnValue::Float(f) => f.to_string(),
        SdnValue::String(s) => s.clone(),
        SdnValue::Array(arr) => {
            let items: Vec<String> = arr.iter().map(format_sdn_value).collect();
            format!("[{}]", items.join(", "))
        }
        SdnValue::Dict(dict) => {
            let items: Vec<String> = dict
                .iter()
                .map(|(k, v)| format!("{}: {}", k, format_sdn_value(v)))
                .collect();
            format!("{{{}}}", items.join(", "))
        }
        SdnValue::Table { fields, rows, .. } => {
            let mut result = String::new();
            if let Some(fields) = fields {
                result.push_str(&format!("|{}|", fields.join(", ")));
            }
            for row in rows {
                let items: Vec<String> = row.iter().map(format_sdn_value).collect();
                result.push_str(&format!("\n    {}", items.join(", ")));
            }
            result
        }
    }
}

fn parse_value_string(s: &str) -> SdnValue {
    if s == "null" || s == "nil" {
        return SdnValue::Null;
    }
    if s == "true" {
        return SdnValue::Bool(true);
    }
    if s == "false" {
        return SdnValue::Bool(false);
    }
    if let Ok(i) = s.parse::<i64>() {
        return SdnValue::Int(i);
    }
    if let Ok(f) = s.parse::<f64>() {
        return SdnValue::Float(f);
    }
    SdnValue::String(s.to_string())
}

fn json_to_sdn(json: &serde_json::Value) -> SdnValue {
    match json {
        serde_json::Value::Null => SdnValue::Null,
        serde_json::Value::Bool(b) => SdnValue::Bool(*b),
        serde_json::Value::Number(n) => {
            if let Some(i) = n.as_i64() {
                SdnValue::Int(i)
            } else if let Some(f) = n.as_f64() {
                SdnValue::Float(f)
            } else {
                SdnValue::Null
            }
        }
        serde_json::Value::String(s) => SdnValue::String(s.clone()),
        serde_json::Value::Array(arr) => SdnValue::array(arr.iter().map(json_to_sdn).collect()),
        serde_json::Value::Object(obj) => {
            let mut dict = indexmap::IndexMap::new();
            for (k, v) in obj {
                dict.insert(k.clone(), json_to_sdn(v));
            }
            SdnValue::Dict(dict)
        }
    }
}

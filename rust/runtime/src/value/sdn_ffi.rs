//! SDN FFI functions for Simple programs
//!
//! These functions provide SDN file operations that Simple programs can call.

use super::{rt_string_new, RuntimeValue};
use simple_sdn::{SdnDocument, SdnValue};
use std::path::Path;

/// SDN version string
const SDN_VERSION: &str = "sdn 0.1.0";

/// Get SDN version
#[no_mangle]
pub extern "C" fn rt_sdn_version() -> RuntimeValue {
    rt_string_new(SDN_VERSION.as_ptr(), SDN_VERSION.len() as u64)
}

/// Check/validate an SDN file
/// Returns 0 on success, 1 on error
#[no_mangle]
pub extern "C" fn rt_sdn_check(path: RuntimeValue) -> i64 {
    let path_str = match runtime_value_to_string(path) {
        Some(s) => s,
        None => return 1,
    };

    match simple_sdn::parse_file(Path::new(&path_str)) {
        Ok(_) => 0,
        Err(e) => {
            eprintln!("error: Parse error: {}", e);
            1
        }
    }
}

/// Convert SDN file to JSON string
#[no_mangle]
pub extern "C" fn rt_sdn_to_json(path: RuntimeValue) -> RuntimeValue {
    let path_str = match runtime_value_to_string(path) {
        Some(s) => s,
        None => return rt_string_new(std::ptr::null(), 0),
    };

    match SdnDocument::from_file(Path::new(&path_str)) {
        Ok(doc) => {
            let json = doc.to_json();
            rt_string_new(json.as_ptr(), json.len() as u64)
        }
        Err(e) => {
            eprintln!("error: Parse error: {}", e);
            rt_string_new(std::ptr::null(), 0)
        }
    }
}

/// Convert JSON file to SDN string
#[no_mangle]
pub extern "C" fn rt_sdn_from_json(path: RuntimeValue) -> RuntimeValue {
    let path_str = match runtime_value_to_string(path) {
        Some(s) => s,
        None => return rt_string_new(std::ptr::null(), 0),
    };

    let content = match std::fs::read_to_string(&path_str) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: Read error: {}", e);
            return rt_string_new(std::ptr::null(), 0);
        }
    };

    // Parse JSON and convert to SDN
    match serde_json::from_str::<serde_json::Value>(&content) {
        Ok(json) => {
            let sdn = json_to_sdn(&json);
            let sdn_str = format_sdn_value(&sdn);
            rt_string_new(sdn_str.as_ptr(), sdn_str.len() as u64)
        }
        Err(e) => {
            eprintln!("error: JSON parse error: {}", e);
            rt_string_new(std::ptr::null(), 0)
        }
    }
}

/// Get value at path from SDN file
#[no_mangle]
pub extern "C" fn rt_sdn_get(path: RuntimeValue, key: RuntimeValue) -> RuntimeValue {
    let path_str = match runtime_value_to_string(path) {
        Some(s) => s,
        None => return rt_string_new(std::ptr::null(), 0),
    };
    let key_str = match runtime_value_to_string(key) {
        Some(s) => s,
        None => return rt_string_new(std::ptr::null(), 0),
    };

    match SdnDocument::from_file(Path::new(&path_str)) {
        Ok(doc) => match doc.get(&key_str) {
            Some(value) => {
                let s = format_sdn_value(value);
                rt_string_new(s.as_ptr(), s.len() as u64)
            }
            None => rt_string_new(std::ptr::null(), 0),
        },
        Err(e) => {
            eprintln!("error: Parse error: {}", e);
            rt_string_new(std::ptr::null(), 0)
        }
    }
}

/// Set value at path in SDN file
/// Returns 0 on success, 1 on error
#[no_mangle]
pub extern "C" fn rt_sdn_set(path: RuntimeValue, key: RuntimeValue, value: RuntimeValue) -> i64 {
    let path_str = match runtime_value_to_string(path) {
        Some(s) => s,
        None => return 1,
    };
    let key_str = match runtime_value_to_string(key) {
        Some(s) => s,
        None => return 1,
    };
    let value_str = match runtime_value_to_string(value) {
        Some(s) => s,
        None => return 1,
    };

    let mut doc = match SdnDocument::from_file(Path::new(&path_str)) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("error: Parse error: {}", e);
            return 1;
        }
    };

    let sdn_value = parse_value_string(&value_str);
    if let Err(e) = doc.set(&key_str, sdn_value) {
        eprintln!("error: Set error: {}", e);
        return 1;
    }

    if let Err(e) = doc.write_file(Path::new(&path_str)) {
        eprintln!("error: Write error: {}", e);
        return 1;
    }

    0
}

/// Format SDN file
/// Returns 0 on success, 1 on error
#[no_mangle]
pub extern "C" fn rt_sdn_fmt(path: RuntimeValue) -> i64 {
    let path_str = match runtime_value_to_string(path) {
        Some(s) => s,
        None => return 1,
    };

    let doc = match SdnDocument::from_file(Path::new(&path_str)) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("error: Parse error: {}", e);
            return 1;
        }
    };

    if let Err(e) = doc.write_file(Path::new(&path_str)) {
        eprintln!("error: Write error: {}", e);
        return 1;
    }

    0
}

// === Helper functions ===

fn runtime_value_to_string(value: RuntimeValue) -> Option<String> {
    let len = super::rt_string_len(value);
    if len <= 0 {
        return None;
    }
    let data = super::rt_string_data(value);
    if data.is_null() {
        return None;
    }
    unsafe {
        let slice = std::slice::from_raw_parts(data, len as usize);
        Some(String::from_utf8_lossy(slice).to_string())
    }
}

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
        serde_json::Value::Array(arr) => SdnValue::Array(arr.iter().map(json_to_sdn).collect()),
        serde_json::Value::Object(obj) => {
            let mut dict = indexmap::IndexMap::new();
            for (k, v) in obj {
                dict.insert(k.clone(), json_to_sdn(v));
            }
            SdnValue::Dict(dict)
        }
    }
}

//! SDN CLI - Command line interface for SDN files.
//!
//! Usage:
//!   sdn check <file>              Validate SDN file
//!   sdn to-json <file>            Convert SDN to JSON
//!   sdn from-json <file>          Convert JSON to SDN
//!   sdn get <file> <path>         Get value at path
//!   sdn set <file> <path> <value> Set value at path
//!   sdn fmt <file>                Format SDN file

use simple_sdn::{parse_file, SdnDocument, SdnValue};
use std::env;
use std::path::Path;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        print_usage();
        process::exit(1);
    }

    let result = match args[1].as_str() {
        "check" => cmd_check(&args[2..]),
        "to-json" => cmd_to_json(&args[2..]),
        "from-json" => cmd_from_json(&args[2..]),
        "get" => cmd_get(&args[2..]),
        "set" => cmd_set(&args[2..]),
        "fmt" => cmd_fmt(&args[2..]),
        "help" | "--help" | "-h" => {
            print_usage();
            Ok(())
        }
        "version" | "--version" | "-v" => {
            println!("sdn 0.1.0");
            Ok(())
        }
        _ => {
            eprintln!("Unknown command: {}", args[1]);
            print_usage();
            process::exit(1);
        }
    };

    if let Err(e) = result {
        eprintln!("Error: {}", e);
        process::exit(1);
    }
}

fn print_usage() {
    eprintln!(
        r#"SDN - Simple Data Notation CLI

Usage: sdn <command> [args]

Commands:
    check <file>                Validate SDN file
    to-json <file>              Convert SDN to JSON
    from-json <file>            Convert JSON to SDN (outputs to stdout)
    get <file> <path>           Get value at path (e.g., server.port)
    set <file> <path> <value>   Set value at path (modifies file)
    fmt <file>                  Format SDN file (modifies file)
    help                        Show this help message
    version                     Show version

Examples:
    sdn check config.sdn
    sdn to-json config.sdn > config.json
    sdn get config.sdn server.port
    sdn set config.sdn server.port 9090
    sdn fmt config.sdn
"#
    );
}

fn cmd_check(args: &[String]) -> Result<(), String> {
    if args.is_empty() {
        return Err("Usage: sdn check <file>".to_string());
    }

    let path = Path::new(&args[0]);
    match parse_file(path) {
        Ok(_) => {
            println!("OK: {}", args[0]);
            Ok(())
        }
        Err(e) => Err(format!("Parse error: {}", e)),
    }
}

fn cmd_to_json(args: &[String]) -> Result<(), String> {
    if args.is_empty() {
        return Err("Usage: sdn to-json <file>".to_string());
    }

    let path = Path::new(&args[0]);
    let doc = SdnDocument::from_file(path).map_err(|e| format!("Parse error: {}", e))?;

    println!("{}", doc.to_json());
    Ok(())
}

fn cmd_from_json(args: &[String]) -> Result<(), String> {
    if args.is_empty() {
        return Err("Usage: sdn from-json <file>".to_string());
    }

    let path = Path::new(&args[0]);
    let content = std::fs::read_to_string(path).map_err(|e| format!("Read error: {}", e))?;

    // Simple JSON parsing (basic implementation)
    let value = parse_json(&content)?;
    let doc = SdnDocument::parse(&format_as_sdn(&value))
        .map_err(|e| format!("Conversion error: {}", e))?;

    println!("{}", doc.to_sdn());
    Ok(())
}

fn cmd_get(args: &[String]) -> Result<(), String> {
    if args.len() < 2 {
        return Err("Usage: sdn get <file> <path>".to_string());
    }

    let path = Path::new(&args[0]);
    let doc = SdnDocument::from_file(path).map_err(|e| format!("Parse error: {}", e))?;

    match doc.get(&args[1]) {
        Some(value) => {
            println!("{}", format_value(value));
            Ok(())
        }
        None => Err(format!("Path not found: {}", args[1])),
    }
}

fn cmd_set(args: &[String]) -> Result<(), String> {
    if args.len() < 3 {
        return Err("Usage: sdn set <file> <path> <value>".to_string());
    }

    let file_path = Path::new(&args[0]);
    let mut doc = SdnDocument::from_file(file_path).map_err(|e| format!("Parse error: {}", e))?;

    let value = parse_value_string(&args[2])?;
    doc.set(&args[1], value)
        .map_err(|e| format!("Set error: {}", e))?;

    doc.write_file(file_path)
        .map_err(|e| format!("Write error: {}", e))?;

    println!("Updated: {} = {}", args[1], args[2]);
    Ok(())
}

fn cmd_fmt(args: &[String]) -> Result<(), String> {
    if args.is_empty() {
        return Err("Usage: sdn fmt <file>".to_string());
    }

    let file_path = Path::new(&args[0]);
    let doc = SdnDocument::from_file(file_path).map_err(|e| format!("Parse error: {}", e))?;

    doc.write_file(file_path)
        .map_err(|e| format!("Write error: {}", e))?;

    println!("Formatted: {}", args[0]);
    Ok(())
}

// === Helper functions ===

fn format_value(value: &SdnValue) -> String {
    match value {
        SdnValue::Null => "null".to_string(),
        SdnValue::Bool(b) => b.to_string(),
        SdnValue::Int(i) => i.to_string(),
        SdnValue::Float(f) => f.to_string(),
        SdnValue::String(s) => s.clone(),
        SdnValue::Array(arr) => {
            let items: Vec<String> = arr.iter().map(format_value).collect();
            format!("[{}]", items.join(", "))
        }
        SdnValue::Dict(dict) => {
            let items: Vec<String> = dict
                .iter()
                .map(|(k, v)| format!("{}: {}", k, format_value(v)))
                .collect();
            format!("{{{}}}", items.join(", "))
        }
        SdnValue::Table { fields, rows, .. } => {
            let mut result = String::new();
            if let Some(fields) = fields {
                result.push_str(&format!("|{}|", fields.join(", ")));
            }
            for row in rows {
                let items: Vec<String> = row.iter().map(format_value).collect();
                result.push_str(&format!("\n    {}", items.join(", ")));
            }
            result
        }
    }
}

fn parse_value_string(s: &str) -> Result<SdnValue, String> {
    // Try to parse as different types
    if s == "null" || s == "nil" {
        return Ok(SdnValue::Null);
    }
    if s == "true" {
        return Ok(SdnValue::Bool(true));
    }
    if s == "false" {
        return Ok(SdnValue::Bool(false));
    }
    if let Ok(i) = s.parse::<i64>() {
        return Ok(SdnValue::Int(i));
    }
    if let Ok(f) = s.parse::<f64>() {
        return Ok(SdnValue::Float(f));
    }
    // Default to string
    Ok(SdnValue::String(s.to_string()))
}

// Simple JSON parsing (basic implementation for common cases)
fn parse_json(s: &str) -> Result<SdnValue, String> {
    let s = s.trim();

    if s == "null" {
        return Ok(SdnValue::Null);
    }
    if s == "true" {
        return Ok(SdnValue::Bool(true));
    }
    if s == "false" {
        return Ok(SdnValue::Bool(false));
    }
    if let Ok(i) = s.parse::<i64>() {
        return Ok(SdnValue::Int(i));
    }
    if let Ok(f) = s.parse::<f64>() {
        return Ok(SdnValue::Float(f));
    }
    if s.starts_with('"') && s.ends_with('"') {
        return Ok(SdnValue::String(
            s[1..s.len() - 1]
                .replace("\\\"", "\"")
                .replace("\\n", "\n")
                .replace("\\t", "\t")
                .replace("\\\\", "\\"),
        ));
    }
    if s.starts_with('[') && s.ends_with(']') {
        let inner = &s[1..s.len() - 1];
        if inner.trim().is_empty() {
            return Ok(SdnValue::Array(vec![]));
        }
        let items = split_json_array(inner)?;
        let values: Result<Vec<SdnValue>, String> = items.iter().map(|i| parse_json(i)).collect();
        return Ok(SdnValue::Array(values?));
    }
    if s.starts_with('{') && s.ends_with('}') {
        let inner = &s[1..s.len() - 1];
        if inner.trim().is_empty() {
            return Ok(SdnValue::Dict(indexmap::IndexMap::new()));
        }
        let pairs = split_json_object(inner)?;
        let mut dict = indexmap::IndexMap::new();
        for (k, v) in pairs {
            let key = k.trim();
            if key.starts_with('"') && key.ends_with('"') {
                dict.insert(key[1..key.len() - 1].to_string(), parse_json(&v)?);
            }
        }
        return Ok(SdnValue::Dict(dict));
    }

    Err(format!("Cannot parse JSON value: {}", s))
}

fn split_json_array(s: &str) -> Result<Vec<String>, String> {
    let mut items = Vec::new();
    let mut current = String::new();
    let mut depth = 0;
    let mut in_string = false;
    let mut escape = false;

    for c in s.chars() {
        if escape {
            current.push(c);
            escape = false;
            continue;
        }
        if c == '\\' {
            current.push(c);
            escape = true;
            continue;
        }
        if c == '"' {
            in_string = !in_string;
            current.push(c);
            continue;
        }
        if in_string {
            current.push(c);
            continue;
        }
        match c {
            '[' | '{' => {
                depth += 1;
                current.push(c);
            }
            ']' | '}' => {
                depth -= 1;
                current.push(c);
            }
            ',' if depth == 0 => {
                items.push(current.trim().to_string());
                current = String::new();
            }
            _ => current.push(c),
        }
    }
    if !current.trim().is_empty() {
        items.push(current.trim().to_string());
    }
    Ok(items)
}

fn split_json_object(s: &str) -> Result<Vec<(String, String)>, String> {
    let mut pairs = Vec::new();
    let mut current_key = String::new();
    let mut current_value = String::new();
    let mut in_key = true;
    let mut depth = 0;
    let mut in_string = false;
    let mut escape = false;

    for c in s.chars() {
        if escape {
            if in_key {
                current_key.push(c);
            } else {
                current_value.push(c);
            }
            escape = false;
            continue;
        }
        if c == '\\' {
            if in_key {
                current_key.push(c);
            } else {
                current_value.push(c);
            }
            escape = true;
            continue;
        }
        if c == '"' {
            in_string = !in_string;
            if in_key {
                current_key.push(c);
            } else {
                current_value.push(c);
            }
            continue;
        }
        if in_string {
            if in_key {
                current_key.push(c);
            } else {
                current_value.push(c);
            }
            continue;
        }
        match c {
            '[' | '{' => {
                depth += 1;
                if !in_key {
                    current_value.push(c);
                }
            }
            ']' | '}' => {
                depth -= 1;
                if !in_key {
                    current_value.push(c);
                }
            }
            ':' if depth == 0 && in_key => {
                in_key = false;
            }
            ',' if depth == 0 => {
                pairs.push((
                    current_key.trim().to_string(),
                    current_value.trim().to_string(),
                ));
                current_key = String::new();
                current_value = String::new();
                in_key = true;
            }
            _ => {
                if in_key {
                    current_key.push(c);
                } else {
                    current_value.push(c);
                }
            }
        }
    }
    if !current_key.trim().is_empty() {
        pairs.push((
            current_key.trim().to_string(),
            current_value.trim().to_string(),
        ));
    }
    Ok(pairs)
}

fn format_as_sdn(value: &SdnValue) -> String {
    match value {
        SdnValue::Dict(dict) => {
            let mut result = String::new();
            for (k, v) in dict {
                match v {
                    SdnValue::Dict(_) | SdnValue::Array(_) => {
                        result.push_str(&format!("{}: {}\n", k, format_as_sdn(v)));
                    }
                    _ => {
                        result.push_str(&format!("{}: {}\n", k, format_as_sdn(v)));
                    }
                }
            }
            result
        }
        SdnValue::Array(arr) => {
            let items: Vec<String> = arr.iter().map(format_as_sdn).collect();
            format!("[{}]", items.join(", "))
        }
        SdnValue::String(s) => {
            if s.contains(char::is_whitespace) || s.contains(',') || s.contains(':') {
                format!("\"{}\"", s)
            } else {
                s.clone()
            }
        }
        _ => format!("{}", value),
    }
}

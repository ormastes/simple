//! Regex block handler for compiled regular expressions.
//!
//! Supports:
//! - Standard regex syntax (Rust regex crate compatible)
//! - Named capture groups: (?P<name>pattern)
//! - Flags: i (case insensitive), m (multiline), s (dotall), x (extended)
//! - Compile-time regex validation

use super::{BlockHandler, BlockResult};
use crate::error::CompileError;
use crate::value::Value;
use std::collections::HashMap;

/// Regex block handler
pub struct RegexBlock;

impl BlockHandler for RegexBlock {
    fn evaluate(&self, payload: &str) -> BlockResult {
        // Parse and validate the regex
        let regex_info = parse_regex(payload)?;

        // Return as a Block value with the parsed regex info
        Ok(Value::Block {
            kind: "re".to_string(),
            payload: payload.to_string(),
            result: Some(Box::new(regex_info)),
        })
    }

    fn kind(&self) -> &'static str {
        "re"
    }
}

/// Regex flags
#[derive(Debug, Clone, Default)]
pub struct RegexFlags {
    pub case_insensitive: bool, // i
    pub multiline: bool,        // m
    pub dotall: bool,           // s
    pub extended: bool,         // x
    pub unicode: bool,          // u
}

/// Parse a regex pattern and return a Value with metadata
fn parse_regex(payload: &str) -> Result<Value, CompileError> {
    let payload = payload.trim();

    if payload.is_empty() {
        return Err(CompileError::Semantic("empty regex pattern".into()));
    }

    // Extract flags if present (format: /pattern/flags or just pattern)
    let (pattern, flags) = extract_flags(payload);

    // Validate the regex pattern
    validate_regex(&pattern)?;

    // Extract named capture groups
    let capture_groups = extract_capture_groups(&pattern);

    // Build result structure
    let mut result = HashMap::new();
    result.insert("pattern".to_string(), Value::Str(pattern.clone()));
    result.insert(
        "flags".to_string(),
        Value::Dict({
            let mut flags_map = HashMap::new();
            flags_map.insert(
                "case_insensitive".to_string(),
                Value::Bool(flags.case_insensitive),
            );
            flags_map.insert("multiline".to_string(), Value::Bool(flags.multiline));
            flags_map.insert("dotall".to_string(), Value::Bool(flags.dotall));
            flags_map.insert("extended".to_string(), Value::Bool(flags.extended));
            flags_map.insert("unicode".to_string(), Value::Bool(flags.unicode));
            flags_map
        }),
    );
    result.insert(
        "capture_groups".to_string(),
        Value::Array(capture_groups.into_iter().map(Value::Str).collect()),
    );

    Ok(Value::Dict(result))
}

/// Extract flags from regex literal (e.g., /pattern/imsx)
fn extract_flags(payload: &str) -> (String, RegexFlags) {
    let mut flags = RegexFlags::default();

    // Check for /pattern/flags format
    if payload.starts_with('/') {
        if let Some(last_slash) = payload.rfind('/') {
            if last_slash > 0 {
                let pattern = payload[1..last_slash].to_string();
                let flag_str = &payload[last_slash + 1..];

                for ch in flag_str.chars() {
                    match ch {
                        'i' => flags.case_insensitive = true,
                        'm' => flags.multiline = true,
                        's' => flags.dotall = true,
                        'x' => flags.extended = true,
                        'u' => flags.unicode = true,
                        _ => {}
                    }
                }

                return (pattern, flags);
            }
        }
    }

    // Check for inline flags at start: (?imsx)pattern
    if payload.starts_with("(?") {
        let mut chars = payload.chars().skip(2).peekable();
        let mut inline_flags = String::new();

        while let Some(&ch) = chars.peek() {
            if ch == ')' {
                chars.next();
                break;
            }
            if ch == '-' || ch.is_alphabetic() {
                inline_flags.push(ch);
                chars.next();
            } else {
                break;
            }
        }

        // Check if this is just flags (not a group)
        let rest: String = chars.collect();
        if !inline_flags.is_empty() && !inline_flags.contains(':') {
            for ch in inline_flags.chars() {
                match ch {
                    'i' => flags.case_insensitive = true,
                    'm' => flags.multiline = true,
                    's' => flags.dotall = true,
                    'x' => flags.extended = true,
                    'u' => flags.unicode = true,
                    _ => {}
                }
            }
            return (rest, flags);
        }
    }

    (payload.to_string(), flags)
}

/// Validate regex syntax (basic validation)
fn validate_regex(pattern: &str) -> Result<(), CompileError> {
    // Check for balanced parentheses
    let mut paren_depth = 0;
    let mut bracket_depth = 0;
    let mut prev = ' ';

    for ch in pattern.chars() {
        // Skip escaped characters
        if prev == '\\' {
            prev = ch;
            continue;
        }

        match ch {
            '(' => paren_depth += 1,
            ')' => {
                paren_depth -= 1;
                if paren_depth < 0 {
                    return Err(CompileError::Semantic(
                        "unbalanced parentheses in regex".into(),
                    ));
                }
            }
            '[' => bracket_depth += 1,
            ']' => {
                if bracket_depth > 0 {
                    bracket_depth -= 1;
                }
            }
            _ => {}
        }
        prev = ch;
    }

    if paren_depth != 0 {
        return Err(CompileError::Semantic(
            "unbalanced parentheses in regex".into(),
        ));
    }

    if bracket_depth != 0 {
        return Err(CompileError::Semantic(
            "unbalanced brackets in regex".into(),
        ));
    }

    // Check for invalid quantifier usage
    if pattern.starts_with('*')
        || pattern.starts_with('+')
        || pattern.starts_with('?')
        || pattern.starts_with('{')
    {
        return Err(CompileError::Semantic(
            "regex cannot start with quantifier".into(),
        ));
    }

    Ok(())
}

/// Extract named capture group names
fn extract_capture_groups(pattern: &str) -> Vec<String> {
    let mut groups = Vec::new();
    let mut chars = pattern.chars().peekable();
    let mut prev = ' ';

    while let Some(ch) = chars.next() {
        // Skip escaped characters
        if prev == '\\' {
            prev = ch;
            continue;
        }

        // Look for (?P<name> or (?<name>
        if ch == '(' {
            if chars.peek() == Some(&'?') {
                chars.next();
                let next = chars.peek();

                // (?P<name> format
                if next == Some(&'P') {
                    chars.next();
                    if chars.peek() == Some(&'<') {
                        chars.next();
                        let mut name = String::new();
                        while let Some(&c) = chars.peek() {
                            if c == '>' {
                                chars.next();
                                break;
                            }
                            name.push(c);
                            chars.next();
                        }
                        if !name.is_empty() {
                            groups.push(name);
                        }
                    }
                }
                // (?<name> format
                else if next == Some(&'<') {
                    chars.next();
                    let mut name = String::new();
                    while let Some(&c) = chars.peek() {
                        if c == '>' {
                            chars.next();
                            break;
                        }
                        name.push(c);
                        chars.next();
                    }
                    if !name.is_empty() {
                        groups.push(name);
                    }
                }
            }
        }

        prev = ch;
    }

    groups
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_pattern() {
        let result = parse_regex("hello").unwrap();
        if let Value::Dict(map) = result {
            assert_eq!(map.get("pattern"), Some(&Value::Str("hello".to_string())));
        } else {
            panic!("expected dict");
        }
    }

    #[test]
    fn test_flags_extraction() {
        let (pattern, flags) = extract_flags("/test/im");
        assert_eq!(pattern, "test");
        assert!(flags.case_insensitive);
        assert!(flags.multiline);
        assert!(!flags.dotall);
    }

    #[test]
    fn test_capture_groups() {
        let groups = extract_capture_groups("(?P<name>\\w+)@(?P<domain>\\w+\\.\\w+)");
        assert_eq!(groups, vec!["name", "domain"]);
    }

    #[test]
    fn test_capture_groups_short_form() {
        let groups = extract_capture_groups("(?<name>\\w+)@(?<domain>\\w+\\.\\w+)");
        assert_eq!(groups, vec!["name", "domain"]);
    }

    #[test]
    fn test_invalid_quantifier_start() {
        let result = validate_regex("*test");
        assert!(result.is_err());
    }

    #[test]
    fn test_unbalanced_parens() {
        let result = validate_regex("(test");
        assert!(result.is_err());
    }

    #[test]
    fn test_regex_block_evaluate() {
        let handler = RegexBlock;
        let result = handler.evaluate("\\d+").unwrap();
        match result {
            Value::Block { kind, .. } => {
                assert_eq!(kind, "re");
            }
            _ => panic!("expected block value"),
        }
    }
}

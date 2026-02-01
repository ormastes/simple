//! SQL block handler for parameterized database queries.
//!
//! Supports:
//! - Parameterized queries: SELECT * FROM users WHERE id = $1
//! - Named parameters: SELECT * FROM users WHERE name = :name
//! - Basic SQL parsing for validation
//! - Query type detection (SELECT, INSERT, UPDATE, DELETE, etc.)

use super::{BlockHandler, BlockResult};
use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use std::collections::HashMap;

/// SQL block handler
pub struct SqlBlock;

impl BlockHandler for SqlBlock {
    fn evaluate(&self, payload: &str) -> BlockResult {
        // Parse the SQL query
        let query = parse_sql_query(payload)?;

        // Return as a Block value with the parsed query
        Ok(Value::Block {
            kind: "sql".to_string(),
            payload: payload.to_string(),
            result: Some(Box::new(query)),
        })
    }

    fn kind(&self) -> &'static str {
        "sql"
    }
}

/// SQL query type
#[derive(Debug, Clone, PartialEq)]
pub enum SqlQueryType {
    Select,
    Insert,
    Update,
    Delete,
    Create,
    Drop,
    Alter,
    Other(String),
}

impl SqlQueryType {
    fn as_str(&self) -> &str {
        match self {
            SqlQueryType::Select => "SELECT",
            SqlQueryType::Insert => "INSERT",
            SqlQueryType::Update => "UPDATE",
            SqlQueryType::Delete => "DELETE",
            SqlQueryType::Create => "CREATE",
            SqlQueryType::Drop => "DROP",
            SqlQueryType::Alter => "ALTER",
            SqlQueryType::Other(s) => s,
        }
    }
}

/// Parse a SQL query and return a Value
fn parse_sql_query(payload: &str) -> Result<Value, CompileError> {
    let payload = payload.trim();

    if payload.is_empty() {
        let ctx = ErrorContext::new()
            .with_code(codes::SQL_BLOCK_SYNTAX_ERROR)
            .with_help("provide a non-empty SQL query");
        return Err(CompileError::semantic_with_context("empty SQL query", ctx));
    }

    // Detect query type
    let query_type = detect_query_type(payload);

    // Extract parameters
    let (positional_params, named_params) = extract_parameters(payload);

    // Basic validation
    validate_sql(payload)?;

    // Build result structure
    let mut result = HashMap::new();
    result.insert("query_type".to_string(), Value::Str(query_type.as_str().to_string()));
    result.insert("raw_query".to_string(), Value::Str(payload.to_string()));
    result.insert(
        "positional_params".to_string(),
        Value::Array(positional_params.into_iter().map(Value::Str).collect()),
    );
    result.insert(
        "named_params".to_string(),
        Value::Array(named_params.into_iter().map(Value::Str).collect()),
    );

    Ok(Value::dict(result))
}

/// Detect the type of SQL query
fn detect_query_type(query: &str) -> SqlQueryType {
    let upper = query.to_uppercase();
    let first_word = upper.split_whitespace().next().unwrap_or("");

    match first_word {
        "SELECT" => SqlQueryType::Select,
        "INSERT" => SqlQueryType::Insert,
        "UPDATE" => SqlQueryType::Update,
        "DELETE" => SqlQueryType::Delete,
        "CREATE" => SqlQueryType::Create,
        "DROP" => SqlQueryType::Drop,
        "ALTER" => SqlQueryType::Alter,
        other => SqlQueryType::Other(other.to_string()),
    }
}

/// Extract positional ($1, $2) and named (:name) parameters
fn extract_parameters(query: &str) -> (Vec<String>, Vec<String>) {
    let mut positional = Vec::new();
    let mut named = Vec::new();

    let mut chars = query.chars().peekable();
    while let Some(ch) = chars.next() {
        // Positional parameter: $1, $2, etc.
        if ch == '$' {
            let mut num = String::new();
            while let Some(&digit) = chars.peek() {
                if digit.is_ascii_digit() {
                    num.push(digit);
                    chars.next();
                } else {
                    break;
                }
            }
            if !num.is_empty() {
                let param = format!("${}", num);
                if !positional.contains(&param) {
                    positional.push(param);
                }
            }
        }
        // Named parameter: :name
        else if ch == ':' {
            // Skip if it's ::type cast
            if chars.peek() == Some(&':') {
                chars.next();
                continue;
            }
            let mut name = String::new();
            while let Some(&c) = chars.peek() {
                if c.is_alphanumeric() || c == '_' {
                    name.push(c);
                    chars.next();
                } else {
                    break;
                }
            }
            if !name.is_empty() {
                let param = format!(":{}", name);
                if !named.contains(&param) {
                    named.push(param);
                }
            }
        }
        // Skip string literals
        else if ch == '\'' {
            while let Some(c) = chars.next() {
                if c == '\'' {
                    // Check for escaped quote
                    if chars.peek() == Some(&'\'') {
                        chars.next();
                    } else {
                        break;
                    }
                }
            }
        }
    }

    // Sort positional parameters numerically
    positional.sort_by(|a, b| {
        let a_num: i32 = a[1..].parse().unwrap_or(0);
        let b_num: i32 = b[1..].parse().unwrap_or(0);
        a_num.cmp(&b_num)
    });

    (positional, named)
}

/// Basic SQL validation
fn validate_sql(query: &str) -> Result<(), CompileError> {
    // Check for balanced parentheses
    let mut paren_depth = 0;
    for ch in query.chars() {
        match ch {
            '(' => paren_depth += 1,
            ')' => {
                paren_depth -= 1;
                if paren_depth < 0 {
                    let ctx = ErrorContext::new()
                        .with_code(codes::SQL_BLOCK_SYNTAX_ERROR)
                        .with_help("check that parentheses are balanced");
                    return Err(CompileError::semantic_with_context(
                        "unbalanced parentheses in SQL query",
                        ctx,
                    ));
                }
            }
            _ => {}
        }
    }
    if paren_depth != 0 {
        let ctx = ErrorContext::new()
            .with_code(codes::SQL_BLOCK_SYNTAX_ERROR)
            .with_help("check that parentheses are balanced");
        return Err(CompileError::semantic_with_context(
            "unbalanced parentheses in SQL query",
            ctx,
        ));
    }

    // Check for unclosed string literals
    let mut in_string = false;
    let mut prev = ' ';
    for ch in query.chars() {
        if ch == '\'' && prev != '\'' {
            in_string = !in_string;
        }
        prev = ch;
    }
    if in_string {
        let ctx = ErrorContext::new()
            .with_code(codes::SQL_BLOCK_SYNTAX_ERROR)
            .with_help("check that all string literals are properly closed");
        return Err(CompileError::semantic_with_context(
            "unclosed string literal in SQL query",
            ctx,
        ));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_detect_select() {
        assert_eq!(detect_query_type("SELECT * FROM users"), SqlQueryType::Select);
    }

    #[test]
    fn test_detect_insert() {
        assert_eq!(
            detect_query_type("INSERT INTO users VALUES (1, 'test')"),
            SqlQueryType::Insert
        );
    }

    #[test]
    fn test_extract_positional_params() {
        let (pos, named) = extract_parameters("SELECT * FROM users WHERE id = $1 AND name = $2");
        assert_eq!(pos, vec!["$1", "$2"]);
        assert!(named.is_empty());
    }

    #[test]
    fn test_extract_named_params() {
        let (pos, named) = extract_parameters("SELECT * FROM users WHERE id = :id AND name = :name");
        assert!(pos.is_empty());
        assert_eq!(named, vec![":id", ":name"]);
    }

    #[test]
    fn test_mixed_params() {
        let (pos, named) = extract_parameters("SELECT * FROM users WHERE id = $1 AND name = :name");
        assert_eq!(pos, vec!["$1"]);
        assert_eq!(named, vec![":name"]);
    }

    #[test]
    fn test_sql_block_evaluate() {
        let handler = SqlBlock;
        let result = handler.evaluate("SELECT * FROM users WHERE id = $1").unwrap();
        match result {
            Value::Block { kind, .. } => {
                assert_eq!(kind, "sql");
            }
            _ => panic!("expected block value"),
        }
    }

    #[test]
    fn test_validation_unbalanced_parens() {
        let result = validate_sql("SELECT * FROM users WHERE (id = 1");
        assert!(result.is_err());
    }
}

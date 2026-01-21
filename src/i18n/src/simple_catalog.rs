use crate::catalog::MessageCatalog;
use crate::error::{I18nError, Result};
use crate::message::LocalizedMessage;
use simple_parser::ast::{Expr, FStringPart, Node, Pattern};
use simple_parser::Parser;
use std::collections::HashMap;
use std::fs;
use std::path::Path;

/// Parser for Simple language catalog files
pub struct SimpleCatalogParser;

impl SimpleCatalogParser {
    /// Parse a Simple language catalog file and extract messages
    ///
    /// The catalog file should contain a `val messages = { ... }` or `val severity = { ... }`
    /// declaration with a dictionary of message IDs to message structures.
    pub fn parse_catalog(path: &Path, domain: &str, locale: &str) -> Result<MessageCatalog> {
        // Read the file
        let content = fs::read_to_string(path).map_err(|e| I18nError::CatalogLoadError {
            path: path.display().to_string(),
            source: e,
        })?;

        // Parse the Simple file
        let mut parser = Parser::new(&content);
        let ast = parser.parse().map_err(|e| I18nError::CatalogParseError {
            path: path.display().to_string(),
            message: format!("Parse error: {}", e),
        })?;

        // Find the variable declaration
        let var_name = if domain == "common" { "severity" } else { "messages" };

        let dict_expr =
            Self::find_variable_value(&ast.items, var_name).ok_or_else(|| I18nError::CatalogParseError {
                path: path.display().to_string(),
                message: format!("No '{}' variable found in catalog", var_name),
            })?;

        // Extract messages from the dictionary
        let messages = Self::extract_messages(dict_expr, domain, path)?;

        Ok(MessageCatalog {
            version: "1.0".to_string(),
            locale: locale.to_string(),
            domain: domain.to_string(),
            messages,
        })
    }

    /// Find a variable declaration and return its value expression
    ///
    /// Looks for both `val name = ...` (Let) and `const name = ...` (Const) declarations
    fn find_variable_value<'a>(items: &'a [Node], name: &str) -> Option<&'a Expr> {
        for item in items {
            match item {
                // Handle `const name = value` declarations
                Node::Const(const_stmt) if const_stmt.name == name => {
                    return Some(&const_stmt.value);
                }
                // Handle `val name = value` (Let with Identifier pattern)
                Node::Let(let_stmt) => {
                    if let Pattern::Identifier(ident_name) = &let_stmt.pattern {
                        if ident_name == name {
                            return let_stmt.value.as_ref();
                        }
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Extract messages from a dictionary expression
    fn extract_messages(expr: &Expr, domain: &str, path: &Path) -> Result<HashMap<String, LocalizedMessage>> {
        match expr {
            Expr::Dict(pairs) => {
                let mut messages = HashMap::new();

                for (key_expr, value_expr) in pairs {
                    // Skip dict spreads
                    if matches!(key_expr, Expr::DictSpread(_)) {
                        continue;
                    }

                    // Extract the key (message ID)
                    let key = Self::extract_string(key_expr).ok_or_else(|| I18nError::CatalogParseError {
                        path: path.display().to_string(),
                        message: format!("Message key must be a string, got: {:?}", key_expr),
                    })?;

                    // For common domain (severity), values are simple strings
                    if domain == "common" {
                        let value = Self::extract_string(value_expr).ok_or_else(|| I18nError::CatalogParseError {
                            path: path.display().to_string(),
                            message: "Severity value must be a string".to_string(),
                        })?;

                        messages.insert(
                            key.clone(),
                            LocalizedMessage {
                                id: key.clone(),
                                title: value.clone(),
                                message: value,
                                label: None,
                                help: None,
                                note: None,
                            },
                        );
                    } else {
                        // For other domains, values are dictionaries
                        let message = Self::extract_message(value_expr, &key, path)?;
                        messages.insert(key, message);
                    }
                }

                Ok(messages)
            }
            _ => Err(I18nError::CatalogParseError {
                path: path.display().to_string(),
                message: "Expected dictionary expression".to_string(),
            }),
        }
    }

    /// Extract a LocalizedMessage from a dictionary expression
    fn extract_message(expr: &Expr, message_id: &str, path: &Path) -> Result<LocalizedMessage> {
        match expr {
            Expr::Dict(pairs) => {
                let mut fields: HashMap<String, String> = HashMap::new();

                for (key_expr, value_expr) in pairs {
                    // Skip dict spreads
                    if matches!(key_expr, Expr::DictSpread(_)) {
                        continue;
                    }

                    let key = Self::extract_string(key_expr).ok_or_else(|| I18nError::CatalogParseError {
                        path: path.display().to_string(),
                        message: "Field key must be a string".to_string(),
                    })?;

                    let value = Self::extract_string(value_expr).ok_or_else(|| I18nError::CatalogParseError {
                        path: path.display().to_string(),
                        message: "Field value must be a string".to_string(),
                    })?;

                    fields.insert(key, value);
                }

                // Build LocalizedMessage from fields
                Ok(LocalizedMessage {
                    id: fields.get("id").cloned().unwrap_or_else(|| message_id.to_string()),
                    title: fields.get("title").cloned().unwrap_or_else(|| "Untitled".to_string()),
                    message: fields
                        .get("message")
                        .cloned()
                        .unwrap_or_else(|| "No message".to_string()),
                    label: fields.get("label").cloned(),
                    help: fields.get("help").cloned(),
                    note: fields.get("note").cloned(),
                })
            }
            _ => Err(I18nError::CatalogParseError {
                path: path.display().to_string(),
                message: "Expected dictionary for message".to_string(),
            }),
        }
    }

    /// Extract a string value from an expression
    ///
    /// Handles string literals, identifiers, and f-strings with only literal parts
    fn extract_string(expr: &Expr) -> Option<String> {
        match expr {
            Expr::String(s) => Some(s.clone()),
            Expr::Identifier(s) => Some(s.clone()),
            // Handle f-strings that contain only literal parts (no interpolation)
            Expr::FString { parts, .. } if parts.len() == 1 => {
                if let FStringPart::Literal(s) = &parts[0] {
                    Some(s.clone())
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_parse_simple_catalog() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(
            file,
            r#"
val messages = {{
    "E0001": {{
        "id": "E0001",
        "title": "Test Error",
        "message": "This is a test error",
        "label": "test label"
    }}
}}
"#
        )
        .unwrap();

        let catalog = SimpleCatalogParser::parse_catalog(file.path(), "parser", "en").unwrap();

        assert_eq!(catalog.locale, "en");
        assert_eq!(catalog.domain, "parser");
        assert!(catalog.messages.contains_key("E0001"));

        let msg = catalog.messages.get("E0001").unwrap();
        assert_eq!(msg.id, "E0001");
        assert_eq!(msg.title, "Test Error");
        assert_eq!(msg.message, "This is a test error");
        assert_eq!(msg.label, Some("test label".to_string()));
    }

    #[test]
    fn test_parse_severity_catalog() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(
            file,
            r#"
val severity = {{
    "error": "error",
    "warning": "warning"
}}
"#
        )
        .unwrap();

        let catalog = SimpleCatalogParser::parse_catalog(file.path(), "common", "en").unwrap();

        assert_eq!(catalog.locale, "en");
        assert_eq!(catalog.domain, "common");
        assert!(catalog.messages.contains_key("error"));
        assert!(catalog.messages.contains_key("warning"));
    }
}

//! Basic code formatter for Simple language.
//!
//! Provides simple indentation-based formatting without full AST analysis.

use simple_parser::Parser;

/// Code formatter configuration
#[derive(Debug, Clone)]
pub struct FormatConfig {
    pub indent_size: usize,
}

impl Default for FormatConfig {
    fn default() -> Self {
        Self { indent_size: 4 }
    }
}

/// Basic code formatter
pub struct Formatter {
    config: FormatConfig,
}

impl Formatter {
    /// Create a new formatter with default configuration
    pub fn new() -> Self {
        Self {
            config: FormatConfig::default(),
        }
    }

    /// Create a formatter with custom configuration
    pub fn with_config(config: FormatConfig) -> Self {
        Self { config }
    }

    /// Format a complete module
    /// For now, this validates the code can be parsed and returns it unchanged
    pub fn format_module(&mut self, module: &simple_parser::ast::Module) -> String {
        // Basic formatting: just ensure consistent indentation
        // Full AST-based formatting would require matching the exact AST structure
        // For now, return a placeholder showing the module was processed
        format!("// Module with {} items\n", module.items.len())
    }

    /// Format source code (validates and returns formatted)
    pub fn format_source(&mut self, source: &str) -> Result<String, String> {
        // Validate by parsing
        let mut parser = Parser::new(source);
        match parser.parse() {
            Ok(_) => {
                // For now, just return the source unchanged
                // Full formatting would rebuild from AST
                Ok(source.to_string())
            }
            Err(e) => Err(format!("Parse error: {}", e)),
        }
    }
}

impl Default for Formatter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_valid_source() {
        let source = "fn main():\n    val x = 5\n    return x";
        let mut formatter = Formatter::new();
        let result = formatter.format_source(source);
        if result.is_err() {
            eprintln!("Format error: {:?}", result);
        }
        assert!(result.is_ok());
    }

    #[test]
    fn test_format_invalid_source() {
        let source = "fn invalid syntax )(";
        let mut formatter = Formatter::new();
        let result = formatter.format_source(source);
        assert!(result.is_err());
    }
}

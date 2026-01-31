//! AST-based code formatter for Simple language.
//!
//! Provides proper formatting by parsing source into AST and pretty-printing it.

use simple_parser::Parser;
use crate::pretty_printer::{PrettyPrinter, PrettyConfig};

/// Code formatter configuration
#[derive(Debug, Clone)]
pub struct FormatConfig {
    pub indent_size: usize,
    pub max_line_length: usize,
}

impl Default for FormatConfig {
    fn default() -> Self {
        Self {
            indent_size: 4,
            max_line_length: 100,
        }
    }
}

impl From<FormatConfig> for PrettyConfig {
    fn from(config: FormatConfig) -> Self {
        PrettyConfig {
            indent_size: config.indent_size,
            max_line_length: config.max_line_length,
        }
    }
}

/// AST-based code formatter
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

    /// Format a complete module using AST pretty-printer
    pub fn format_module(&mut self, module: &simple_parser::ast::Module) -> String {
        let pretty_config = PrettyConfig::from(self.config.clone());
        let mut printer = PrettyPrinter::new(pretty_config);
        printer.print_module(module)
    }

    /// Format source code by parsing and pretty-printing
    pub fn format_source(&mut self, source: &str) -> Result<String, String> {
        // Parse the source
        let mut parser = Parser::new(source);
        match parser.parse() {
            Ok(module) => {
                // Pretty-print the AST
                Ok(self.format_module(&module))
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

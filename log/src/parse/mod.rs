//! Parse and Lex compile-time logging.
//!
//! This module provides structured logging for the lexer and parser phases
//! of compilation. Use these loggers for:
//! - Token stream generation
//! - AST construction
//! - Parse errors and recovery
//! - Syntax analysis
//!
//! # Usage
//!
//! ```ignore
//! use simple_log::parse;
//!
//! // Log lexer events
//! parse::token("Identifier", "foo", 1, 5);
//! parse::lex_error("Invalid escape sequence", 1, 10);
//!
//! // Log parser events
//! parse::ast_node("FunctionDef", "main");
//! parse::parse_error("Expected ':'", 5, 15);
//! ```
//!
//! # Filtering
//!
//! Use `SIMPLE_LOG` env var to filter:
//! - `SIMPLE_LOG=simple_log::parse=debug` - all parse logs
//! - `SIMPLE_LOG=simple_log::parse::lexer=trace` - lexer only
//! - `SIMPLE_LOG=simple_log::parse::parser=debug` - parser only

use tracing::{debug, error, info, trace, warn, span, Level};

/// Log a token being produced by the lexer.
#[inline]
pub fn token(kind: &str, lexeme: &str, line: usize, column: usize) {
    trace!(
        target: "simple_log::parse::lexer",
        kind = kind,
        lexeme = lexeme,
        line = line,
        column = column,
        "token"
    );
}

/// Log a lexer error.
#[inline]
pub fn lex_error(message: &str, line: usize, column: usize) {
    error!(
        target: "simple_log::parse::lexer",
        message = message,
        line = line,
        column = column,
        "lexer error"
    );
}

/// Log a lexer warning.
#[inline]
pub fn lex_warning(message: &str, line: usize, column: usize) {
    warn!(
        target: "simple_log::parse::lexer",
        message = message,
        line = line,
        column = column,
        "lexer warning"
    );
}

/// Log entering a lexer phase (e.g., string parsing, number parsing).
#[inline]
pub fn lex_phase(phase: &str) {
    debug!(
        target: "simple_log::parse::lexer",
        phase = phase,
        "entering lexer phase"
    );
}

/// Log an AST node being constructed.
#[inline]
pub fn ast_node(kind: &str, name: &str) {
    debug!(
        target: "simple_log::parse::parser",
        kind = kind,
        name = name,
        "ast node"
    );
}

/// Log a parser error.
#[inline]
pub fn parse_error(message: &str, line: usize, column: usize) {
    error!(
        target: "simple_log::parse::parser",
        message = message,
        line = line,
        column = column,
        "parse error"
    );
}

/// Log a parser warning.
#[inline]
pub fn parse_warning(message: &str, line: usize, column: usize) {
    warn!(
        target: "simple_log::parse::parser",
        message = message,
        line = line,
        column = column,
        "parse warning"
    );
}

/// Log entering a parser rule.
#[inline]
pub fn parse_rule(rule: &str) {
    trace!(
        target: "simple_log::parse::parser",
        rule = rule,
        "entering parse rule"
    );
}

/// Log parser recovery from an error.
#[inline]
pub fn parse_recovery(rule: &str, skipped_tokens: usize) {
    info!(
        target: "simple_log::parse::parser",
        rule = rule,
        skipped_tokens = skipped_tokens,
        "parser recovery"
    );
}

/// Log module resolution.
#[inline]
pub fn module_resolve(path: &str, resolved: &str) {
    debug!(
        target: "simple_log::parse::module",
        path = path,
        resolved = resolved,
        "module resolved"
    );
}

/// Log import processing.
#[inline]
pub fn import_process(from: &str, item: &str) {
    debug!(
        target: "simple_log::parse::module",
        from = from,
        item = item,
        "import processed"
    );
}

/// Create a span for lexing a file.
#[inline]
pub fn lex_file_span(file: &str) -> tracing::Span {
    span!(Level::INFO, "lex_file", file = file)
}

/// Create a span for parsing a file.
#[inline]
pub fn parse_file_span(file: &str) -> tracing::Span {
    span!(Level::INFO, "parse_file", file = file)
}

/// Create a span for parsing a specific construct.
#[inline]
pub fn parse_construct_span(construct: &str) -> tracing::Span {
    span!(Level::DEBUG, "parse", construct = construct)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_token_logging() {
        // Just verify the functions compile and don't panic
        token("Identifier", "foo", 1, 5);
        lex_error("test error", 1, 10);
        lex_warning("test warning", 2, 1);
        lex_phase("string");
    }

    #[test]
    fn test_parser_logging() {
        ast_node("FunctionDef", "main");
        parse_error("test error", 5, 15);
        parse_warning("test warning", 6, 1);
        parse_rule("expression");
        parse_recovery("statement", 3);
    }

    #[test]
    fn test_module_logging() {
        module_resolve("crate.core.option", "/path/to/option.spl");
        import_process("crate.core", "Option");
    }
}

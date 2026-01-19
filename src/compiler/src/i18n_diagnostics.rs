//! Conversion utilities for compiler errors to i18n diagnostics.
//!
//! This module provides functions to convert `CompileError` instances
//! to localized `simple-diagnostics::Diagnostic` instances with proper
//! i18n message loading.

use crate::error::{codes, CompileError, ErrorContext};
use simple_diagnostics::{
    Diagnostic as I18nDiagnostic, Severity as I18nSeverity, Span as I18nSpan,
    i18n::{ctx1, ctx2, ctx3, ContextBuilder}
};
use simple_i18n::MessageContext;

/// Convert a compiler error to an i18n diagnostic.
///
/// This function examines the error context and error code to determine
/// which localized message to use from the compiler catalog.
pub fn convert_compiler_error(error: &CompileError) -> I18nDiagnostic {
    // Get the context if available
    if let Some(ctx) = error.context() {
        // Convert span
        let span = ctx.span.map(|s| I18nSpan::new(s.start, s.end, s.line, s.column));

        // Determine error code and create i18n diagnostic
        if let Some(code) = &ctx.code {
            let i18n_diag = create_i18n_diagnostic_from_code(code, error.message(), ctx);

            // Add span if available
            let mut diag = if let Some(s) = span {
                i18n_diag.with_span(s)
            } else {
                i18n_diag
            };

            // Add secondary labels
            for (sec_span, label) in &ctx.secondary_spans {
                let sec_i18n_span = I18nSpan::new(sec_span.start, sec_span.end, sec_span.line, sec_span.column);
                diag = diag.with_label(sec_i18n_span, label.clone());
            }

            // Add notes
            for note in &ctx.notes {
                diag = diag.with_note(note.clone());
            }

            // Add help
            for help in &ctx.help {
                diag = diag.with_help(help.clone());
            }

            diag
        } else {
            // No error code, create a plain diagnostic
            create_plain_diagnostic(error, span)
        }
    } else {
        // No context, create a simple diagnostic with just the message
        create_plain_diagnostic(error, None)
    }
}

/// Create an i18n diagnostic from an error code.
fn create_i18n_diagnostic_from_code(code: &str, message: &str, ctx: &ErrorContext) -> I18nDiagnostic {
    match code {
        // Semantic errors (E10xx)
        codes::UNDEFINED_VARIABLE => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1001", &msg_ctx)
        }

        codes::UNDEFINED_FUNCTION => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1002", &msg_ctx)
        }

        codes::TYPE_MISMATCH => {
            let (expected, found) = extract_type_mismatch(message);
            let msg_ctx = ctx2("expected", expected, "found", found);
            I18nDiagnostic::error_i18n("compiler", "E1003", &msg_ctx)
        }

        codes::INVALID_ASSIGNMENT => {
            let target = extract_target_from_message(message);
            let msg_ctx = ctx1("target", target);
            I18nDiagnostic::error_i18n("compiler", "E1004", &msg_ctx)
        }

        codes::INVALID_OPERATION => {
            let (operator, type_name) = extract_operation_info(message);
            let msg_ctx = ctx2("operator", operator, "type", type_name);
            I18nDiagnostic::error_i18n("compiler", "E1005", &msg_ctx)
        }

        codes::INVALID_PATTERN => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E1006", &msg_ctx)
        }

        codes::MISSING_FIELD => {
            let (struct_name, field_name) = extract_field_info(message);
            let msg_ctx = ctx2("struct_name", struct_name, "field_name", field_name);
            I18nDiagnostic::error_i18n("compiler", "E1007", &msg_ctx)
        }

        codes::DUPLICATE_DEFINITION => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1008", &msg_ctx)
        }

        codes::CIRCULAR_DEPENDENCY => {
            let msg_ctx = ctx1("cycle", message);
            I18nDiagnostic::error_i18n("compiler", "E1009", &msg_ctx)
        }

        codes::MODULE_NOT_FOUND => {
            let module = extract_module_name(message);
            let msg_ctx = ctx1("module", module);
            I18nDiagnostic::error_i18n("compiler", "E1010", &msg_ctx)
        }

        // Control flow errors (E11xx)
        codes::BREAK_OUTSIDE_LOOP => {
            I18nDiagnostic::error_i18n("compiler", "E1101", &MessageContext::new())
        }

        codes::CONTINUE_OUTSIDE_LOOP => {
            I18nDiagnostic::error_i18n("compiler", "E1102", &MessageContext::new())
        }

        codes::RETURN_OUTSIDE_FUNCTION => {
            I18nDiagnostic::error_i18n("compiler", "E1103", &MessageContext::new())
        }

        // Macro errors (E14xx)
        codes::MACRO_UNDEFINED => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1401", &msg_ctx)
        }

        codes::MACRO_USED_BEFORE_DEFINITION => {
            let name = extract_name_from_message(message);
            let msg_ctx = ctx1("name", name);
            I18nDiagnostic::error_i18n("compiler", "E1402", &msg_ctx)
        }

        // Codegen errors (E20xx)
        codes::UNSUPPORTED_FEATURE => {
            let feature = extract_feature_name(message);
            let msg_ctx = ctx1("feature", feature);
            I18nDiagnostic::error_i18n("compiler", "E2001", &msg_ctx)
        }

        codes::FFI_ERROR => {
            let msg_ctx = ctx1("message", message);
            I18nDiagnostic::error_i18n("compiler", "E2002", &msg_ctx)
        }

        // Runtime errors (E30xx)
        codes::DIVISION_BY_ZERO => {
            I18nDiagnostic::error_i18n("compiler", "E3001", &MessageContext::new())
        }

        codes::INDEX_OUT_OF_BOUNDS => {
            let (index, length) = extract_index_bounds(message);
            let msg_ctx = ctx2("index", index, "length", length);
            I18nDiagnostic::error_i18n("compiler", "E3002", &msg_ctx)
        }

        codes::STACK_OVERFLOW => {
            I18nDiagnostic::error_i18n("compiler", "E3003", &MessageContext::new())
        }

        codes::ASSERTION_FAILED => {
            let condition = extract_condition(message);
            let note_msg = ctx.notes.first().map(|s| s.as_str()).unwrap_or("");
            let msg_ctx = ctx2("condition", condition, "message", note_msg);
            I18nDiagnostic::error_i18n("compiler", "E3004", &msg_ctx)
        }

        codes::TIMEOUT => {
            let duration = extract_duration(message);
            let msg_ctx = ctx1("duration", duration);
            I18nDiagnostic::error_i18n("compiler", "E3005", &msg_ctx)
        }

        // Unknown error code - fall back to plain diagnostic
        _ => {
            create_plain_diagnostic_with_code(message, code, None)
        }
    }
}

/// Create a plain diagnostic without i18n (fallback).
fn create_plain_diagnostic(error: &CompileError, span: Option<I18nSpan>) -> I18nDiagnostic {
    let severity = match error {
        CompileError::Lint(_) | CompileError::LintWithContext { .. } => I18nSeverity::Warning,
        _ => I18nSeverity::Error,
    };

    let mut diag = I18nDiagnostic::new(severity, error.message().to_string());

    if let Some(s) = span {
        diag = diag.with_span(s);
    }

    diag
}

/// Create a plain diagnostic with an error code.
fn create_plain_diagnostic_with_code(message: &str, code: &str, span: Option<I18nSpan>) -> I18nDiagnostic {
    let mut diag = I18nDiagnostic::error(message.to_string())
        .with_code(code.to_string());

    if let Some(s) = span {
        diag = diag.with_span(s);
    }

    diag
}

// Helper functions to extract context from error messages

fn extract_name_from_message(message: &str) -> &str {
    // Extract name from messages like "undefined variable: foo" or "cannot find variable `foo` in this scope"
    if let Some(pos) = message.find('`') {
        if let Some(end_pos) = message[pos+1..].find('`') {
            return &message[pos+1..pos+1+end_pos];
        }
    }

    if let Some(pos) = message.find(": ") {
        message[pos+2..].trim()
    } else {
        "unknown"
    }
}

fn extract_type_mismatch(message: &str) -> (&str, &str) {
    // Extract from "expected type `Foo`, found `Bar`"
    let expected = if let Some(start) = message.find("expected type `") {
        let start_pos = start + "expected type `".len();
        if let Some(end) = message[start_pos..].find('`') {
            &message[start_pos..start_pos + end]
        } else {
            "unknown"
        }
    } else {
        "unknown"
    };

    let found = if let Some(start) = message.find("found `") {
        let start_pos = start + "found `".len();
        if let Some(end) = message[start_pos..].find('`') {
            &message[start_pos..start_pos + end]
        } else {
            "unknown"
        }
    } else {
        "unknown"
    };

    (expected, found)
}

fn extract_target_from_message(message: &str) -> &str {
    // Extract from "cannot assign to `foo`"
    if let Some(pos) = message.find("to `") {
        let start_pos = pos + 4;
        if let Some(end) = message[start_pos..].find('`') {
            return &message[start_pos..start_pos + end];
        }
    }
    "expression"
}

fn extract_operation_info(message: &str) -> (&str, &str) {
    // Extract from "cannot apply operator `+` to type `String`"
    let operator = if let Some(start) = message.find("operator `") {
        let start_pos = start + 10;
        if let Some(end) = message[start_pos..].find('`') {
            &message[start_pos..start_pos + end]
        } else {
            "unknown"
        }
    } else {
        "unknown"
    };

    let type_name = if let Some(start) = message.find("type `") {
        let start_pos = start + 6;
        if let Some(end) = message[start_pos..].find('`') {
            &message[start_pos..start_pos + end]
        } else {
            "unknown"
        }
    } else {
        "unknown"
    };

    (operator, type_name)
}

fn extract_field_info(message: &str) -> (&str, &str) {
    // Extract from "struct `Foo` does not have a field named `bar`"
    let struct_name = if let Some(start) = message.find("struct `") {
        let start_pos = start + 8;
        if let Some(end) = message[start_pos..].find('`') {
            &message[start_pos..start_pos + end]
        } else {
            "unknown"
        }
    } else {
        "unknown"
    };

    let field_name = if let Some(start) = message.find("field named `") {
        let start_pos = start + 13;
        if let Some(end) = message[start_pos..].find('`') {
            &message[start_pos..start_pos + end]
        } else {
            "unknown"
        }
    } else {
        "unknown"
    };

    (struct_name, field_name)
}

fn extract_module_name(message: &str) -> &str {
    // Extract from "module `foo` not found"
    if let Some(start) = message.find("module `") {
        let start_pos = start + 8;
        if let Some(end) = message[start_pos..].find('`') {
            return &message[start_pos..start_pos + end];
        }
    }
    "unknown"
}

fn extract_feature_name(message: &str) -> &str {
    // Extract from "feature `foo` is not supported in this context"
    if let Some(start) = message.find("feature `") {
        let start_pos = start + 9;
        if let Some(end) = message[start_pos..].find('`') {
            return &message[start_pos..start_pos + end];
        }
    }
    "unknown"
}

fn extract_index_bounds(message: &str) -> (&str, &str) {
    // Extract from "index 5 out of bounds for array of length 3"
    let index = if let Some(start) = message.find("index ") {
        let start_pos = start + 6;
        if let Some(end) = message[start_pos..].find(' ') {
            &message[start_pos..start_pos + end]
        } else {
            "0"
        }
    } else {
        "0"
    };

    let length = if let Some(start) = message.find("length ") {
        let start_pos = start + 7;
        message[start_pos..].split_whitespace().next().unwrap_or("0")
    } else {
        "0"
    };

    (index, length)
}

fn extract_condition(message: &str) -> &str {
    // Extract from "assertion failed: condition"
    if let Some(pos) = message.find("failed: ") {
        &message[pos + 8..]
    } else {
        "assertion"
    }
}

fn extract_duration(message: &str) -> &str {
    // Extract from "operation timed out after 5s"
    if let Some(pos) = message.find("after ") {
        &message[pos + 6..]
    } else {
        "timeout"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::Span;

    #[test]
    fn test_convert_undefined_variable() {
        let ctx = ErrorContext::new()
            .with_span(Span::new(10, 11, 2, 5))
            .with_code(codes::UNDEFINED_VARIABLE);

        let err = CompileError::semantic_with_context("cannot find variable `x` in this scope", ctx);
        let diag = convert_compiler_error(&err);

        assert_eq!(diag.code.as_ref().unwrap(), "E1001");
    }

    #[test]
    fn test_convert_type_mismatch() {
        let ctx = ErrorContext::new()
            .with_span(Span::new(10, 15, 2, 5))
            .with_code(codes::TYPE_MISMATCH);

        let err = CompileError::semantic_with_context("expected type `Int`, found `String`", ctx);
        let diag = convert_compiler_error(&err);

        assert_eq!(diag.code.as_ref().unwrap(), "E1003");
    }

    #[test]
    fn test_extract_name_from_message() {
        assert_eq!(extract_name_from_message("cannot find variable `foo` in this scope"), "foo");
        assert_eq!(extract_name_from_message("undefined variable: bar"), "bar");
    }

    #[test]
    fn test_extract_type_mismatch() {
        let (expected, found) = extract_type_mismatch("expected type `Int`, found `String`");
        assert_eq!(expected, "Int");
        assert_eq!(found, "String");
    }

    #[test]
    fn test_extract_index_bounds() {
        let (index, length) = extract_index_bounds("index 5 out of bounds for array of length 3");
        assert_eq!(index, "5");
        assert_eq!(length, "3");
    }
}

//! Integration test for i18n diagnostics
//!
//! This test demonstrates the end-to-end flow of the diagnostics system:
//! 1. Parser creates a minimal diagnostic
//! 2. Driver converts it to an i18n diagnostic
//! 3. Formatter outputs localized text

use simple_common::{Diagnostic as ParserDiagnostic, Label, Severity, Span};
use simple_diagnostics::{Diagnostic as I18nDiagnostic, TextFormatter, i18n::ctx2};
use simple_driver::convert_parser_diagnostic;

#[test]
fn test_parser_error_conversion() {
    // Simulate a parser error (E0002: Unexpected Token)
    let parser_diag = ParserDiagnostic {
        severity: Severity::Error,
        code: Some("E0002".to_string()),
        message: "unexpected token: expected identifier, found number".to_string(),
        labels: vec![Label::primary(Span::new(10, 15, 2, 5), "unexpected token")],
        notes: vec![],
        help: vec![],
        file: Some("test.spl".to_string()),
    };

    // Convert to i18n diagnostic
    let i18n_diag = convert_parser_diagnostic(parser_diag);

    // Verify conversion
    assert_eq!(i18n_diag.code, Some("E0002".to_string()));
    assert!(i18n_diag.span.is_some());

    // Format for terminal output (without color for test stability)
    let source = "fn main() {\n    let x = 42abc\n}\n";
    let formatter = TextFormatter::without_color();
    let output = formatter.format(&i18n_diag, source);

    // Verify output contains expected elements
    assert!(output.contains("error"));
    assert!(output.contains("E0002"));
    assert!(output.contains("2:5")); // Line:column
}

#[test]
fn test_manual_i18n_diagnostic() {
    // Directly create an i18n diagnostic (what the driver would do)
    let ctx = ctx2("expected", "identifier", "found", "number");
    let diag = I18nDiagnostic::error_i18n("parser", "E0002", &ctx)
        .with_span(simple_diagnostics::Span::new(10, 15, 2, 5));

    // Verify the diagnostic has the expected properties
    assert_eq!(diag.code, Some("E0002".to_string()));
    assert!(diag.span.is_some());

    // The message should be localized (will use English since we're in test environment)
    assert!(!diag.message.is_empty());
}

#[test]
fn test_multiple_formatters() {
    let ctx = ctx2("expected", "identifier", "found", "number");
    let diag = I18nDiagnostic::error_i18n("parser", "E0002", &ctx)
        .with_span(simple_diagnostics::Span::new(10, 15, 2, 5));

    let source = "fn main() {\n    let x = 42abc\n}\n";

    // Test text formatter
    let text_formatter = TextFormatter::without_color();
    let text_output = text_formatter.format(&diag, source);
    assert!(text_output.contains("error"));

    // Test JSON formatter
    use simple_diagnostics::JsonFormatter;
    let json_formatter = JsonFormatter::new();
    let json_output = json_formatter.format(&diag);
    let json: serde_json::Value = serde_json::from_str(&json_output).unwrap();
    assert_eq!(json["severity"], "error");
    assert_eq!(json["code"], "E0002");

    // Test Simple formatter
    use simple_diagnostics::SimpleFormatter;
    let simple_formatter = SimpleFormatter::new();
    let simple_output = simple_formatter.format(&diag);
    assert!(simple_output.contains("Diagnostic("));
    assert!(simple_output.contains("Severity.Error"));
}

#[test]
fn test_korean_locale_fallback() {
    // Set Korean locale
    std::env::set_var("SIMPLE_LANG", "ko");

    let ctx = ctx2("expected", "식별자", "found", "숫자");
    let diag = I18nDiagnostic::error_i18n("parser", "E0002", &ctx);

    // Even if catalog isn't loaded, it should fall back gracefully
    assert_eq!(diag.code, Some("E0002".to_string()));
    assert!(!diag.message.is_empty());

    // Cleanup
    std::env::remove_var("SIMPLE_LANG");
}

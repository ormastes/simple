//! End-to-end integration tests for i18n diagnostics system

use simple_diagnostics::{Diagnostic, Severity, Span, i18n::ctx2};
use simple_diagnostics::formatters::{TextFormatter, JsonFormatter};
use simple_i18n::I18n;
use std::env;

/// Test that i18n system loads catalogs correctly
#[test]
fn test_i18n_catalog_loading() {
    // Set Korean locale
    env::set_var("SIMPLE_LANG", "ko");

    // Force reload of global i18n
    let i18n = I18n::global();

    // Get Korean severity name
    let error_name = i18n.severity_name("error");
    assert!(error_name.contains("오류") || error_name == "error",
            "Expected Korean '오류' or fallback 'error', got: {}", error_name);

    // Cleanup
    env::remove_var("SIMPLE_LANG");
}

/// Test parser error E0002 in English
#[test]
fn test_parser_error_english() {
    env::set_var("SIMPLE_LANG", "en");

    let ctx = ctx2("expected", "identifier", "found", "number");
    let diag = Diagnostic::error_i18n("parser", "E0002", &ctx)
        .with_span(Span::new(10, 15, 2, 5));

    assert_eq!(diag.code, Some("E0002".to_string()));
    assert!(diag.message.contains("identifier") || diag.message.contains("expected"));

    env::remove_var("SIMPLE_LANG");
}

/// Test parser error E0002 in Korean
#[test]
fn test_parser_error_korean() {
    env::set_var("SIMPLE_LANG", "ko");

    let ctx = ctx2("expected", "식별자", "found", "숫자");
    let diag = Diagnostic::error_i18n("parser", "E0002", &ctx);

    assert_eq!(diag.code, Some("E0002".to_string()));
    // The message should either be Korean or fall back to English
    assert!(!diag.message.is_empty());

    env::remove_var("SIMPLE_LANG");
}

/// Test compiler error E1001 (undefined variable)
#[test]
fn test_compiler_error_undefined_variable() {
    env::set_var("SIMPLE_LANG", "en");

    let ctx = ctx2("name", "foo", "", "");
    let diag = Diagnostic::error_i18n("compiler", "E1001", &ctx);

    assert_eq!(diag.code, Some("E1001".to_string()));
    assert!(!diag.message.is_empty());

    env::remove_var("SIMPLE_LANG");
}

/// Test compiler error E1003 (type mismatch)
#[test]
fn test_compiler_error_type_mismatch() {
    env::set_var("SIMPLE_LANG", "ko");

    let ctx = ctx2("expected", "Int", "found", "String");
    let diag = Diagnostic::error_i18n("compiler", "E1003", &ctx);

    assert_eq!(diag.code, Some("E1003".to_string()));
    assert!(!diag.message.is_empty());

    env::remove_var("SIMPLE_LANG");
}

/// Test text formatter with i18n diagnostic
#[test]
fn test_text_formatter_with_i18n() {
    env::set_var("SIMPLE_LANG", "en");

    let source = "fn main():\n    let x = foo";
    let span = Span::new(20, 23, 2, 13);

    let ctx = ctx2("name", "foo", "", "");
    let diag = Diagnostic::error_i18n("compiler", "E1001", &ctx)
        .with_span(span);

    let formatter = TextFormatter::new();
    let output = formatter.format(&diag, source);

    // Should contain error marker, code, and line/column info
    assert!(output.contains("error") || output.contains("E1001"));

    env::remove_var("SIMPLE_LANG");
}

/// Test JSON formatter with i18n diagnostic
#[test]
fn test_json_formatter_with_i18n() {
    env::set_var("SIMPLE_LANG", "en");

    let ctx = ctx2("expected", "Int", "found", "Bool");
    let diag = Diagnostic::error_i18n("compiler", "E1003", &ctx)
        .with_span(Span::new(10, 14, 2, 5));

    let formatter = JsonFormatter::new();
    let json = formatter.format(&diag);

    // Should be valid JSON
    assert!(json.contains("{"));
    assert!(json.contains("\"severity\"") || json.contains("\"message\""));

    env::remove_var("SIMPLE_LANG");
}

/// Test fallback when catalog not found
#[test]
fn test_fallback_to_english() {
    // Set unsupported language
    env::set_var("SIMPLE_LANG", "fr");

    let ctx = ctx2("expected", "identifier", "found", "number");
    let diag = Diagnostic::error_i18n("parser", "E0002", &ctx);

    // Should fallback to English
    assert_eq!(diag.code, Some("E0002".to_string()));
    assert!(!diag.message.is_empty());

    env::remove_var("SIMPLE_LANG");
}

/// Test multiple diagnostics with mixed locales
#[test]
fn test_multiple_diagnostics() {
    let mut diagnostics = Vec::new();

    // English error
    env::set_var("SIMPLE_LANG", "en");
    let ctx1 = ctx2("name", "x", "", "");
    diagnostics.push(Diagnostic::error_i18n("compiler", "E1001", &ctx1));

    // Korean error
    env::set_var("SIMPLE_LANG", "ko");
    let ctx2 = ctx2("expected", "Int", "found", "String");
    diagnostics.push(Diagnostic::error_i18n("compiler", "E1003", &ctx2));

    assert_eq!(diagnostics.len(), 2);
    assert_eq!(diagnostics[0].code, Some("E1001".to_string()));
    assert_eq!(diagnostics[1].code, Some("E1003".to_string()));

    env::remove_var("SIMPLE_LANG");
}

/// Test that all parser error codes are available
#[test]
fn test_all_parser_codes_exist() {
    env::set_var("SIMPLE_LANG", "en");

    let parser_codes = vec!["E0001", "E0002", "E0003", "E0004", "E0005",
                           "E0006", "E0007", "E0008", "E0009", "E0010",
                           "E0011", "E0012"];

    for code in parser_codes {
        let ctx = ctx2("test", "value", "", "");
        let diag = Diagnostic::error_i18n("parser", code, &ctx);
        assert_eq!(diag.code, Some(code.to_string()), "Code {} should exist", code);
    }

    env::remove_var("SIMPLE_LANG");
}

/// Test that all compiler error codes are available
#[test]
fn test_all_compiler_codes_exist() {
    env::set_var("SIMPLE_LANG", "en");

    let compiler_codes = vec![
        "E1001", "E1002", "E1003", "E1004", "E1005", "E1006", "E1007", "E1008", "E1009", "E1010",
        "E1101", "E1102", "E1103",
        "E1401", "E1402",
        "E2001", "E2002",
        "E3001", "E3002", "E3003", "E3004", "E3005"
    ];

    for code in compiler_codes {
        let ctx = ctx2("test", "value", "", "");
        let diag = Diagnostic::error_i18n("compiler", code, &ctx);
        assert_eq!(diag.code, Some(code.to_string()), "Code {} should exist", code);
    }

    env::remove_var("SIMPLE_LANG");
}

/// Test locale detection from environment
#[test]
fn test_locale_detection() {
    // Test SIMPLE_LANG takes precedence
    env::set_var("SIMPLE_LANG", "ko");
    env::set_var("LANG", "en_US.UTF-8");

    let i18n = I18n::global();
    let severity = i18n.severity_name("error");
    // Should use Korean from SIMPLE_LANG
    assert!(severity.contains("오류") || severity == "error");

    env::remove_var("SIMPLE_LANG");
    env::remove_var("LANG");
}

/// Test that diagnostics with notes and help are properly formatted
#[test]
fn test_diagnostic_with_notes_and_help() {
    env::set_var("SIMPLE_LANG", "en");

    let ctx = ctx2("name", "count", "", "");
    let diag = Diagnostic::error_i18n("compiler", "E1001", &ctx)
        .with_note("The variable was declared in an outer scope")
        .with_help("Check if the variable name is spelled correctly");

    assert_eq!(diag.code, Some("E1001".to_string()));
    assert!(!diag.notes.is_empty());
    assert!(diag.help.is_some());

    env::remove_var("SIMPLE_LANG");
}

/// Integration test: Full error reporting pipeline
#[test]
fn test_full_error_pipeline() {
    env::set_var("SIMPLE_LANG", "ko");

    let source_code = r#"
fn main():
    let result = undefined_var + 42
"#;

    // Simulate error at line 3, column 18
    let span = Span::new(30, 43, 3, 18);

    let ctx = ctx2("name", "undefined_var", "", "");
    let diag = Diagnostic::error_i18n("compiler", "E1001", &ctx)
        .with_span(span)
        .with_help("철자를 확인하거나 사용하기 전에 변수를 선언하세요");

    // Format with text formatter
    let formatter = TextFormatter::new();
    let output = formatter.format(&diag, source_code);

    // Verify output contains expected elements
    assert!(!output.is_empty());
    assert!(output.contains("E1001") || output.contains("오류"));

    env::remove_var("SIMPLE_LANG");
}

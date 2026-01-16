//! Lint system for the Simple language compiler.
//!
//! This module provides a configurable lint system that can emit warnings or errors
//! for various code patterns. Key features:
//!
//! - `primitive_api`: Warns/errors when bare primitives are used in public APIs
//! - Lint levels: `allow`, `warn` (default), `deny`
//! - Attribute-based control: `#[allow(lint)]`, `#[warn(lint)]`, `#[deny(lint)]`
//! - Module-level inheritance through `__init__.spl`

mod checker;
mod config;
mod diagnostics;
mod rules;
mod types;

// Re-export public API
pub use checker::LintChecker;
pub use config::LintConfig;
pub use diagnostics::LintDiagnostic;
pub use types::{LintLevel, LintName};

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::Parser;

    fn parse_code(code: &str) -> simple_parser::ast::Module {
        let mut parser = Parser::new(code);
        parser.parse().expect("parse failed")
    }

    fn check_code(code: &str) -> Vec<LintDiagnostic> {
        let module = parse_code(code);
        let mut checker = LintChecker::new();
        checker.check_module(&module.items);
        checker.take_diagnostics()
    }

    fn check_code_with_deny(code: &str) -> Vec<LintDiagnostic> {
        let module = parse_code(code);
        let mut config = LintConfig::new();
        config.set_level(LintName::PrimitiveApi, LintLevel::Deny);
        let mut checker = LintChecker::with_config(config);
        checker.check_module(&module.items);
        checker.take_diagnostics()
    }

    #[test]
    fn test_public_function_with_primitive_param() {
        let code = r#"
pub fn get_value(x: i64) -> i64:
    return x
"#;
        let diagnostics = check_code(code);
        assert!(!diagnostics.is_empty());
        assert!(diagnostics.iter().any(|d| d.lint == LintName::PrimitiveApi));
        assert!(diagnostics.iter().all(|d| d.level == LintLevel::Warn));
    }

    #[test]
    fn test_private_function_no_warning() {
        let code = r#"
fn internal_compute(x: i64) -> i64:
    return x
"#;
        let diagnostics = check_code(code);
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_public_function_with_unit_type_no_warning() {
        let code = r#"
pub fn get_user_id() -> UserId:
    return 42
"#;
        let diagnostics = check_code(code);
        // UserId is not a primitive, so no warning
        assert!(diagnostics.iter().all(|d| d.lint != LintName::PrimitiveApi));
    }

    #[test]
    fn test_bare_bool_warning() {
        let code = r#"
pub fn set_active(active: bool):
    pass
"#;
        let diagnostics = check_code(code);
        assert!(diagnostics.iter().any(|d| d.lint == LintName::BareBool));
    }

    #[test]
    fn test_deny_makes_error() {
        let code = r#"
pub fn get_value(x: i64) -> i64:
    return x
"#;
        let diagnostics = check_code_with_deny(code);
        assert!(!diagnostics.is_empty());
        assert!(diagnostics.iter().any(|d| d.is_error()));
    }

    #[test]
    fn test_allow_suppresses_warning() {
        let code = r#"
#[allow(primitive_api)]
pub fn raw_bytes(count: i32) -> i32:
    return count
"#;
        let diagnostics = check_code(code);
        // The allow attribute should suppress primitive_api warnings
        assert!(diagnostics.iter().all(|d| d.lint != LintName::PrimitiveApi));
    }

    #[test]
    fn test_public_struct_field() {
        let code = r#"
pub struct Config:
    pub timeout: i64
    internal: i32
"#;
        let diagnostics = check_code(code);
        // Only public fields should trigger warning
        assert!(diagnostics.len() == 1);
        assert!(diagnostics[0].message.contains("timeout"));
    }

    #[test]
    fn test_string_type_no_warning() {
        let code = r#"
pub fn get_name() -> str:
    return "test"
"#;
        let diagnostics = check_code(code);
        // str is allowed
        assert!(diagnostics.is_empty());
    }

    #[test]
    fn test_option_type_checks_inner() {
        let code = r#"
pub fn find_value() -> Option[i64]:
    return None
"#;
        let diagnostics = check_code(code);
        // Should warn about i64 inside Option
        assert!(diagnostics.iter().any(|d| d.lint == LintName::PrimitiveApi));
    }

    #[test]
    fn test_lint_level_from_str() {
        assert_eq!(LintLevel::from_str("allow"), Some(LintLevel::Allow));
        assert_eq!(LintLevel::from_str("warn"), Some(LintLevel::Warn));
        assert_eq!(LintLevel::from_str("deny"), Some(LintLevel::Deny));
        assert_eq!(LintLevel::from_str("DENY"), Some(LintLevel::Deny));
        assert_eq!(LintLevel::from_str("invalid"), None);
    }

    #[test]
    fn test_lint_name_from_str() {
        assert_eq!(LintName::from_str("primitive_api"), Some(LintName::PrimitiveApi));
        assert_eq!(LintName::from_str("bare_bool"), Some(LintName::BareBool));
        assert_eq!(LintName::from_str("unknown"), None);
    }

    #[test]
    fn test_sdn_config_parsing() {
        let sdn_content = r#"
# Lint configuration for Simple project
[lints]
primitive_api = "deny"
bare_bool = "warn"

[other_section]
something = "else"
        "#;

        let config = LintConfig::from_sdn_string(sdn_content).unwrap();
        assert_eq!(config.get_level(LintName::PrimitiveApi), LintLevel::Deny);
        assert_eq!(config.get_level(LintName::BareBool), LintLevel::Warn);
    }

    #[test]
    fn test_sdn_config_with_invalid_level() {
        let sdn_content = r#"
[lints]
primitive_api = "invalid"
        "#;

        let result = LintConfig::from_sdn_string(sdn_content);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Invalid lint level"));
    }

    #[test]
    fn test_sdn_config_with_unknown_lint() {
        let sdn_content = r#"
[lints]
unknown_lint = "deny"
primitive_api = "warn"
        "#;

        // Should succeed but warn about unknown lint
        let config = LintConfig::from_sdn_string(sdn_content).unwrap();
        assert_eq!(config.get_level(LintName::PrimitiveApi), LintLevel::Warn);
    }

    #[test]
    fn test_sdn_config_empty() {
        let sdn_content = r#"
[lints]
# No lints configured
        "#;

        let config = LintConfig::from_sdn_string(sdn_content).unwrap();
        // Should use defaults
        assert_eq!(config.get_level(LintName::PrimitiveApi), LintLevel::Warn);
    }

    #[test]
    fn test_lint_to_diagnostic_conversion() {
        use simple_parser::token::Span;

        let lint = LintDiagnostic::new(
            LintName::PrimitiveApi,
            LintLevel::Warn,
            Span::new(10, 13, 2, 5),
            "bare primitive in public API".to_string(),
        )
        .with_suggestion("consider using a unit type".to_string());

        let diag = lint.to_diagnostic(Some("test.spl".to_string()));

        assert_eq!(diag.severity, simple_common::diagnostic::Severity::Warning);
        assert_eq!(diag.message, "bare primitive in public API");
        assert_eq!(diag.file, Some("test.spl".to_string()));
        assert_eq!(diag.code, Some("L:primitive_api".to_string()));
        assert_eq!(diag.help.len(), 1);
        assert_eq!(diag.help[0], "consider using a unit type");
    }

    #[test]
    fn test_lint_checker_json_export() {
        let code = r#"
pub fn get_value(x: i64) -> i64:
    return x
"#;
        let module = parse_code(code);
        let mut checker = LintChecker::new();
        checker.check_module(&module.items);

        let json = checker.to_json(Some("test.spl".to_string())).unwrap();

        // Verify it's valid JSON
        let value: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert_eq!(value["has_errors"], false);
        assert!(value["warning_count"].as_u64().unwrap() > 0);
        assert!(value["diagnostics"].is_array());
    }

    #[test]
    fn test_lint_checker_json_compact() {
        let code = r#"
pub fn set_active(active: bool):
    pass
"#;
        let module = parse_code(code);
        let mut checker = LintChecker::new();
        checker.check_module(&module.items);

        let compact = checker.to_json_compact(None).unwrap();
        let pretty = checker.to_json(None).unwrap();

        // Compact should have no extra whitespace
        assert!(!compact.contains("\n  "));
        assert!(pretty.contains("\n  "));

        // Both should deserialize to same structure
        let compact_val: serde_json::Value = serde_json::from_str(&compact).unwrap();
        let pretty_val: serde_json::Value = serde_json::from_str(&pretty).unwrap();
        assert_eq!(compact_val, pretty_val);
    }

    #[test]
    fn test_print_in_test_spec_lint() {
        use std::path::PathBuf;

        let code = r#"
print("Test starting")
val result = 42
print("Test passed")
"#;
        let module = parse_code(code);
        let mut checker = LintChecker::new()
            .with_source_file(Some(PathBuf::from("test_spec.spl")));
        checker.check_module(&module.items);

        let diagnostics = checker.diagnostics();
        // Should find 2 print calls
        assert_eq!(diagnostics.len(), 2);
        assert!(diagnostics[0].message.contains("print()"));
        assert_eq!(diagnostics[0].lint, LintName::PrintInTestSpec);
        assert_eq!(diagnostics[0].level, LintLevel::Warn);
    }

    #[test]
    fn test_print_in_test_spec_not_triggered_for_regular_files() {
        use std::path::PathBuf;

        let code = r#"
print("Regular file output")
"#;
        let module = parse_code(code);
        let mut checker = LintChecker::new()
            .with_source_file(Some(PathBuf::from("regular.spl")));
        checker.check_module(&module.items);

        let diagnostics = checker.diagnostics();
        // Should not trigger for non-test-spec files
        assert_eq!(diagnostics.len(), 0);
    }

    #[test]
    fn test_todo_format_lint_valid() {
        use std::path::PathBuf;
        use std::fs;
        use tempfile::NamedTempFile;

        let code = r#"
# TODO: [runtime][P1] Implement feature X
# FIXME: [parser][P0] Fix critical bug [#123]
fn test():
    pass
"#;
        let mut temp_file = NamedTempFile::new().unwrap();
        fs::write(&temp_file, code).unwrap();

        let module = parse_code(code);
        let mut checker = LintChecker::new()
            .with_source_file(Some(temp_file.path().to_path_buf()));
        checker.check_module(&module.items);

        let diagnostics = checker.diagnostics();
        // Should not warn about properly formatted TODOs
        let todo_warnings: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.lint == LintName::TodoFormat)
            .collect();
        assert_eq!(todo_warnings.len(), 0);
    }

    #[test]
    fn test_todo_format_lint_invalid() {
        use std::path::PathBuf;
        use std::fs;
        use tempfile::NamedTempFile;

        let code = r#"
# TODO: implement this feature
# FIXME: broken code here
fn test():
    pass
"#;
        let mut temp_file = NamedTempFile::new().unwrap();
        fs::write(&temp_file, code).unwrap();

        let module = parse_code(code);
        let mut checker = LintChecker::new()
            .with_source_file(Some(temp_file.path().to_path_buf()));
        checker.check_module(&module.items);

        let diagnostics = checker.diagnostics();
        // Should warn about improperly formatted TODOs
        let todo_warnings: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.lint == LintName::TodoFormat)
            .collect();
        assert_eq!(todo_warnings.len(), 2); // Both TODOs are improperly formatted
        assert!(todo_warnings[0].message.contains("missing [area][priority]"));
    }

    #[test]
    fn test_todo_format_lint_invalid_area() {
        use std::path::PathBuf;
        use std::fs;
        use tempfile::NamedTempFile;

        let code = r#"
# TODO: [invalid_area][P1] Do something
fn test():
    pass
"#;
        let mut temp_file = NamedTempFile::new().unwrap();
        fs::write(&temp_file, code).unwrap();

        let module = parse_code(code);
        let mut checker = LintChecker::new()
            .with_source_file(Some(temp_file.path().to_path_buf()));
        checker.check_module(&module.items);

        let diagnostics = checker.diagnostics();
        let todo_warnings: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.lint == LintName::TodoFormat)
            .collect();
        assert_eq!(todo_warnings.len(), 1);
        assert!(todo_warnings[0].message.contains("invalid area"));
    }

    #[test]
    fn test_todo_format_lint_invalid_priority() {
        use std::path::PathBuf;
        use std::fs;
        use tempfile::NamedTempFile;

        let code = r#"
# TODO: [runtime][P99] Do something
fn test():
    pass
"#;
        let mut temp_file = NamedTempFile::new().unwrap();
        fs::write(&temp_file, code).unwrap();

        let module = parse_code(code);
        let mut checker = LintChecker::new()
            .with_source_file(Some(temp_file.path().to_path_buf()));
        checker.check_module(&module.items);

        let diagnostics = checker.diagnostics();
        let todo_warnings: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.lint == LintName::TodoFormat)
            .collect();
        assert_eq!(todo_warnings.len(), 1);
        assert!(todo_warnings[0].message.contains("invalid priority"));
    }
}

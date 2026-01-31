//! Lint system for the Simple language compiler.
//!
//! This module provides a configurable lint system that can emit warnings or errors
//! for various code patterns. Key features:
//!
//! - `primitive_api`: Warns/errors when bare primitives are used in public APIs
//! - Lint levels: `allow`, `warn` (default), `deny`
//! - Attribute-based control: `#[allow(lint)]`, `#[warn(lint)]`, `#[deny(lint)]`
//! - Module-level inheritance through `__init__.spl`
//!
//! #![skip_todo]

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
        let mut checker = LintChecker::new().with_source_file(Some(PathBuf::from("test_spec.spl")));
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
        let mut checker = LintChecker::new().with_source_file(Some(PathBuf::from("regular.spl")));
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
        let mut checker = LintChecker::new().with_source_file(Some(temp_file.path().to_path_buf()));
        checker.check_module(&module.items);

        let diagnostics = checker.diagnostics();
        // Should not warn about properly formatted TODOs
        let todo_warnings: Vec<_> = diagnostics.iter().filter(|d| d.lint == LintName::TodoFormat).collect();
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
        let mut checker = LintChecker::new().with_source_file(Some(temp_file.path().to_path_buf()));
        checker.check_module(&module.items);

        let diagnostics = checker.diagnostics();
        // Should warn about improperly formatted TODOs
        let todo_warnings: Vec<_> = diagnostics.iter().filter(|d| d.lint == LintName::TodoFormat).collect();
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
        let mut checker = LintChecker::new().with_source_file(Some(temp_file.path().to_path_buf()));
        checker.check_module(&module.items);

        let diagnostics = checker.diagnostics();
        let todo_warnings: Vec<_> = diagnostics.iter().filter(|d| d.lint == LintName::TodoFormat).collect();
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
        let mut checker = LintChecker::new().with_source_file(Some(temp_file.path().to_path_buf()));
        checker.check_module(&module.items);

        let diagnostics = checker.diagnostics();
        let todo_warnings: Vec<_> = diagnostics.iter().filter(|d| d.lint == LintName::TodoFormat).collect();
        assert_eq!(todo_warnings.len(), 1);
        assert!(todo_warnings[0].message.contains("invalid priority"));
    }

    #[test]
    fn test_unnamed_duplicate_typed_args_warns() {
        let code = r#"
fn point(x: i64, y: i64) -> i64:
    x + y

fn test():
    val result = point(3, 4)
"#;
        let diagnostics = check_code(code);
        let dup_warnings: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.lint == LintName::UnnamedDuplicateTypedArgs)
            .collect();
        // Should warn about positional args with same type
        assert!(!dup_warnings.is_empty());
        assert!(dup_warnings[0].message.contains("positional argument"));
    }

    #[test]
    fn test_unnamed_duplicate_typed_args_no_warn_named() {
        let code = r#"
fn point(x: i64, y: i64) -> i64:
    x + y

fn test():
    val result = point(x: 3, y: 4)
"#;
        let diagnostics = check_code(code);
        let dup_warnings: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.lint == LintName::UnnamedDuplicateTypedArgs)
            .collect();
        // Should NOT warn when all same-typed params are named
        assert!(dup_warnings.is_empty());
    }

    #[test]
    fn test_unnamed_duplicate_typed_args_no_warn_different_types() {
        let code = r#"
fn describe(name: text, age: i64) -> text:
    name

fn test():
    val result = describe("Alice", 30)
"#;
        let diagnostics = check_code(code);
        let dup_warnings: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.lint == LintName::UnnamedDuplicateTypedArgs)
            .collect();
        // Should NOT warn when types are different
        assert!(dup_warnings.is_empty());
    }

    #[test]
    fn test_unnamed_duplicate_typed_args_partial_named() {
        let code = r#"
fn point(x: i64, y: i64) -> i64:
    x + y

fn test():
    val result = point(x: 3, 4)
"#;
        let diagnostics = check_code(code);
        let dup_warnings: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.lint == LintName::UnnamedDuplicateTypedArgs)
            .collect();
        // Should warn about the positional arg (y)
        assert!(!dup_warnings.is_empty());
        assert!(dup_warnings[0].message.contains("y"));
    }

    #[test]
    fn test_export_outside_init_regular_file() {
        let code = r#"
pub struct Router:
    path: str

export use Router
"#;
        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(std::path::PathBuf::from("src/http/router.spl")));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        // Should error: export in regular file
        assert!(diagnostics.iter().any(|d| d.lint == LintName::ExportOutsideInit));
        assert!(diagnostics.iter().any(|d| d.is_error()));
    }

    #[test]
    fn test_export_allowed_in_init() {
        let code = r#"
pub mod router

export use router.Router
"#;
        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(std::path::PathBuf::from("src/http/__init__.spl")));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        // Should NOT error: export in __init__.spl is allowed
        assert!(diagnostics.iter().all(|d| d.lint != LintName::ExportOutsideInit));
    }

    #[test]
    fn test_export_glob_outside_init() {
        let code = r#"
pub struct Client:
    url: str

export use Client.*
"#;
        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(std::path::PathBuf::from("src/client.spl")));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        // Should error: export in regular file
        assert!(diagnostics.iter().any(|d| d.lint == LintName::ExportOutsideInit));
    }

    #[test]
    fn test_init_boundary_violation_lint_name() {
        assert_eq!(LintName::from_str("init_boundary_violation"), Some(LintName::InitBoundaryViolation));
        assert_eq!(LintName::InitBoundaryViolation.as_str(), "init_boundary_violation");
        assert_eq!(LintName::InitBoundaryViolation.default_level(), LintLevel::Warn);
    }

    #[test]
    fn test_bypass_with_code_files_lint_name() {
        assert_eq!(LintName::from_str("bypass_with_code_files"), Some(LintName::BypassWithCodeFiles));
        assert_eq!(LintName::BypassWithCodeFiles.as_str(), "bypass_with_code_files");
        assert_eq!(LintName::BypassWithCodeFiles.default_level(), LintLevel::Warn);
    }

    #[test]
    fn test_bypass_validity_not_triggered_for_regular_files() {
        let code = r#"
pub struct Helper:
    name: str
"#;
        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(std::path::PathBuf::from("src/lib/helper.spl")));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        // Should NOT trigger: not an __init__.spl file
        assert!(diagnostics.iter().all(|d| d.lint != LintName::BypassWithCodeFiles));
    }

    #[test]
    fn test_all_lints_includes_new_lints() {
        let all = LintName::all_lints();
        assert!(all.contains(&LintName::InitBoundaryViolation));
        assert!(all.contains(&LintName::BypassWithCodeFiles));
    }

    // =========================================================================
    // Intensive coverage: init boundary violation (filesystem-based)
    // =========================================================================

    #[test]
    fn test_init_boundary_violation_with_filesystem() {
        use std::fs;
        use tempfile::TempDir;

        // Create: project/src/pkg/__init__.spl, project/src/pkg/internal.spl
        let tmp = TempDir::new().unwrap();
        let project = tmp.path();
        let src = project.join("src");
        let pkg = src.join("pkg");
        fs::create_dir_all(&pkg).unwrap();
        fs::write(project.join("simple.toml"), "[package]\nname = \"test\"\n").unwrap();
        fs::write(pkg.join("__init__.spl"), "pub mod internal\nexport use internal.Api\n").unwrap();
        fs::write(pkg.join("internal.spl"), "pub struct Api:\n    name: str\n").unwrap();

        // Code that imports past the boundary: use crate.pkg.internal.Secret
        let code = r#"
use crate.pkg.internal.Secret
"#;
        let caller_file = src.join("main.spl");
        fs::write(&caller_file, code).unwrap();

        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(caller_file));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        // Should detect init boundary violation
        assert!(
            diagnostics.iter().any(|d| d.lint == LintName::InitBoundaryViolation),
            "expected InitBoundaryViolation, got: {:?}",
            diagnostics.iter().map(|d| &d.lint).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_init_boundary_no_violation_when_no_init() {
        use std::fs;
        use tempfile::TempDir;

        // Create: project/src/utils/helper.spl (no __init__.spl)
        let tmp = TempDir::new().unwrap();
        let project = tmp.path();
        let src = project.join("src");
        let utils = src.join("utils");
        fs::create_dir_all(&utils).unwrap();
        fs::write(project.join("simple.toml"), "[package]\nname = \"test\"\n").unwrap();
        fs::write(utils.join("helper.spl"), "pub fn help():\n    pass\n").unwrap();

        // use crate.utils.helper.help — no boundary because no __init__.spl
        let code = r#"
use crate.utils.helper.help
"#;
        let caller = src.join("main.spl");
        fs::write(&caller, code).unwrap();

        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(caller));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        assert!(
            diagnostics.iter().all(|d| d.lint != LintName::InitBoundaryViolation),
            "should not trigger boundary violation without __init__.spl"
        );
    }

    #[test]
    fn test_init_boundary_bypass_directory_transparent() {
        use std::fs;
        use tempfile::TempDir;

        // Create: project/src/lib/__init__.spl with #[bypass]
        //         project/src/lib/http/__init__.spl
        let tmp = TempDir::new().unwrap();
        let project = tmp.path();
        let src = project.join("src");
        let lib = src.join("lib");
        let http = lib.join("http");
        fs::create_dir_all(&http).unwrap();
        fs::write(project.join("simple.toml"), "[package]\nname = \"test\"\n").unwrap();
        fs::write(lib.join("__init__.spl"), "#[bypass]\nmod lib\n").unwrap();
        fs::write(http.join("__init__.spl"), "pub mod client\nexport use client.HttpClient\n").unwrap();
        fs::write(http.join("client.spl"), "pub struct HttpClient:\n    url: str\n").unwrap();

        // use crate.lib.http.client.HttpClient — lib is bypass, so transparent
        // Should NOT trigger because lib/__init__.spl has #[bypass]
        let code = r#"
use crate.lib.http.HttpClient
"#;
        let caller = src.join("main.spl");
        fs::write(&caller, code).unwrap();

        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(caller));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        // lib is bypass, so going through it is fine. http has boundary but
        // HttpClient is at the boundary level (not going deeper).
        assert!(
            diagnostics.iter().all(|d| d.lint != LintName::InitBoundaryViolation),
            "bypass directory should be transparent, got: {:?}",
            diagnostics.iter().map(|d| format!("{:?}: {}", d.lint, d.message)).collect::<Vec<_>>()
        );
    }

    // =========================================================================
    // Intensive coverage: bypass with code files (filesystem-based)
    // =========================================================================

    #[test]
    fn test_bypass_with_code_files_triggers() {
        use std::fs;
        use tempfile::TempDir;

        let tmp = TempDir::new().unwrap();
        let dir = tmp.path().join("lib");
        fs::create_dir_all(&dir).unwrap();
        let init_file = dir.join("__init__.spl");
        fs::write(&init_file, "#[bypass]\nmod lib\n").unwrap();
        fs::write(dir.join("helper.spl"), "pub fn help():\n    pass\n").unwrap();

        let code = "#[bypass]\nmod lib\n";
        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(init_file));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        assert!(
            diagnostics.iter().any(|d| d.lint == LintName::BypassWithCodeFiles),
            "expected BypassWithCodeFiles, got: {:?}",
            diagnostics.iter().map(|d| &d.lint).collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_bypass_without_code_files_ok() {
        use std::fs;
        use tempfile::TempDir;

        let tmp = TempDir::new().unwrap();
        let dir = tmp.path().join("lib");
        let subdir = dir.join("http");
        fs::create_dir_all(&subdir).unwrap();
        let init_file = dir.join("__init__.spl");
        fs::write(&init_file, "#[bypass]\nmod lib\n").unwrap();
        // Only subdirectories, no .spl files

        let code = "#[bypass]\nmod lib\n";
        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(init_file));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        assert!(
            diagnostics.iter().all(|d| d.lint != LintName::BypassWithCodeFiles),
            "should not trigger when no code files in bypass dir"
        );
    }

    #[test]
    fn test_bypass_multiple_code_files_reports_each() {
        use std::fs;
        use tempfile::TempDir;

        let tmp = TempDir::new().unwrap();
        let dir = tmp.path().join("lib");
        fs::create_dir_all(&dir).unwrap();
        let init_file = dir.join("__init__.spl");
        fs::write(&init_file, "#[bypass]\nmod lib\n").unwrap();
        fs::write(dir.join("a.spl"), "pub fn a():\n    pass\n").unwrap();
        fs::write(dir.join("b.spl"), "pub fn b():\n    pass\n").unwrap();
        fs::write(dir.join("c.spl"), "pub fn c():\n    pass\n").unwrap();

        let code = "#[bypass]\nmod lib\n";
        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(init_file));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        let bypass_diags: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.lint == LintName::BypassWithCodeFiles)
            .collect();
        assert!(
            bypass_diags.len() >= 3,
            "expected at least 3 BypassWithCodeFiles diagnostics, got {}",
            bypass_diags.len()
        );
    }

    #[test]
    fn test_bypass_ignores_non_spl_files() {
        use std::fs;
        use tempfile::TempDir;

        let tmp = TempDir::new().unwrap();
        let dir = tmp.path().join("lib");
        fs::create_dir_all(&dir).unwrap();
        let init_file = dir.join("__init__.spl");
        fs::write(&init_file, "#[bypass]\nmod lib\n").unwrap();
        fs::write(dir.join("README.md"), "# Library\n").unwrap();
        fs::write(dir.join("config.sdn"), "[settings]\n").unwrap();

        let code = "#[bypass]\nmod lib\n";
        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(init_file));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        assert!(
            diagnostics.iter().all(|d| d.lint != LintName::BypassWithCodeFiles),
            "non-.spl files should not trigger BypassWithCodeFiles"
        );
    }

    #[test]
    fn test_non_bypass_init_no_code_files_check() {
        use std::fs;
        use tempfile::TempDir;

        let tmp = TempDir::new().unwrap();
        let dir = tmp.path().join("pkg");
        fs::create_dir_all(&dir).unwrap();
        let init_file = dir.join("__init__.spl");
        // Regular __init__.spl without bypass
        fs::write(&init_file, "pub mod router\nexport use router.Router\n").unwrap();
        fs::write(dir.join("router.spl"), "pub struct Router:\n    path: str\n").unwrap();

        let code = "pub mod router\nexport use router.Router\n";
        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(init_file));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        // Should NOT trigger BypassWithCodeFiles for non-bypass __init__.spl
        assert!(
            diagnostics.iter().all(|d| d.lint != LintName::BypassWithCodeFiles),
            "non-bypass __init__.spl should not check for code files"
        );
    }

    // =========================================================================
    // Intensive coverage: export outside init edge cases
    // =========================================================================

    #[test]
    fn test_export_outside_init_multiple_exports() {
        let code = r#"
pub struct A:
    x: i64
pub struct B:
    y: i64

export use A
export use B
"#;
        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(std::path::PathBuf::from("src/types.spl")));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        let export_diags: Vec<_> = diagnostics
            .iter()
            .filter(|d| d.lint == LintName::ExportOutsideInit)
            .collect();
        assert_eq!(export_diags.len(), 2, "should report each export separately");
    }

    #[test]
    fn test_export_in_init_with_multiple_exports_ok() {
        let code = r#"
pub mod router
pub mod handlers

export use router.Router
export use handlers.GetHandler
export use handlers.PostHandler
"#;
        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(std::path::PathBuf::from("src/http/__init__.spl")));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        assert!(
            diagnostics.iter().all(|d| d.lint != LintName::ExportOutsideInit),
            "all exports in __init__.spl should be fine"
        );
    }

    // =========================================================================
    // Intensive coverage: lint explain and config
    // =========================================================================

    #[test]
    fn test_init_boundary_violation_explain() {
        let explain = LintName::InitBoundaryViolation.explain();
        assert!(explain.contains("init_boundary_violation"));
        assert!(explain.contains("__init__.spl"));
        assert!(explain.contains("boundary"));
    }

    #[test]
    fn test_bypass_with_code_files_explain() {
        let explain = LintName::BypassWithCodeFiles.explain();
        assert!(explain.contains("bypass_with_code_files"));
        assert!(explain.contains("#[bypass]"));
        assert!(explain.contains(".spl"));
    }

    #[test]
    fn test_lint_config_new_lints() {
        let mut config = LintConfig::new();

        // Default levels
        assert_eq!(config.get_level(LintName::InitBoundaryViolation), LintLevel::Warn);
        assert_eq!(config.get_level(LintName::BypassWithCodeFiles), LintLevel::Warn);

        // Can be changed
        config.set_level(LintName::InitBoundaryViolation, LintLevel::Deny);
        assert_eq!(config.get_level(LintName::InitBoundaryViolation), LintLevel::Deny);

        config.set_level(LintName::BypassWithCodeFiles, LintLevel::Allow);
        assert_eq!(config.get_level(LintName::BypassWithCodeFiles), LintLevel::Allow);
    }

    #[test]
    fn test_sdn_config_new_lints() {
        let sdn = r#"
[lints]
init_boundary_violation = "deny"
bypass_with_code_files = "allow"
"#;
        let config = LintConfig::from_sdn_string(sdn).unwrap();
        assert_eq!(config.get_level(LintName::InitBoundaryViolation), LintLevel::Deny);
        assert_eq!(config.get_level(LintName::BypassWithCodeFiles), LintLevel::Allow);
    }

    #[test]
    fn test_no_export_no_error() {
        let code = r#"
pub struct Router:
    path: str

pub fn create_router() -> Router:
    Router(path: "/")
"#;
        let module = parse_code(code);
        let mut checker = LintChecker::new().with_source_file(Some(std::path::PathBuf::from("src/http/router.spl")));
        checker.check_module(&module.items);
        let diagnostics = checker.take_diagnostics();

        // Should NOT error: no export statements
        assert!(diagnostics.iter().all(|d| d.lint != LintName::ExportOutsideInit));
    }
}

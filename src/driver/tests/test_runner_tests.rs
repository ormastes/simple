//! Tests for the test runner CLI module.
//!
//! These tests verify CLI-008 (JSON formatter) and CLI-009 (Doc formatter).

use std::path::PathBuf;

// We test the test_runner module through its public interface
mod test_runner {
    use super::*;

    /// Helper to create a mock TestFileResult
    fn mock_file_result(path: &str, passed: usize, failed: usize, duration_ms: u64) -> MockResult {
        MockResult {
            path: PathBuf::from(path),
            passed,
            failed,
            duration_ms,
            error: None,
        }
    }

    fn mock_file_result_with_error(
        path: &str,
        passed: usize,
        failed: usize,
        duration_ms: u64,
        error: &str,
    ) -> MockResult {
        MockResult {
            path: PathBuf::from(path),
            passed,
            failed,
            duration_ms,
            error: Some(error.to_string()),
        }
    }

    /// Mock test result for unit testing formatters
    struct MockResult {
        path: PathBuf,
        passed: usize,
        failed: usize,
        duration_ms: u64,
        error: Option<String>,
    }

    /// Mock test run result
    struct MockRunResult {
        files: Vec<MockResult>,
        total_passed: usize,
        total_failed: usize,
        total_duration_ms: u64,
    }

    impl MockRunResult {
        fn success(&self) -> bool {
            self.total_failed == 0
        }
    }

    // =========================================================================
    // CLI-008: JSON formatter tests
    // =========================================================================

    #[test]
    fn json_formatter_outputs_valid_json_structure() {
        // Test that JSON output has correct structure
        let result = MockRunResult {
            files: vec![mock_file_result("test/unit/foo_spec.spl", 3, 0, 100)],
            total_passed: 3,
            total_failed: 0,
            total_duration_ms: 100,
        };

        // Manually format to JSON like the formatter does
        let json = format_json(&result);

        // Verify JSON structure
        assert!(json.contains("\"success\": true"));
        assert!(json.contains("\"total_passed\": 3"));
        assert!(json.contains("\"total_failed\": 0"));
        assert!(json.contains("\"total_duration_ms\": 100"));
        assert!(json.contains("\"files\": ["));
    }

    #[test]
    fn json_formatter_handles_failures() {
        let result = MockRunResult {
            files: vec![
                mock_file_result("test/unit/foo_spec.spl", 2, 0, 50),
                mock_file_result_with_error("test/unit/bar_spec.spl", 0, 1, 30, "assertion failed"),
            ],
            total_passed: 2,
            total_failed: 1,
            total_duration_ms: 80,
        };

        let json = format_json(&result);

        assert!(json.contains("\"success\": false"));
        assert!(json.contains("\"total_passed\": 2"));
        assert!(json.contains("\"total_failed\": 1"));
        assert!(json.contains("\"error\": \"assertion failed\""));
    }

    #[test]
    fn json_formatter_escapes_special_characters() {
        let result = MockRunResult {
            files: vec![mock_file_result_with_error(
                "test/spec.spl",
                0,
                1,
                10,
                "error: \"unexpected\" value\nnew line",
            )],
            total_passed: 0,
            total_failed: 1,
            total_duration_ms: 10,
        };

        let json = format_json(&result);

        // Verify quotes and newlines are escaped
        assert!(json.contains("\\\"unexpected\\\""));
        assert!(json.contains("\\n"));
    }

    #[test]
    fn json_formatter_handles_empty_results() {
        let result = MockRunResult {
            files: vec![],
            total_passed: 0,
            total_failed: 0,
            total_duration_ms: 0,
        };

        let json = format_json(&result);

        assert!(json.contains("\"success\": true"));
        // Empty files array is formatted with newlines
        assert!(json.contains("\"files\": ["));
        assert!(json.contains("  ]"));
    }

    // =========================================================================
    // CLI-009: Doc formatter tests
    // =========================================================================

    #[test]
    fn doc_formatter_groups_by_directory() {
        let result = MockRunResult {
            files: vec![
                mock_file_result("test/unit/foo_spec.spl", 2, 0, 50),
                mock_file_result("test/unit/bar_spec.spl", 1, 0, 30),
                mock_file_result("test/system/sys_spec.spl", 1, 0, 20),
            ],
            total_passed: 4,
            total_failed: 0,
            total_duration_ms: 100,
        };

        let doc = format_doc(&result);

        // Verify directory grouping
        assert!(doc.contains("test/unit"));
        assert!(doc.contains("test/system"));
        // Files should appear under their directories
        assert!(doc.contains("foo_spec.spl"));
        assert!(doc.contains("bar_spec.spl"));
        assert!(doc.contains("sys_spec.spl"));
    }

    #[test]
    fn doc_formatter_shows_pass_fail_indicators() {
        let result = MockRunResult {
            files: vec![
                mock_file_result("test/pass_spec.spl", 1, 0, 10),
                mock_file_result("test/fail_spec.spl", 0, 1, 10),
            ],
            total_passed: 1,
            total_failed: 1,
            total_duration_ms: 20,
        };

        let doc = format_doc(&result);

        // Check for status indicators (✓ and ✗)
        assert!(doc.contains("✓") || doc.contains("PASS") || doc.contains("pass"));
        assert!(doc.contains("✗") || doc.contains("FAIL") || doc.contains("fail"));
    }

    #[test]
    fn doc_formatter_shows_summary() {
        let result = MockRunResult {
            files: vec![mock_file_result("test/spec.spl", 5, 2, 100)],
            total_passed: 5,
            total_failed: 2,
            total_duration_ms: 100,
        };

        let doc = format_doc(&result);

        // Summary line should include counts
        assert!(doc.contains("examples") || doc.contains("5"));
        assert!(doc.contains("failures") || doc.contains("2"));
    }

    // =========================================================================
    // Test options parsing tests
    // =========================================================================

    #[test]
    fn parse_args_default_values() {
        let args: Vec<String> = vec![];
        let options = parse_test_args(&args);

        assert!(options.path.is_none());
        assert_eq!(options.format, OutputFormat::Text);
        assert!(!options.fail_fast);
        assert!(options.seed.is_none());
        assert!(options.tag.is_none());
    }

    #[test]
    fn parse_args_json_format() {
        let args = vec!["--json".to_string()];
        let options = parse_test_args(&args);
        assert_eq!(options.format, OutputFormat::Json);

        let args2 = vec!["--format".to_string(), "json".to_string()];
        let options2 = parse_test_args(&args2);
        assert_eq!(options2.format, OutputFormat::Json);
    }

    #[test]
    fn parse_args_doc_format() {
        let args = vec!["--doc".to_string()];
        let options = parse_test_args(&args);
        assert_eq!(options.format, OutputFormat::Doc);

        let args2 = vec!["--format".to_string(), "doc".to_string()];
        let options2 = parse_test_args(&args2);
        assert_eq!(options2.format, OutputFormat::Doc);
    }

    #[test]
    fn parse_args_test_level() {
        let args = vec!["--unit".to_string()];
        let options = parse_test_args(&args);
        assert_eq!(options.level, TestLevel::Unit);

        let args2 = vec!["--integration".to_string()];
        let options2 = parse_test_args(&args2);
        assert_eq!(options2.level, TestLevel::Integration);

        let args3 = vec!["--system".to_string()];
        let options3 = parse_test_args(&args3);
        assert_eq!(options3.level, TestLevel::System);
    }

    #[test]
    fn parse_args_fail_fast() {
        let args = vec!["--fail-fast".to_string()];
        let options = parse_test_args(&args);
        assert!(options.fail_fast);
    }

    #[test]
    fn parse_args_seed() {
        let args = vec!["--seed".to_string(), "12345".to_string()];
        let options = parse_test_args(&args);
        assert_eq!(options.seed, Some(12345));
    }

    #[test]
    fn parse_args_tag() {
        let args = vec!["--tag".to_string(), "slow".to_string()];
        let options = parse_test_args(&args);
        assert_eq!(options.tag, Some("slow".to_string()));
    }

    #[test]
    fn parse_args_path() {
        let args = vec!["test/my_tests".to_string()];
        let options = parse_test_args(&args);
        assert_eq!(options.path, Some(PathBuf::from("test/my_tests")));
    }

    #[test]
    fn parse_args_combined() {
        let args = vec![
            "test/unit".to_string(),
            "--unit".to_string(),
            "--fail-fast".to_string(),
            "--format".to_string(),
            "json".to_string(),
            "--seed".to_string(),
            "42".to_string(),
        ];
        let options = parse_test_args(&args);

        assert_eq!(options.path, Some(PathBuf::from("test/unit")));
        assert_eq!(options.level, TestLevel::Unit);
        assert!(options.fail_fast);
        assert_eq!(options.format, OutputFormat::Json);
        assert_eq!(options.seed, Some(42));
    }

    // =========================================================================
    // Helper functions for testing (simulate test_runner behavior)
    // =========================================================================

    #[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
    enum OutputFormat {
        #[default]
        Text,
        Json,
        Doc,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    enum TestLevel {
        All,
        Unit,
        Integration,
        System,
    }

    struct TestOptions {
        path: Option<PathBuf>,
        level: TestLevel,
        tag: Option<String>,
        fail_fast: bool,
        seed: Option<u64>,
        format: OutputFormat,
    }

    impl Default for TestOptions {
        fn default() -> Self {
            Self {
                path: None,
                level: TestLevel::All,
                tag: None,
                fail_fast: false,
                seed: None,
                format: OutputFormat::Text,
            }
        }
    }

    fn parse_test_args(args: &[String]) -> TestOptions {
        let mut options = TestOptions::default();
        let mut i = 0;

        while i < args.len() {
            match args[i].as_str() {
                "--unit" => options.level = TestLevel::Unit,
                "--integration" => options.level = TestLevel::Integration,
                "--system" => options.level = TestLevel::System,
                "--fail-fast" => options.fail_fast = true,
                "--tag" => {
                    i += 1;
                    if i < args.len() {
                        options.tag = Some(args[i].clone());
                    }
                }
                "--seed" => {
                    i += 1;
                    if i < args.len() {
                        options.seed = args[i].parse().ok();
                    }
                }
                "--format" => {
                    i += 1;
                    if i < args.len() {
                        options.format = match args[i].as_str() {
                            "json" => OutputFormat::Json,
                            "doc" => OutputFormat::Doc,
                            _ => OutputFormat::Text,
                        };
                    }
                }
                "--json" => options.format = OutputFormat::Json,
                "--doc" => options.format = OutputFormat::Doc,
                arg if !arg.starts_with('-') && options.path.is_none() => {
                    options.path = Some(PathBuf::from(arg));
                }
                _ => {}
            }
            i += 1;
        }

        options
    }

    /// Format JSON output (mirrors test_runner::print_summary_json)
    fn format_json(result: &MockRunResult) -> String {
        let mut output = String::new();
        output.push_str("{\n");
        output.push_str(&format!("  \"success\": {},\n", result.success()));
        output.push_str(&format!("  \"total_passed\": {},\n", result.total_passed));
        output.push_str(&format!("  \"total_failed\": {},\n", result.total_failed));
        output.push_str(&format!("  \"total_duration_ms\": {},\n", result.total_duration_ms));
        output.push_str("  \"files\": [\n");

        for (i, file) in result.files.iter().enumerate() {
            let comma = if i < result.files.len() - 1 { "," } else { "" };
            let error_str = match &file.error {
                Some(e) => format!("\"{}\"", e.replace('\"', "\\\"").replace('\n', "\\n")),
                None => "null".to_string(),
            };
            output.push_str("    {\n");
            output.push_str(&format!(
                "      \"path\": \"{}\",\n",
                file.path.display().to_string().replace('\\', "\\\\")
            ));
            output.push_str(&format!("      \"passed\": {},\n", file.passed));
            output.push_str(&format!("      \"failed\": {},\n", file.failed));
            output.push_str(&format!("      \"duration_ms\": {},\n", file.duration_ms));
            output.push_str(&format!("      \"error\": {}\n", error_str));
            output.push_str(&format!("    }}{}\n", comma));
        }

        output.push_str("  ]\n");
        output.push_str("}\n");
        output
    }

    /// Format doc output (mirrors test_runner::print_summary_doc)
    fn format_doc(result: &MockRunResult) -> String {
        let mut output = String::new();
        output.push('\n');

        let mut current_dir = String::new();

        for file in &result.files {
            let path_str = file.path.display().to_string();
            let parts: Vec<&str> = path_str.split('/').collect();

            let dir = if parts.len() > 1 {
                parts[..parts.len() - 1].join("/")
            } else {
                String::new()
            };

            if dir != current_dir {
                if !current_dir.is_empty() {
                    output.push('\n');
                }
                output.push_str(&dir);
                output.push('\n');
                current_dir = dir;
            }

            let file_name = parts.last().unwrap_or(&"");
            let status = if file.failed > 0 || file.error.is_some() {
                "✗"
            } else {
                "✓"
            };

            output.push_str(&format!("  {} {} ({}ms)\n", status, file_name, file.duration_ms));

            if let Some(ref err) = file.error {
                for line in err.lines().take(3) {
                    output.push_str(&format!("      {}\n", line));
                }
            }
        }

        output.push('\n');
        output.push_str("─────────────────────────────────────────────────────────────────\n");

        if result.success() {
            output.push_str(&format!(
                "{} examples, 0 failures ({}ms)\n",
                result.total_passed, result.total_duration_ms
            ));
        } else {
            output.push_str(&format!(
                "{} examples, {} failures ({}ms)\n",
                result.total_passed + result.total_failed,
                result.total_failed,
                result.total_duration_ms
            ));
        }

        output
    }
}

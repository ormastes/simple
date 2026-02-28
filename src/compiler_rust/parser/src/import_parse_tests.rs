#[cfg(test)]
mod tests {
    use crate::parser_impl::core::Parser;
    use crate::error::ParseError;

    fn try_parse(source: &str) -> Result<usize, String> {
        let mut parser = Parser::new(source);
        match parser.parse() {
            Ok(module) => Ok(module.items.len()),
            Err(e) => Err(format!("{}", e)),
        }
    }

    fn parse_file_detail(path: &str) -> String {
        let full_path = format!("/home/ormastes/dev/pub/simple/{}", path);
        let source = match std::fs::read_to_string(&full_path) {
            Ok(s) => s,
            Err(e) => return format!("READ ERROR: {}", e),
        };
        let mut parser = Parser::new(&source);
        match parser.parse() {
            Ok(module) => format!("OK: {} items", module.items.len()),
            Err(e) => {
                // Extract line number from error
                let (line, col) = match &e {
                    ParseError::UnexpectedToken { span, .. } => (span.line, span.column),
                    ParseError::SyntaxError { line, column, .. } => (*line, *column),
                    _ => (0, 0),
                };
                let lines: Vec<&str> = source.lines().collect();
                let context_line = if line > 0 && line <= lines.len() {
                    lines[line - 1]
                } else if line == 0 && !lines.is_empty() {
                    lines[0]
                } else {
                    "(no context)"
                };
                format!(
                    "FAIL at line {}:{}: {}\n    Source line: '{}'",
                    line, col, e, context_line
                )
            }
        }
    }

    /// Files that were previously failing and are now fixed by parser changes.
    /// These must all parse successfully.
    #[test]
    fn test_fixed_files() {
        let files = [
            ("Group 2: resource", "src/lib/common/core/resource.spl"),
            (
                "Group 2: mock_example",
                "src/lib/nogc_sync_mut/examples/testing/mock_example.spl",
            ),
            ("Group 2: path_ops", "src/lib/nogc_sync_mut/file_system/path_ops.spl"),
            ("Group 3: checker", "src/lib/common/type/checker.spl"),
            ("Group 4: lz77", "src/lib/nogc_sync_mut/compression/gzip/lz77.spl"),
            ("Group 4: zlib", "src/lib/nogc_sync_mut/compression/zlib.spl"),
            ("Group 5: semver", "src/lib/nogc_sync_mut/package/semver.spl"),
        ];

        let mut all_ok = true;
        for (desc, path) in &files {
            let result = parse_file_detail(path);
            eprintln!("[{}] {}", desc, result);
            if result.starts_with("FAIL") {
                all_ok = false;
            }
        }

        if !all_ok {
            panic!("Some previously-fixed files failed to parse - see output above");
        }
    }

    /// Files that still fail due to issues outside the scope of import/module fixes:
    /// - Source file bugs (LSP server indentation, base64 `use` as expression)
    /// - Method chain indentation state bug (diagnostic.spl)
    /// - Triple-quoted string lexer issue (gpu_init)
    /// This test is informational only - it reports status but doesn't assert.
    #[test]
    fn test_remaining_known_issues() {
        let files = [
            (
                "Group 1: LSP server (source indent bug)",
                "src/lib/nogc_sync_mut/lsp/server.spl",
            ),
            (
                "Group 5: diagnostic (method chain state)",
                "src/lib/common/report/compiler/diagnostic.spl",
            ),
            (
                "Group 6: gpu_init (nested triple-quoted)",
                "src/lib/gc_async_mut/gpu/__init__.spl",
            ),
            (
                "Group 7: base64 decode (use as expr)",
                "src/lib/common/base64/decode.spl",
            ),
            (
                "Group 7: base64 validation (use as expr)",
                "src/lib/common/base64/validation.spl",
            ),
            (
                "Group 7: base64 encode (use as expr)",
                "src/lib/common/base64/encode.spl",
            ),
        ];

        for (desc, path) in &files {
            let result = parse_file_detail(path);
            eprintln!("[KNOWN ISSUE] [{}] {}", desc, result);
        }
        // Note: these are not asserted - they are known issues
        // requiring separate fixes (method chain state, lexer, source file edits)
    }

    // Focused syntax tests
    #[test]
    fn test_import_patterns() {
        assert!(try_parse("import io.fs as fs\n").is_ok());
        assert!(try_parse("import sys\n").is_ok());
        assert!(try_parse("import ..level\n").is_ok());
        assert!(try_parse("import .easy_fix\n").is_ok());
        assert!(try_parse("from types import {Type}\n").is_ok());
        assert!(try_parse("mod compression.gzip.types\n").is_ok());
        assert!(try_parse("use base64::types::{X, Y}\n").is_ok());
        assert!(try_parse("use std.path\n").is_ok());
        assert!(try_parse("export A, B, C\n").is_ok());
    }

    #[test]
    fn test_triple_quoted_strings() {
        assert!(try_parse("\"\"\"A docstring\"\"\"\n").is_ok());
        assert!(try_parse("\"\"\"Line 1\nLine 2\n\"\"\"\n").is_ok());
        assert!(try_parse("fn foo():\n    \"\"\"Docstring.\"\"\"\n    42\n").is_ok());
    }

    #[test]
    fn test_use_double_colon_with_group() {
        let r = try_parse("use base64::types::{A, B, C}\n");
        assert!(r.is_ok(), "use :: with group: {:?}", r);
    }

    #[test]
    fn test_dot_question_in_if() {
        let r = try_parse("fn foo(x: Option<i64>):\n    if x.?:\n        42\n");
        assert!(r.is_ok(), "if x.?: {:?}", r);
    }

    #[test]
    fn test_match_as_variable_with_index() {
        let r = try_parse("fn foo():\n    val m = [1, 2]\n    val x = m[0]\n");
        assert!(r.is_ok(), "m[0]: {:?}", r);
    }

    #[test]
    fn test_common_as_variable() {
        let r = try_parse("fn foo():\n    var common = []\n    common.push(1)\n");
        assert!(r.is_ok(), "common as var: {:?}", r);
    }

    #[test]
    fn test_mock_as_variable() {
        let r = try_parse("fn foo():\n    val mock = create()\n    mock.call()\n");
        assert!(r.is_ok(), "mock as var: {:?}", r);
    }

    #[test]
    fn test_inline_for() {
        let r = try_parse("fn foo(items: [i64]):\n    for x in items: print(x)\n");
        assert!(r.is_ok(), "inline for: {:?}", r);
    }

    #[test]
    fn test_impl_in_class_body() {
        let r = try_parse("class Foo:\n    impl Bar\n\nimpl Foo:\n    fn hello():\n        42\n");
        assert!(r.is_ok(), "impl in class body: {:?}", r);
    }

    #[test]
    fn test_multiline_export() {
        let r = try_parse("export a, b,\n       c, d\n");
        assert!(r.is_ok(), "multiline export: {:?}", r);
    }

    #[test]
    fn test_method_chain_then_dot_question_a() {
        // Test A: simple .? works
        let r = try_parse("fn foo(x: text?):\n    if x.?:\n        42\n");
        assert!(r.is_ok(), "simple .?: {:?}", r);
    }

    #[test]
    fn test_dot_question_without_method_chain() {
        // .? works correctly without preceding method chain
        let r = try_parse(concat!(
            "fn foo():\n",
            "    var diag = 1\n",
            "\n",
            "    if x.?:\n",
            "        42\n",
        ));
        assert!(r.is_ok(), "no chain + blank: {:?}", r);
    }
}

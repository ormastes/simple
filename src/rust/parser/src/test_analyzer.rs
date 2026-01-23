//! Static test analyzer for extracting test metadata from AST.
//!
//! This module walks the AST of a parsed test file and extracts test metadata
//! WITHOUT executing any DSL code. This enables fast test listing (~1 second)
//! for large test suites.
//!
//! # Supported Test DSL Patterns
//!
//! ## Test Functions
//! - `it "description": body` - Regular test
//! - `slow_it "description": body` - Slow test (marked with is_slow)
//! - `skip_it "description": body` - Skipped test
//! - `skip "description": body` - Alias for skip_it
//! - `ignore_it "description": body` - Ignored test
//!
//! ## Grouping Functions
//! - `describe "name": body` - Test group
//! - `context "name": body` - Test group (alias)
//! - `feature "name": body` - Feature group (Gherkin-style)
//!
//! ## Tag Comments (extracted via content analysis)
//! - `#[tag("name")]` - Attribute-style tag
//! - `# @tag name` - Comment-style tag
//! - `# @slow`, `# @skip` - Shorthand tags
//!
//! # Example
//!
//! ```simple
//! describe "Math operations":
//!     context "addition":
//!         it "adds positive numbers":
//!             expect(1 + 1).to_equal(2)
//!
//!         slow_it "handles large numbers":
//!             # This is marked as slow
//!             expect(big_calc()).to_equal(expected)
//!
//!         skip_it "future feature":
//!             # This is skipped
//!             pass
//! ```
//!
//! The analyzer extracts:
//! - Group: "Math operations" > "addition"
//! - Test: "adds positive numbers" (normal)
//! - Test: "handles large numbers" (slow)
//! - Test: "future feature" (skipped)

use std::path::PathBuf;

use crate::ast::nodes::test_meta::{FileTestMeta, TestGroupMeta, TestKind, TestMeta};
use crate::ast::{Argument, Block, Expr, Node};
use crate::token::Span;

/// Names of DSL functions that create tests
const TEST_FUNCTIONS: &[&str] = &["it", "test", "example", "specify"];
const SLOW_TEST_FUNCTIONS: &[&str] = &["slow_it", "slow_test"];
const SKIP_TEST_FUNCTIONS: &[&str] = &["skip_it", "skip", "skip_test", "pending"];
const IGNORE_TEST_FUNCTIONS: &[&str] = &["ignore_it", "ignore_test", "ignored"];

/// Names of DSL functions that create test groups
const GROUP_FUNCTIONS: &[&str] = &["describe", "context", "feature", "scenario"];

/// Analyze a parsed AST and extract test metadata.
///
/// This is the main entry point for static test analysis.
///
/// # Arguments
///
/// * `statements` - The AST nodes from parsing a test file
/// * `file_path` - Path to the source file (for diagnostics)
///
/// # Returns
///
/// `FileTestMeta` containing all extracted test metadata
pub fn extract_file_test_meta(statements: &[Node], file_path: Option<&PathBuf>) -> FileTestMeta {
    let mut analyzer = TestMetaAnalyzer::new(file_path);
    analyzer.analyze_statements(statements);
    analyzer.finish()
}

/// Internal analyzer state
struct TestMetaAnalyzer {
    /// File path for diagnostics
    file_path: Option<PathBuf>,
    /// Current group stack (for nested describe/context)
    group_stack: Vec<TestGroupMeta>,
    /// Top-level file metadata being built
    file_meta: FileTestMeta,
    /// Current group path (for building full test names)
    group_path: Vec<String>,
}

impl TestMetaAnalyzer {
    /// Create a new analyzer
    fn new(file_path: Option<&PathBuf>) -> Self {
        Self {
            file_path: file_path.cloned(),
            group_stack: Vec::new(),
            file_meta: FileTestMeta::new(),
            group_path: Vec::new(),
        }
    }

    /// Analyze a list of statements
    fn analyze_statements(&mut self, statements: &[Node]) {
        for node in statements {
            self.analyze_node(node);
        }
    }

    /// Analyze a single AST node
    fn analyze_node(&mut self, node: &Node) {
        match node {
            Node::Expression(expr) => self.analyze_expr(expr),
            Node::Let(let_stmt) => {
                // Check if the value is a test DSL call
                if let Some(ref value) = let_stmt.value {
                    self.analyze_expr(value);
                }
            }
            Node::If(if_stmt) => {
                // Analyze then and else blocks
                self.analyze_block(&if_stmt.then_block);
                if let Some(ref else_block) = if_stmt.else_block {
                    self.analyze_block(else_block);
                }
            }
            Node::For(for_stmt) => {
                self.analyze_block(&for_stmt.body);
            }
            Node::While(while_stmt) => {
                self.analyze_block(&while_stmt.body);
            }
            Node::Loop(loop_stmt) => {
                self.analyze_block(&loop_stmt.body);
            }
            Node::Match(match_stmt) => {
                for arm in &match_stmt.arms {
                    self.analyze_block(&arm.body);
                }
            }
            _ => {}
        }
    }

    /// Analyze a block
    fn analyze_block(&mut self, block: &Block) {
        self.analyze_statements(&block.statements);
    }

    /// Analyze an expression
    fn analyze_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Call { callee, args } => {
                self.analyze_call(callee, args);
            }
            Expr::DoBlock(statements) => {
                self.analyze_statements(statements);
            }
            Expr::If {
                then_branch,
                else_branch,
                ..
            } => {
                self.analyze_expr(then_branch);
                if let Some(ref else_expr) = else_branch {
                    self.analyze_expr(else_expr);
                }
            }
            Expr::Match { arms, .. } => {
                for arm in arms {
                    // MatchArm.body is a Block, not an Expr
                    self.analyze_block(&arm.body);
                }
            }
            Expr::Lambda { body, .. } => {
                self.analyze_expr(body);
            }
            _ => {}
        }
    }

    /// Analyze a function call - this is where we detect test DSL
    fn analyze_call(&mut self, callee: &Expr, args: &[Argument]) {
        // Get the function name
        let func_name = match callee {
            Expr::Identifier(name) => name.as_str(),
            Expr::Path(path) => path.last().map(|s| s.as_str()).unwrap_or(""),
            _ => {
                // Not a simple function call - analyze args for nested tests
                for arg in args {
                    self.analyze_expr(&arg.value);
                }
                return;
            }
        };

        // Check if this is a test function - don't analyze body, just record the test
        if TEST_FUNCTIONS.contains(&func_name) {
            self.add_test(args, TestKind::Normal);
            return;
        } else if SLOW_TEST_FUNCTIONS.contains(&func_name) {
            self.add_test(args, TestKind::Slow);
            return;
        } else if SKIP_TEST_FUNCTIONS.contains(&func_name) {
            self.add_test(args, TestKind::Skipped);
            return;
        } else if IGNORE_TEST_FUNCTIONS.contains(&func_name) {
            self.add_test(args, TestKind::Ignored);
            return;
        } else if GROUP_FUNCTIONS.contains(&func_name) {
            // enter_group handles the body analysis internally
            self.enter_group(args);
            return;
        }

        // For other function calls, analyze arguments for nested tests
        for arg in args {
            self.analyze_expr(&arg.value);
        }
    }

    /// Add a test from DSL call arguments
    fn add_test(&mut self, args: &[Argument], kind: TestKind) {
        // First argument should be the description (string)
        let description = args.first().and_then(|arg| extract_string(&arg.value)).unwrap_or_default();

        // Try to get span from the expression (approximation)
        let span = Span::new(0, 0, 1, 0);

        let test_meta = TestMeta::with_kind(description, span, kind);

        // Add to current group or file
        if let Some(group) = self.group_stack.last_mut() {
            let path = self.group_path.clone();
            group.add_test(test_meta, &path);
        } else {
            self.file_meta.add_top_level_test(test_meta);
        }
    }

    /// Enter a new test group (describe/context)
    fn enter_group(&mut self, args: &[Argument]) {
        // First argument should be the description
        let description = args.first().and_then(|arg| extract_string(&arg.value)).unwrap_or_default();

        let span = Span::new(0, 0, 1, 0);
        let group = TestGroupMeta::new(description.clone(), span);

        // Push group onto stack
        self.group_path.push(description);
        self.group_stack.push(group);

        // Analyze body (second argument, usually a DoBlock)
        if args.len() > 1 {
            self.analyze_expr(&args[1].value);
        }

        // Pop group and add to parent
        if let Some(completed_group) = self.group_stack.pop() {
            self.group_path.pop();

            if let Some(parent) = self.group_stack.last_mut() {
                parent.add_child(completed_group);
            } else {
                self.file_meta.add_group(completed_group);
            }
        }
    }

    /// Finish analysis and return the file metadata
    fn finish(self) -> FileTestMeta {
        self.file_meta
    }
}

/// Extract a string literal from an expression
fn extract_string(expr: &Expr) -> Option<String> {
    match expr {
        Expr::String(s) => Some(s.clone()),
        Expr::FString { parts, .. } => {
            // For f-strings, just extract the literal parts
            let mut result = String::new();
            for part in parts {
                match part {
                    crate::ast::FStringPart::Literal(s) => result.push_str(s),
                    crate::ast::FStringPart::Expr(_) => result.push_str("{...}"),
                }
            }
            Some(result)
        }
        _ => None,
    }
}

/// Extract test metadata from file content using regex patterns.
///
/// This is a fallback/supplement for cases where AST analysis misses
/// comment-based tags like `# @slow` or `#[tag("name")]`.
///
/// This function complements `extract_file_test_meta` by handling:
/// - `#[tag("name")]` attribute-style tags
/// - `# @tag name` comment-style tags
/// - `# @slow`, `# @skip` shorthand tags
pub fn extract_tags_from_content(content: &str) -> Vec<String> {
    let mut tags = Vec::new();

    // Known shorthand tags
    const SHORTHAND_TAGS: &[&str] = &["gui", "slow", "skip", "wip", "fast", "flaky", "screenshot"];

    for line in content.lines() {
        let trimmed = line.trim();

        // Match #[tag("name")]
        if let Some(rest) = trimmed.strip_prefix("#[tag(\"") {
            if let Some(end) = rest.find("\")]") {
                let tag = &rest[..end];
                tags.push(tag.to_lowercase());
            }
        }

        // Match @tag name (in comments like # @tag slow)
        if let Some(idx) = trimmed.find("@tag ") {
            let after = &trimmed[idx + 5..];
            let tag: String = after
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            if !tag.is_empty() {
                tags.push(tag.to_lowercase());
            }
        }

        // Match @name shorthand for known tags
        for shorthand in SHORTHAND_TAGS {
            let pattern = format!("@{}", shorthand);
            if trimmed.contains(&pattern) {
                if let Some(idx) = trimmed.find(&pattern) {
                    let after_idx = idx + pattern.len();
                    let is_end = after_idx >= trimmed.len();
                    let is_word_boundary = is_end
                        || !trimmed
                            .chars()
                            .nth(after_idx)
                            .map(|c| c.is_alphanumeric() || c == '_')
                            .unwrap_or(false);
                    if is_word_boundary {
                        tags.push(shorthand.to_string());
                    }
                }
            }
        }

        // Match #tag: name
        if let Some(rest) = trimmed.strip_prefix("#tag:") {
            let tag: String = rest
                .trim()
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            if !tag.is_empty() {
                tags.push(tag.to_lowercase());
            }
        }
    }

    // Deduplicate
    tags.sort();
    tags.dedup();
    tags
}

/// Merge content-based tags into file test metadata
pub fn merge_content_tags(file_meta: &mut FileTestMeta, content: &str) {
    let tags = extract_tags_from_content(content);
    for tag in tags {
        file_meta.file_tags.push(tag);
    }
    file_meta.file_tags.sort();
    file_meta.file_tags.dedup();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Argument, Expr, Node};

    fn make_test_call(func_name: &str, description: &str) -> Node {
        Node::Expression(Expr::Call {
            callee: Box::new(Expr::Identifier(func_name.to_string())),
            args: vec![Argument {
                name: None,
                value: Expr::String(description.to_string()),
            }],
        })
    }

    fn make_group_call(func_name: &str, description: &str, body: Vec<Node>) -> Node {
        Node::Expression(Expr::Call {
            callee: Box::new(Expr::Identifier(func_name.to_string())),
            args: vec![
                Argument {
                    name: None,
                    value: Expr::String(description.to_string()),
                },
                Argument {
                    name: None,
                    value: Expr::DoBlock(body),
                },
            ],
        })
    }

    #[test]
    fn test_extract_simple_test() {
        let statements = vec![make_test_call("it", "my test")];

        let meta = extract_file_test_meta(&statements, None);

        assert_eq!(meta.total_tests, 1);
        assert_eq!(meta.top_level_tests.len(), 1);
        assert_eq!(meta.top_level_tests[0].description(), Some("my test"));
        assert!(!meta.top_level_tests[0].is_slow());
    }

    #[test]
    fn test_extract_slow_test() {
        let statements = vec![make_test_call("slow_it", "slow test")];

        let meta = extract_file_test_meta(&statements, None);

        assert_eq!(meta.total_tests, 1);
        assert!(meta.top_level_tests[0].is_slow());
    }

    #[test]
    fn test_extract_skipped_test() {
        let statements = vec![make_test_call("skip_it", "skipped test")];

        let meta = extract_file_test_meta(&statements, None);

        assert_eq!(meta.total_tests, 1);
        assert!(meta.top_level_tests[0].is_skipped());
        assert_eq!(meta.skipped_count, 1);
    }

    #[test]
    fn test_extract_test_group() {
        let inner_tests = vec![
            make_test_call("it", "test 1"),
            make_test_call("slow_it", "test 2"),
        ];
        let statements = vec![make_group_call("describe", "Math", inner_tests)];

        let meta = extract_file_test_meta(&statements, None);

        assert_eq!(meta.total_tests, 2);
        assert_eq!(meta.groups.len(), 1);
        assert_eq!(meta.groups[0].description, "Math");
        assert_eq!(meta.groups[0].tests.len(), 2);
        assert_eq!(meta.slow_count, 1);
    }

    #[test]
    fn test_extract_nested_groups() {
        let inner_tests = vec![make_test_call("it", "inner test")];
        let inner_group = make_group_call("context", "nested", inner_tests);
        let outer = vec![make_group_call("describe", "outer", vec![inner_group])];

        let meta = extract_file_test_meta(&outer, None);

        assert_eq!(meta.total_tests, 1);
        assert_eq!(meta.groups.len(), 1);
        assert_eq!(meta.groups[0].children.len(), 1);
    }

    #[test]
    fn test_extract_tags_from_content() {
        let content = r#"
            # @tag integration
            #[tag("database")]
            # @slow
            #tag: network
        "#;

        let tags = extract_tags_from_content(content);

        assert!(tags.contains(&"integration".to_string()));
        assert!(tags.contains(&"database".to_string()));
        assert!(tags.contains(&"slow".to_string()));
        assert!(tags.contains(&"network".to_string()));
    }

    #[test]
    fn test_full_test_path() {
        let inner = vec![make_test_call("it", "adds numbers")];
        let group = make_group_call("describe", "Math", inner);
        let meta = extract_file_test_meta(&vec![group], None);

        let test = &meta.groups[0].tests[0];
        assert_eq!(test.full_name(), "Math > adds numbers");
    }
}

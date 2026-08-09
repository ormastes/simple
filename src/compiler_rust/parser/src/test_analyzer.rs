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
            Expr::DoBlock(statements) | Expr::UnsafeBlock(statements) => {
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
        let description = args
            .first()
            .and_then(|arg| extract_string(&arg.value))
            .unwrap_or_default();

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
        let description = args
            .first()
            .and_then(|arg| extract_string(&arg.value))
            .unwrap_or_default();

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

/// A *lower bound* on the number of BDD examples a file is obliged to execute.
///
/// This exists to catch **silently dropped examples**: when a module-level
/// statement inside a `describe` body aborts (a bare `return`, a failed import
/// whose symbol is only used there, a registration-time error), the remaining
/// `it` blocks in that `describe` — and every later `describe` — are never
/// registered.  The run then prints a green per-describe summary such as
/// `0 examples, 0 failures` and exits 0.  Measured: a five-example fixture whose
/// second `describe` body starts with a bare `return` executes 3 of 5 examples,
/// prints all-green, and exits 0.  Nothing in the output says two examples
/// vanished.
///
/// # Why this is NOT `extract_file_test_meta(..).total_tests`
///
/// `total_tests` descends into `if` / `for` / `while` / `match` bodies, so it
/// counts *conditionally generated* examples.  Comparing it against the executed
/// count would cry wolf on every legitimate `if cfg: describe ...` (declared 2,
/// executed 0 — perfectly fine) and would also undercount a `for` loop that
/// generates N examples from one `it` node.  A runner that cries wolf gets
/// worked around, which is worse than the bug.
///
/// This function therefore counts only examples that are **unconditionally
/// reachable**: it walks module-level statements and `describe`/`context` bodies
/// and nothing else.  It never enters a conditional, a loop, a `match`, a lambda
/// or a function body.  Every example it counts *must* run on every execution of
/// the file, so `executed < floor` is proof of a drop rather than a heuristic.
///
/// Skipped/ignored example forms (`skip_it`, `pending`, `ignore_it`, ...) are
/// deliberately **excluded** — whether the runtime records them as results is a
/// separate contract, and counting them could only produce false positives.
pub fn unconditional_example_floor(statements: &[Node]) -> usize {
    let mut count = 0usize;
    count_unconditional_statements(statements, &mut count);
    count
}

fn count_unconditional_statements(statements: &[Node], count: &mut usize) {
    for node in statements {
        match node {
            Node::Expression(expr) => count_unconditional_expr(expr, count),
            // A `val x = describe(...)` is unusual but harmless to follow; the
            // binding itself is still unconditional.
            Node::Let(let_stmt) => {
                if let Some(ref value) = let_stmt.value {
                    count_unconditional_expr(value, count);
                }
            }
            // Everything else — If/For/While/Loop/Match/Function — is either
            // conditional or not module-level, and is deliberately not counted.
            _ => {}
        }
    }
}

fn count_unconditional_expr(expr: &Expr, count: &mut usize) {
    match expr {
        Expr::Call { callee, args } => {
            let func_name = match &**callee {
                Expr::Identifier(name) => name.as_str(),
                Expr::Path(path) => path.last().map(|s| s.as_str()).unwrap_or(""),
                _ => return,
            };
            if TEST_FUNCTIONS.contains(&func_name) || SLOW_TEST_FUNCTIONS.contains(&func_name) {
                *count += 1;
            } else if GROUP_FUNCTIONS.contains(&func_name) {
                // Descend into the group body only — the second argument. The
                // `it` body (also an argument) is deliberately NOT descended
                // into: an example is counted once, whatever it contains.
                if args.len() > 1 {
                    count_group_body(&args[1].value, count);
                }
            }
            // Any other call (including `it_behaves_like`, which expands at
            // runtime to an unknown number of examples) contributes nothing:
            // executed > floor is fine, executed < floor is the bug.
        }
        _ => {}
    }
}

/// Walk the body of a `describe`/`context`.
///
/// Block syntax (`describe "x":` followed by an indented body) parses as a call
/// whose second argument is a zero-argument lambda wrapping the block, so the
/// lambda must be unwrapped here. The DSL invokes that body exactly once, at
/// registration time, unconditionally — which is what makes everything reached
/// through it part of the floor.
fn count_group_body(expr: &Expr, count: &mut usize) {
    match expr {
        Expr::DoBlock(statements) | Expr::UnsafeBlock(statements) => {
            count_unconditional_statements(statements, count);
        }
        Expr::Lambda { body, .. } => count_group_body(body, count),
        other => count_unconditional_expr(other, count),
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
                    crate::ast::FStringPart::ExprWithFormat(_, spec) => result.push_str(&format!("{{...:{}}}", spec)),
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
            let tag: String = after.chars().take_while(|c| c.is_alphanumeric() || *c == '_').collect();
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
    use crate::token::Span;

    fn make_test_call(func_name: &str, description: &str) -> Node {
        Node::Expression(Expr::Call {
            callee: Box::new(Expr::Identifier(func_name.to_string())),
            args: vec![Argument {
                name: None,
                value: Expr::String(description.to_string()),
                span: Span::new(0, 0, 0, 0),
                label: None,
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
                    span: Span::new(0, 0, 0, 0),
                    label: None,
                },
                Argument {
                    name: None,
                    value: Expr::DoBlock(body),
                    span: Span::new(0, 0, 0, 0),
                    label: None,
                },
            ],
        })
    }

    /// The floor counts every unconditionally-reachable example, across every
    /// top-level `describe` — this is the count a dropped-example check compares
    /// the executed total against.
    #[test]
    fn floor_counts_all_unconditional_examples_across_groups() {
        let statements = [
            make_group_call(
                "describe",
                "alpha",
                vec![make_test_call("it", "a1"), make_test_call("it", "a2")],
            ),
            make_group_call("describe", "beta", vec![make_test_call("it", "b1")]),
            make_test_call("it", "top level"),
        ];

        assert_eq!(unconditional_example_floor(&statements), 4);
    }

    /// A nested `context` inside a `describe` is still unconditional.
    #[test]
    fn floor_descends_through_nested_groups() {
        let statements = [make_group_call(
            "describe",
            "outer",
            vec![
                make_test_call("it", "direct"),
                make_group_call("context", "inner", vec![make_test_call("test", "nested")]),
            ],
        )];

        assert_eq!(unconditional_example_floor(&statements), 2);
    }

    /// The whole point of the floor: conditional generation must NOT be counted,
    /// or a legitimate `if cfg:` guard would be reported as a dropped example.
    #[test]
    fn floor_ignores_conditionally_generated_examples() {
        use crate::ast::{Block, IfStmt};

        let conditional = Node::If(IfStmt {
            span: Span::new(0, 0, 0, 0),
            let_pattern: None,
            condition: Expr::Bool(false),
            then_block: Block {
                span: Span::new(0, 0, 0, 0),
                statements: vec![make_test_call("it", "only sometimes")],
            },
            elif_branches: Vec::new(),
            else_block: None,
            is_suspend: false,
        });
        let statements = [make_test_call("it", "always"), conditional];

        // `total_tests` counts both; the floor counts only the unconditional one.
        assert_eq!(extract_file_test_meta(&statements, None).total_tests, 2);
        assert_eq!(unconditional_example_floor(&statements), 1);
    }

    /// Skipped/ignored forms are excluded: whether the runtime records them as
    /// results is a separate contract, and counting them could only produce
    /// false "dropped" reports.
    #[test]
    fn floor_excludes_skipped_and_ignored_forms() {
        let statements = [
            make_test_call("it", "real"),
            make_test_call("skip_it", "skipped"),
            make_test_call("pending", "pending"),
            make_test_call("ignore_it", "ignored"),
        ];

        assert_eq!(unconditional_example_floor(&statements), 1);
    }

    /// `it_behaves_like` expands at runtime to an unknown number of examples, so
    /// it contributes zero to the floor: executed > floor is fine, only
    /// executed < floor is a drop.
    #[test]
    fn floor_does_not_count_runtime_expanded_shared_examples() {
        let statements = [make_group_call(
            "describe",
            "alpha",
            vec![
                make_test_call("it", "a1"),
                make_test_call("it_behaves_like", "some shared group"),
            ],
        )];

        assert_eq!(unconditional_example_floor(&statements), 1);
    }

    /// A file with no BDD DSL at all has a floor of zero, so ordinary programs
    /// are never subject to the check.
    #[test]
    fn floor_is_zero_for_a_non_spec_file() {
        let statements = [Node::Expression(Expr::Call {
            callee: Box::new(Expr::Identifier("print".to_string())),
            args: vec![],
        })];

        assert_eq!(unconditional_example_floor(&statements), 0);
    }

    #[test]
    fn test_extract_simple_test() {
        let statements = [make_test_call("it", "my test")];

        let meta = extract_file_test_meta(&statements, None);

        assert_eq!(meta.total_tests, 1);
        assert_eq!(meta.top_level_tests.len(), 1);
        assert_eq!(meta.top_level_tests[0].description(), Some("my test"));
        assert!(!meta.top_level_tests[0].is_slow());
    }

    #[test]
    fn test_extract_slow_test() {
        let statements = [make_test_call("slow_it", "slow test")];

        let meta = extract_file_test_meta(&statements, None);

        assert_eq!(meta.total_tests, 1);
        assert!(meta.top_level_tests[0].is_slow());
    }

    #[test]
    fn test_extract_skipped_test() {
        let statements = [make_test_call("skip_it", "skipped test")];

        let meta = extract_file_test_meta(&statements, None);

        assert_eq!(meta.total_tests, 1);
        assert!(meta.top_level_tests[0].is_skipped());
        assert_eq!(meta.skipped_count, 1);
    }

    #[test]
    fn test_extract_test_group() {
        let inner_tests = vec![make_test_call("it", "test 1"), make_test_call("slow_it", "test 2")];
        let statements = [make_group_call("describe", "Math", inner_tests)];

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
        let outer = [make_group_call("describe", "outer", vec![inner_group])];

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
        let meta = extract_file_test_meta(&[group], None);

        let test = &meta.groups[0].tests[0];
        assert_eq!(test.full_name(), "Math > adds numbers");
    }
}

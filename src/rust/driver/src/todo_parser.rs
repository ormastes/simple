//! TODO comment parser for Simple and Rust source files.
//!
//! This module extracts TODO/FIXME comments from both Simple (.spl) and Rust (.rs) files,
//! validates them against the project's TODO format specification, and provides structured
//! data for the TODO database system.
//!
//! Format specification:
//! ```text
//! TODO: [area][priority] description [#issue] [blocked:#issue,#issue]
//! FIXME: [area][priority] description [#issue] [blocked:#issue,#issue]
//! ```
//!
//! #![skip_todo]

use regex::Regex;
use std::fs;
use std::path::{Path, PathBuf};

/// Valid TODO areas
const TODO_AREAS: &[&str] = &[
    "runtime", "codegen", "compiler", "parser", "type", "stdlib", "gpu", "ui", "test", "driver", "loader", "pkg", "doc",
];

/// Valid TODO priorities (both numeric and named)
const TODO_PRIORITIES: &[&str] = &["P0", "P1", "P2", "P3", "critical", "high", "medium", "low"];

/// Represents a parsed TODO comment
#[derive(Debug, Clone, PartialEq)]
pub struct TodoItem {
    /// TODO or FIXME
    pub keyword: String,
    /// Component area (runtime, codegen, etc.)
    pub area: String,
    /// Priority level (P0-P3 or critical/high/medium/low)
    pub priority: String,
    /// Description of what needs to be done
    pub description: String,
    /// Optional issue number (without #)
    pub issue: Option<String>,
    /// Optional blocked issue numbers (without #)
    pub blocked: Vec<String>,
    /// Source file path
    pub file: PathBuf,
    /// Line number in file (1-indexed)
    pub line: usize,
    /// Full original comment text
    pub raw_text: String,
}

impl TodoItem {
    /// Normalize priority (critical -> P0, high -> P1, etc.)
    pub fn normalized_priority(&self) -> String {
        normalize_priority(&self.priority)
    }

    /// Check if TODO is valid according to format spec
    pub fn is_valid(&self) -> bool {
        TODO_AREAS.contains(&self.area.as_str()) && TODO_PRIORITIES.contains(&self.priority.as_str())
    }

    /// Get validation errors if any
    pub fn validation_errors(&self) -> Vec<String> {
        let mut errors = Vec::new();

        if !TODO_AREAS.contains(&self.area.as_str()) {
            errors.push(format!(
                "Invalid area '{}'. Valid areas: {}",
                self.area,
                TODO_AREAS.join(", ")
            ));
        }

        if !TODO_PRIORITIES.contains(&self.priority.as_str()) {
            errors.push(format!(
                "Invalid priority '{}'. Valid priorities: {}",
                self.priority,
                TODO_PRIORITIES.join(", ")
            ));
        }

        errors
    }
}

/// Parse result for a single file
#[derive(Debug)]
pub struct ParseResult {
    /// Successfully parsed TODOs
    pub todos: Vec<TodoItem>,
    /// Parse errors encountered
    pub errors: Vec<ParseError>,
}

/// Parse error
#[derive(Debug)]
pub struct ParseError {
    pub file: PathBuf,
    pub line: usize,
    pub message: String,
    pub raw_text: String,
}

/// TODO comment parser
pub struct TodoParser {
    /// Regex pattern for TODO format
    pattern: Regex,
    /// Whether to include invalid TODOs in results
    include_invalid: bool,
}

impl TodoParser {
    /// Create a new TODO parser
    pub fn new() -> Self {
        // Pattern: TODO/FIXME: [area][priority] description [#issue] [blocked:#issue,#issue]
        let pattern = Regex::new(
            r"(TODO|FIXME):\s*\[([^\]]+)\]\[([^\]]+)\]\s*(.+?)(?:\s*\[#(\d+)\])?(?:\s*\[blocked:((?:#?\d+(?:,#?\d+)*)?)\])?\s*$"
        ).unwrap();

        Self {
            pattern,
            include_invalid: false,
        }
    }

    /// Create parser that includes invalid TODOs
    pub fn with_invalid(mut self) -> Self {
        self.include_invalid = true;
        self
    }

    /// Parse TODOs from a file
    pub fn parse_file(&self, path: &Path) -> Result<ParseResult, String> {
        let content = fs::read_to_string(path).map_err(|e| format!("Failed to read file: {}", e))?;

        let language = detect_language(path);
        match language {
            Language::Rust => self.parse_rust(&content, path),
            Language::Simple => self.parse_simple(&content, path),
            Language::Markdown => self.parse_markdown(&content, path),
            Language::Unknown => Err(format!("Unsupported file type: {}", path.display())),
        }
    }

    /// Check if file has #![skip_todo] at the top
    fn has_file_level_skip(content: &str) -> bool {
        // Check first 20 lines for skip markers
        for line in content.lines().take(20) {
            let trimmed = line.trim();
            // Primary pattern: #![skip_todo]
            if trimmed.contains("#![skip_todo]") {
                return true;
            }
            // Also support: #![allow(todo_format)] for lint consistency
            if trimmed.contains("#![allow(todo_format)]") {
                return true;
            }
            // Markdown HTML comments: <!-- skip_todo -->
            if trimmed.contains("skip_todo") && trimmed.starts_with("<!--") {
                return true;
            }
            // Comment-based alternatives
            // Rust: // skip_todo
            // Simple: # skip_todo
            if trimmed.contains("skip_todo") && (trimmed.starts_with("//") || trimmed.starts_with('#')) {
                return true;
            }
        }
        false
    }

    /// Parse TODOs from Rust source code
    fn parse_rust(&self, content: &str, path: &Path) -> Result<ParseResult, String> {
        let mut todos = Vec::new();
        let mut errors = Vec::new();

        // Check for file-level skip attribute
        if Self::has_file_level_skip(content) {
            return Ok(ParseResult { todos, errors });
        }

        for (line_num, line) in content.lines().enumerate() {
            let line_num = line_num + 1; // 1-indexed
            let trimmed = line.trim();

            // Check for Rust comments: // or ///
            if !trimmed.starts_with("//") {
                continue;
            }

            // Extract comment content
            let comment = if trimmed.starts_with("///") {
                trimmed.trim_start_matches("///").trim()
            } else {
                trimmed.trim_start_matches("//").trim()
            };

            // Check if contains TODO or FIXME
            if !comment.contains("TODO") && !comment.contains("FIXME") {
                continue;
            }

            // Skip if inside string literal (simple heuristic)
            if is_in_string(trimmed, "TODO") || is_in_string(trimmed, "FIXME") {
                continue;
            }

            // Try to parse TODO
            match self.parse_todo_comment(comment, path.to_path_buf(), line_num, line.to_string()) {
                Ok(Some(todo)) => {
                    if self.include_invalid || todo.is_valid() {
                        todos.push(todo);
                    } else {
                        errors.push(ParseError {
                            file: path.to_path_buf(),
                            line: line_num,
                            message: format!("Invalid TODO format: {}", todo.validation_errors().join(", ")),
                            raw_text: line.to_string(),
                        });
                    }
                }
                Ok(None) => {
                    // Not a TODO comment, skip
                }
                Err(msg) => {
                    errors.push(ParseError {
                        file: path.to_path_buf(),
                        line: line_num,
                        message: msg,
                        raw_text: line.to_string(),
                    });
                }
            }
        }

        Ok(ParseResult { todos, errors })
    }

    /// Parse TODOs from Simple source code
    fn parse_simple(&self, content: &str, path: &Path) -> Result<ParseResult, String> {
        let mut todos = Vec::new();
        let mut errors = Vec::new();

        // Check for file-level skip attribute
        if Self::has_file_level_skip(content) {
            return Ok(ParseResult { todos, errors });
        }

        for (line_num, line) in content.lines().enumerate() {
            let line_num = line_num + 1; // 1-indexed
            let trimmed = line.trim();

            // Check for Simple comments: #
            if !trimmed.starts_with('#') {
                continue;
            }

            // Extract comment content
            let comment = trimmed.trim_start_matches('#').trim();

            // Check if contains TODO or FIXME
            if !comment.contains("TODO") && !comment.contains("FIXME") {
                continue;
            }

            // Skip if inside string literal
            if is_in_string(trimmed, "TODO") || is_in_string(trimmed, "FIXME") {
                continue;
            }

            // Try to parse TODO
            match self.parse_todo_comment(comment, path.to_path_buf(), line_num, line.to_string()) {
                Ok(Some(todo)) => {
                    if self.include_invalid || todo.is_valid() {
                        todos.push(todo);
                    } else {
                        errors.push(ParseError {
                            file: path.to_path_buf(),
                            line: line_num,
                            message: format!("Invalid TODO format: {}", todo.validation_errors().join(", ")),
                            raw_text: line.to_string(),
                        });
                    }
                }
                Ok(None) => {
                    // Not a TODO comment, skip
                }
                Err(msg) => {
                    errors.push(ParseError {
                        file: path.to_path_buf(),
                        line: line_num,
                        message: msg,
                        raw_text: line.to_string(),
                    });
                }
            }
        }

        Ok(ParseResult { todos, errors })
    }

    /// Parse TODOs from Markdown files
    fn parse_markdown(&self, content: &str, path: &Path) -> Result<ParseResult, String> {
        let mut todos = Vec::new();
        let mut errors = Vec::new();

        // Check for file-level skip attribute
        if Self::has_file_level_skip(content) {
            return Ok(ParseResult { todos, errors });
        }

        // Pattern for HTML comments: <!-- TODO: ... -->
        let html_comment_pattern = Regex::new(r"<!--\s*(.+?)\s*-->").unwrap();

        for (line_num, line) in content.lines().enumerate() {
            let line_num = line_num + 1; // 1-indexed

            // Check for HTML comments
            for cap in html_comment_pattern.captures_iter(line) {
                let comment = cap.get(1).map(|m| m.as_str()).unwrap_or("");

                if !comment.contains("TODO") && !comment.contains("FIXME") {
                    continue;
                }

                match self.parse_todo_comment(comment, path.to_path_buf(), line_num, line.to_string()) {
                    Ok(Some(todo)) => {
                        if self.include_invalid || todo.is_valid() {
                            todos.push(todo);
                        } else {
                            errors.push(ParseError {
                                file: path.to_path_buf(),
                                line: line_num,
                                message: format!("Invalid TODO format: {}", todo.validation_errors().join(", ")),
                                raw_text: line.to_string(),
                            });
                        }
                    }
                    Ok(None) => {}
                    Err(msg) => {
                        errors.push(ParseError {
                            file: path.to_path_buf(),
                            line: line_num,
                            message: msg,
                            raw_text: line.to_string(),
                        });
                    }
                }
            }
        }

        Ok(ParseResult { todos, errors })
    }

    /// Parse a single TODO comment line
    fn parse_todo_comment(
        &self,
        comment: &str,
        file: PathBuf,
        line: usize,
        raw_text: String,
    ) -> Result<Option<TodoItem>, String> {
        // Check if starts with TODO: or FIXME:
        if !comment.starts_with("TODO:") && !comment.starts_with("FIXME:") {
            return Ok(None); // Not a standard TODO comment
        }

        // Try to match the pattern
        if let Some(captures) = self.pattern.captures(comment) {
            let keyword = captures.get(1).unwrap().as_str().to_string();
            let area = captures.get(2).unwrap().as_str().trim().to_string();
            let priority = captures.get(3).unwrap().as_str().trim().to_string();
            let description = captures.get(4).unwrap().as_str().trim().to_string();
            let issue = captures.get(5).map(|m| m.as_str().to_string());
            let blocked = captures
                .get(6)
                .map(|m| {
                    m.as_str()
                        .split(',')
                        .map(|s| s.trim().trim_start_matches('#').to_string())
                        .filter(|s| !s.is_empty())
                        .collect()
                })
                .unwrap_or_default();

            Ok(Some(TodoItem {
                keyword,
                area,
                priority,
                description,
                issue,
                blocked,
                file,
                line,
                raw_text,
            }))
        } else {
            Err("TODO/FIXME missing [area][priority] format. Expected: TODO: [area][priority] description".to_string())
        }
    }

    /// Scan directory recursively for TODO comments
    pub fn scan_directory(&self, dir: &Path) -> Result<ParseResult, String> {
        let mut all_todos = Vec::new();
        let mut all_errors = Vec::new();

        self.scan_directory_recursive(dir, &mut all_todos, &mut all_errors)?;

        Ok(ParseResult {
            todos: all_todos,
            errors: all_errors,
        })
    }

    fn scan_directory_recursive(
        &self,
        dir: &Path,
        todos: &mut Vec<TodoItem>,
        errors: &mut Vec<ParseError>,
    ) -> Result<(), String> {
        if !dir.exists() || !dir.is_dir() {
            return Err(format!("Not a valid directory: {}", dir.display()));
        }

        let entries = fs::read_dir(dir).map_err(|e| e.to_string())?;

        for entry in entries {
            let entry = entry.map_err(|e| e.to_string())?;
            let path = entry.path();

            // Skip hidden files and directories
            if path
                .file_name()
                .and_then(|n| n.to_str())
                .map(|n| n.starts_with('.'))
                .unwrap_or(false)
            {
                continue;
            }

            // Skip target, build, vendor directories
            if path.is_dir() {
                let dir_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
                if matches!(dir_name, "target" | "build" | "vendor" | "node_modules") {
                    continue;
                }

                self.scan_directory_recursive(&path, todos, errors)?;
            } else if path.is_file() {
                // Only process supported file types
                if detect_language(&path) != Language::Unknown {
                    match self.parse_file(&path) {
                        Ok(result) => {
                            todos.extend(result.todos);
                            errors.extend(result.errors);
                        }
                        Err(e) => {
                            eprintln!("Warning: Failed to parse {}: {}", path.display(), e);
                        }
                    }
                }
            }
        }

        Ok(())
    }
}

impl Default for TodoParser {
    fn default() -> Self {
        Self::new()
    }
}

/// Source code language
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Language {
    Rust,
    Simple,
    Markdown,
    Unknown,
}

/// Detect language from file extension
fn detect_language(path: &Path) -> Language {
    match path.extension().and_then(|e| e.to_str()) {
        Some("rs") => Language::Rust,
        Some("spl") => Language::Simple,
        Some("md") => Language::Markdown,
        _ => Language::Unknown,
    }
}

/// Normalize priority level
fn normalize_priority(priority: &str) -> String {
    match priority.to_lowercase().as_str() {
        "critical" => "P0".to_string(),
        "high" => "P1".to_string(),
        "medium" => "P2".to_string(),
        "low" => "P3".to_string(),
        _ => priority.to_string(), // Keep P0-P3 as-is
    }
}

/// Check if keyword appears inside a string literal (simple heuristic)
fn is_in_string(line: &str, keyword: &str) -> bool {
    if let Some(keyword_pos) = line.find(keyword) {
        let before = &line[..keyword_pos];
        let double_quotes = before.matches('"').count();
        let single_quotes = before.matches('\'').count();
        // If odd number of quotes, we're inside a string
        double_quotes % 2 == 1 || single_quotes % 2 == 1
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_rust_todo() {
        let parser = TodoParser::new();
        let content = r#"
// TODO: [runtime][P0] Implement monoio TCP write [#234]
fn main() {
    // FIXME: [stdlib][critical] Fix memory leak [#567] [blocked:#123]
    println!("hello");
}
"#;
        let result = parser.parse_rust(content, Path::new("test.rs")).unwrap();

        assert_eq!(result.todos.len(), 2);
        assert_eq!(result.errors.len(), 0);

        let todo1 = &result.todos[0];
        assert_eq!(todo1.keyword, "TODO");
        assert_eq!(todo1.area, "runtime");
        assert_eq!(todo1.priority, "P0");
        assert_eq!(todo1.description, "Implement monoio TCP write");
        assert_eq!(todo1.issue, Some("234".to_string()));
        assert_eq!(todo1.line, 2);

        let todo2 = &result.todos[1];
        assert_eq!(todo2.keyword, "FIXME");
        assert_eq!(todo2.area, "stdlib");
        assert_eq!(todo2.priority, "critical");
        assert_eq!(todo2.blocked, vec!["123".to_string()]);
    }

    #[test]
    fn test_parse_simple_todo() {
        let parser = TodoParser::new();
        let content = r#"
# TODO: [gpu][P1] Create Vector3 variant [#789] [blocked:#100]
fn main():
    # FIXME: [parser][P2] Handle edge case
    print "hello"
"#;
        let result = parser.parse_simple(content, Path::new("test.spl")).unwrap();

        assert_eq!(result.todos.len(), 2);

        let todo1 = &result.todos[0];
        assert_eq!(todo1.keyword, "TODO");
        assert_eq!(todo1.area, "gpu");
        assert_eq!(todo1.priority, "P1");
        assert_eq!(todo1.blocked, vec!["100".to_string()]);

        let todo2 = &result.todos[1];
        assert_eq!(todo2.keyword, "FIXME");
        assert_eq!(todo2.area, "parser");
        assert_eq!(todo2.priority, "P2");
    }

    #[test]
    fn test_parse_invalid_todo() {
        let parser = TodoParser::new();
        let content = r#"
// TODO: implement this feature
// TODO: [invalid_area][P1] Do something
// TODO: [runtime][P99] Invalid priority
"#;
        let result = parser.parse_rust(content, Path::new("test.rs")).unwrap();

        // Invalid TODOs should be in errors, not todos
        assert_eq!(result.todos.len(), 0);
        assert_eq!(result.errors.len(), 3);
    }

    #[test]
    fn test_normalize_priority() {
        assert_eq!(normalize_priority("critical"), "P0");
        assert_eq!(normalize_priority("high"), "P1");
        assert_eq!(normalize_priority("medium"), "P2");
        assert_eq!(normalize_priority("low"), "P3");
        assert_eq!(normalize_priority("P0"), "P0");
        assert_eq!(normalize_priority("P1"), "P1");
    }

    #[test]
    fn test_validation() {
        let parser = TodoParser::new();
        let content = "// TODO: [runtime][P0] Test TODO";
        let result = parser.parse_rust(content, Path::new("test.rs")).unwrap();

        assert_eq!(result.todos.len(), 1);
        let todo = &result.todos[0];
        assert!(todo.is_valid());
        assert!(todo.validation_errors().is_empty());
    }

    #[test]
    fn test_invalid_validation() {
        let parser = TodoParser::new().with_invalid();
        let content = "// TODO: [invalid][P0] Test TODO";
        let result = parser.parse_rust(content, Path::new("test.rs")).unwrap();

        assert_eq!(result.todos.len(), 1);
        let todo = &result.todos[0];
        assert!(!todo.is_valid());
        assert!(!todo.validation_errors().is_empty());
    }

    #[test]
    fn test_skip_string_literals() {
        let parser = TodoParser::new();
        let content = r#"
// TODO: [runtime][P0] Real TODO
let msg = "TODO: this is not a real TODO";
"#;
        let result = parser.parse_rust(content, Path::new("test.rs")).unwrap();

        // Should only find the first TODO, not the one in the string
        assert_eq!(result.todos.len(), 1);
        assert_eq!(result.todos[0].line, 2);
    }

    #[test]
    fn test_multiple_blocked_issues() {
        let parser = TodoParser::new();
        let content = "// TODO: [compiler][P1] Test [#123] [blocked:#100,#101,#102]";
        let result = parser.parse_rust(content, Path::new("test.rs")).unwrap();

        assert_eq!(result.todos.len(), 1);
        let todo = &result.todos[0];
        assert_eq!(todo.blocked, vec!["100", "101", "102"]);
    }

    #[test]
    fn test_todoitem_normalized_priority() {
        let item = TodoItem {
            keyword: "TODO".to_string(),
            area: "runtime".to_string(),
            priority: "critical".to_string(),
            description: "Test".to_string(),
            issue: None,
            blocked: vec![],
            file: PathBuf::from("test.rs"),
            line: 1,
            raw_text: "".to_string(),
        };
        assert_eq!(item.normalized_priority(), "P0");

        let item2 = TodoItem {
            priority: "high".to_string(),
            ..item.clone()
        };
        assert_eq!(item2.normalized_priority(), "P1");

        let item3 = TodoItem {
            priority: "medium".to_string(),
            ..item.clone()
        };
        assert_eq!(item3.normalized_priority(), "P2");

        let item4 = TodoItem {
            priority: "low".to_string(),
            ..item.clone()
        };
        assert_eq!(item4.normalized_priority(), "P3");
    }

    #[test]
    fn test_todoitem_validation_both_invalid() {
        let item = TodoItem {
            keyword: "TODO".to_string(),
            area: "invalid_area".to_string(),
            priority: "P99".to_string(),
            description: "Test".to_string(),
            issue: None,
            blocked: vec![],
            file: PathBuf::from("test.rs"),
            line: 1,
            raw_text: "".to_string(),
        };

        assert!(!item.is_valid());
        let errors = item.validation_errors();
        assert_eq!(errors.len(), 2);
        assert!(errors[0].contains("Invalid area"));
        assert!(errors[1].contains("Invalid priority"));
    }

    #[test]
    fn test_parse_markdown_html_comments() {
        let parser = TodoParser::new();
        let content = r#"
# My Document

<!-- TODO: [doc][P2] Update examples -->

Some text here.

<!-- FIXME: [doc][P1] Fix typo [#456] -->
"#;
        let result = parser.parse_markdown(content, Path::new("README.md")).unwrap();

        assert_eq!(result.todos.len(), 2);

        let todo1 = &result.todos[0];
        assert_eq!(todo1.keyword, "TODO");
        assert_eq!(todo1.area, "doc");
        assert_eq!(todo1.priority, "P2");
        assert_eq!(todo1.description, "Update examples");

        let todo2 = &result.todos[1];
        assert_eq!(todo2.keyword, "FIXME");
        assert_eq!(todo2.issue, Some("456".to_string()));
    }

    #[test]
    fn test_parse_doc_comments() {
        let parser = TodoParser::new();
        let content = r#"
/// Module documentation
/// TODO: [doc][P3] Add more examples
pub struct MyStruct {
    /// TODO: [runtime][P2] Optimize this field
    field: i32,
}
"#;
        let result = parser.parse_rust(content, Path::new("test.rs")).unwrap();

        assert_eq!(result.todos.len(), 2);
        assert_eq!(result.todos[0].area, "doc");
        assert_eq!(result.todos[1].area, "runtime");
    }

    #[test]
    fn test_blocked_issues_without_hash() {
        let parser = TodoParser::new();
        let content = "// TODO: [runtime][P1] Test [blocked:100,200]";
        let result = parser.parse_rust(content, Path::new("test.rs")).unwrap();

        assert_eq!(result.todos.len(), 1);
        let todo = &result.todos[0];
        assert_eq!(todo.blocked, vec!["100", "200"]);
    }

    #[test]
    fn test_case_sensitive_priority() {
        let parser = TodoParser::new().with_invalid();
        let content = r#"
// TODO: [runtime][CRITICAL] Test 1
// TODO: [runtime][High] Test 2
// TODO: [runtime][MEDIUM] Test 3
// TODO: [runtime][LOW] Test 4
"#;
        let result = parser.parse_rust(content, Path::new("test.rs")).unwrap();

        // Parser is case-sensitive for priorities in parsing,
        // but normalization handles case-insensitivity
        // With with_invalid(), we get the TODOs even if invalid
        assert_eq!(result.todos.len(), 4);

        // Check normalized priorities work for any case
        assert_eq!(result.todos[0].normalized_priority(), "P0");
        assert_eq!(result.todos[1].normalized_priority(), "P1");
        assert_eq!(result.todos[2].normalized_priority(), "P2");
        assert_eq!(result.todos[3].normalized_priority(), "P3");
    }

    #[test]
    fn test_all_valid_areas() {
        let parser = TodoParser::new();
        let areas = vec![
            "runtime", "codegen", "compiler", "parser", "type", "stdlib",
            "gpu", "ui", "test", "driver", "loader", "pkg", "doc",
        ];

        for area in areas {
            let content = format!("// TODO: [{}][P1] Test", area);
            let result = parser.parse_rust(&content, Path::new("test.rs")).unwrap();
            assert_eq!(result.todos.len(), 1, "Failed for area: {}", area);
            assert!(result.todos[0].is_valid(), "Invalid area: {}", area);
        }
    }

    #[test]
    fn test_all_valid_priorities() {
        let parser = TodoParser::new();
        let priorities = vec!["P0", "P1", "P2", "P3", "critical", "high", "medium", "low"];

        for priority in priorities {
            let content = format!("// TODO: [runtime][{}] Test", priority);
            let result = parser.parse_rust(&content, Path::new("test.rs")).unwrap();
            assert_eq!(result.todos.len(), 1, "Failed for priority: {}", priority);
            assert!(result.todos[0].is_valid(), "Invalid priority: {}", priority);
        }
    }

    #[test]
    fn test_empty_description() {
        let parser = TodoParser::new();
        let content = "// TODO: [runtime][P1]";
        let result = parser.parse_rust(content, Path::new("test.rs")).unwrap();

        // Empty description should cause parse error
        assert_eq!(result.todos.len(), 0);
        assert_eq!(result.errors.len(), 1);
    }

    #[test]
    fn test_special_characters_in_description() {
        let parser = TodoParser::new();
        let content = r#"// TODO: [runtime][P1] Fix <angle> & {curly} brackets"#;
        let result = parser.parse_rust(content, Path::new("test.rs")).unwrap();

        assert_eq!(result.todos.len(), 1);
        let desc = &result.todos[0].description;
        assert!(desc.contains("<angle>"));
        assert!(desc.contains("{curly}"));
    }

    #[test]
    fn test_inline_comments_not_parsed() {
        let parser = TodoParser::new();
        let content = r#"let x = "done"; // TODO: [runtime][P1] Inline comment not parsed"#;
        let result = parser.parse_rust(content, Path::new("test.rs")).unwrap();

        // Parser only processes lines that START with //, not inline comments after code
        assert_eq!(result.todos.len(), 0);
    }

    #[test]
    fn test_simple_hash_comment_leading_whitespace() {
        let parser = TodoParser::new();
        let content = "        # TODO: [runtime][P2] Deeply indented";
        let result = parser.parse_simple(content, Path::new("test.spl")).unwrap();

        assert_eq!(result.todos.len(), 1);
        assert_eq!(result.todos[0].description, "Deeply indented");
    }

    #[test]
    fn test_multiple_markdown_comments_same_line() {
        let parser = TodoParser::new();
        let content = "<!-- TODO: [doc][P2] First --> text <!-- FIXME: [doc][P1] Second -->";
        let result = parser.parse_markdown(content, Path::new("test.md")).unwrap();

        assert_eq!(result.todos.len(), 2);
        assert_eq!(result.todos[0].keyword, "TODO");
        assert_eq!(result.todos[1].keyword, "FIXME");
    }

    #[test]
    fn test_language_detection() {
        assert_eq!(detect_language(Path::new("test.rs")), Language::Rust);
        assert_eq!(detect_language(Path::new("test.spl")), Language::Simple);
        assert_eq!(detect_language(Path::new("README.md")), Language::Markdown);
        assert_eq!(detect_language(Path::new("test.txt")), Language::Unknown);
        assert_eq!(detect_language(Path::new("src/my.module.rs")), Language::Rust);
    }

    #[test]
    fn test_is_in_string_helper() {
        assert_eq!(is_in_string("let x = \"TODO", "TODO"), true);
        assert_eq!(is_in_string("let x = \"done\"; // TODO", "TODO"), false);
        assert_eq!(is_in_string("let x = 'TODO", "TODO"), true);
        assert_eq!(is_in_string("let x = 'done'; // TODO", "TODO"), false);
        assert_eq!(is_in_string("no keyword here", "TODO"), false);
    }

    #[test]
    fn test_normalize_priority_all_variants() {
        assert_eq!(normalize_priority("critical"), "P0");
        assert_eq!(normalize_priority("CRITICAL"), "P0");
        assert_eq!(normalize_priority("high"), "P1");
        assert_eq!(normalize_priority("High"), "P1");
        assert_eq!(normalize_priority("medium"), "P2");
        assert_eq!(normalize_priority("MEDIUM"), "P2");
        assert_eq!(normalize_priority("low"), "P3");
        assert_eq!(normalize_priority("LOW"), "P3");
        assert_eq!(normalize_priority("P0"), "P0");
        assert_eq!(normalize_priority("P1"), "P1");
        assert_eq!(normalize_priority("P2"), "P2");
        assert_eq!(normalize_priority("P3"), "P3");
        assert_eq!(normalize_priority("invalid"), "invalid");
    }
}

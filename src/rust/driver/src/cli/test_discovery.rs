// Test discovery and tag matching
//
// This module handles:
// - Discovering test files in directories
// - Checking if files are test files
// - Extracting and matching tags

use std::path::{Path, PathBuf};

use super::test_runner::TestLevel;

/// Discover test files in a directory
pub fn discover_tests(dir: &Path, level: TestLevel) -> Vec<PathBuf> {
    discover_tests_with_skip(dir, level, false)
}

/// Discover test files in a directory, optionally including .skip files
pub fn discover_tests_with_skip(dir: &Path, level: TestLevel, include_skip_files: bool) -> Vec<PathBuf> {
    let mut tests = Vec::new();

    if !dir.is_dir() {
        if is_test_file(dir) || (include_skip_files && is_skip_test_file(dir)) {
            tests.push(dir.to_path_buf());
        }
        return tests;
    }

    // Walk directory recursively
    if let Ok(entries) = std::fs::read_dir(dir) {
        for entry in entries.filter_map(|e| e.ok()) {
            let path = entry.path();

            if path.is_dir() {
                let dir_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");

                // Filter by test level based on directory name
                let should_include = match level {
                    TestLevel::All => true,
                    TestLevel::Unit => dir_name == "unit" || !["integration", "system"].contains(&dir_name),
                    TestLevel::Integration => dir_name == "integration",
                    TestLevel::System => dir_name == "system",
                };

                if should_include {
                    tests.extend(discover_tests_with_skip(&path, level, include_skip_files));
                }
            } else if is_test_file(&path) || (include_skip_files && is_skip_test_file(&path)) {
                tests.push(path);
            }
        }
    }

    tests.sort();
    tests
}

/// Check if a file is a test file
pub fn is_test_file(path: &Path) -> bool {
    if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
        let is_simple_ext = name.ends_with(".spl") || name.ends_with(".simple") || name.ends_with(".sscript");
        let is_test = name.contains("_spec.") || name.contains("_test.");
        is_simple_ext && is_test
    } else {
        false
    }
}

/// Check if a file is a skipped test file (*.spl.skip, *_spec.spl.skip, etc.)
pub fn is_skip_test_file(path: &Path) -> bool {
    if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
        // Match patterns like *_spec.spl.skip, *_test.spl.skip
        let is_skip_ext = name.ends_with(".spl.skip") || name.ends_with(".simple.skip") || name.ends_with(".sscript.skip");
        let is_test = name.contains("_spec.") || name.contains("_test.");
        is_skip_ext && is_test
    } else {
        false
    }
}

/// Extract tags from a test file.
///
/// Tags can be specified in the file using:
/// - `#[tag("name")]` decorator
/// - `@tag name` comment
/// - `#tag: name` comment
/// - `@name` shorthand for common tags (gui, slow, skip, wip)
///
/// Also checks:
/// - File name tags (e.g., `slow_spec.spl` matches tag "slow")
/// - `__init__.spl` in parent directories for inherited tags
pub fn extract_tags(path: &Path) -> Vec<String> {
    let mut tags = Vec::new();

    // Check file name for tag patterns
    if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
        // e.g., "slow_spec.spl" -> tag "slow", "integration_test.spl" -> tag "integration"
        let stem = name
            .trim_end_matches(".spl")
            .trim_end_matches("_spec")
            .trim_end_matches("_test");
        if !stem.is_empty() {
            // Split by underscore and take potential tag prefixes
            for part in stem.split('_') {
                if !part.is_empty() {
                    tags.push(part.to_lowercase());
                }
            }
        }
    }

    // Check __init__.spl in parent directories for inherited tags
    if let Some(parent) = path.parent() {
        tags.extend(extract_directory_tags(parent));
    }

    // Try to read file content for tag decorators/comments
    if let Ok(content) = std::fs::read_to_string(path) {
        tags.extend(extract_tags_from_content(&content));
    }

    // Deduplicate
    tags.sort();
    tags.dedup();
    tags
}

/// Known shorthand tags that can be used with @name syntax
const SHORTHAND_TAGS: &[&str] = &["gui", "slow", "skip", "wip", "fast", "flaky", "screenshot"];

/// Extract tags from file content
fn extract_tags_from_content(content: &str) -> Vec<String> {
    let mut tags = Vec::new();

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

        // Match @name shorthand for known tags (e.g., # @gui, # @slow)
        for shorthand in SHORTHAND_TAGS {
            let pattern = format!("@{}", shorthand);
            if trimmed.contains(&pattern) {
                // Make sure it's not part of a longer word
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

    tags
}

/// Extract directory-level tags from __init__.spl files
/// Walks up the directory tree to collect inherited tags
fn extract_directory_tags(dir: &Path) -> Vec<String> {
    let mut tags = Vec::new();
    let mut current = Some(dir);

    while let Some(path) = current {
        let init_file = path.join("__init__.spl");
        if init_file.exists() {
            if let Ok(content) = std::fs::read_to_string(&init_file) {
                tags.extend(extract_tags_from_content(&content));
            }
        }
        current = path.parent();
    }

    tags
}

/// Check if a test has the @gui tag
pub fn is_gui_test(path: &Path) -> bool {
    let tags = extract_tags(path);
    tags.contains(&"gui".to_string()) || tags.contains(&"screenshot".to_string())
}

/// Check if a file matches the tag filter.
///
/// Returns true if:
/// - No tag filter is specified (tag is None)
/// - The file's tags contain the filter tag
pub fn matches_tag(path: &Path, tag_filter: &Option<String>) -> bool {
    match tag_filter {
        None => true,
        Some(filter) => {
            let filter_lower = filter.to_lowercase();
            let tags = extract_tags(path);
            tags.iter().any(|t| t == &filter_lower)
        }
    }
}

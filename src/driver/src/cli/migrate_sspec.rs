// SSpec docstring migration
// Converts print-based SSpec tests to intensive docstring format

use std::fs;
use std::path::Path;

/// Migrate a single file's SSpec print-based tests to docstring format
/// Returns Ok(true) if file was/would be modified, Ok(false) if no changes needed
pub fn migrate_file_sspec(path: &Path, dry_run: bool) -> Result<bool, String> {
    eprintln!("[MIGRATE_SSPEC] Processing file: {}", path.display());
    let content = fs::read_to_string(path).map_err(|e| format!("failed to read file: {}", e))?;

    let new_content = migrate_sspec_to_docstrings(&content);

    // Debug: Print comparison info
    #[cfg(debug_assertions)]
    {
        eprintln!("DEBUG: Original length: {}", content.len());
        eprintln!("DEBUG: New length: {}", new_content.len());
        if new_content != content {
            eprintln!("DEBUG: Content changed!");
        } else {
            eprintln!("DEBUG: Content unchanged");
        }
    }

    if new_content == content {
        // No changes needed
        return Ok(false);
    }

    // Write back only if not in dry-run mode
    if !dry_run {
        fs::write(path, new_content).map_err(|e| format!("failed to write file: {}", e))?;
    }

    Ok(true)
}

/// Convert print-based SSpec patterns to intensive docstring format
fn migrate_sspec_to_docstrings(source: &str) -> String {
    let lines: Vec<&str> = source.lines().collect();
    eprintln!("DEBUG: Processing {} lines", lines.len());
    let mut result = Vec::new();
    let mut i = 0;
    let mut changes = 0;

    while i < lines.len() {
        let line = lines[i];
        let trimmed = line.trim();

        // Check for print-based describe/context/it patterns
        // Use original line to preserve indentation for pattern matching
        if let Some(converted) = convert_print_line(line) {
            eprintln!("DEBUG: Converted line: {}", line);
            changes += 1;
            result.push(converted);
            i += 1;
            continue;
        }

        // Remove manual tracking lines
        if is_manual_tracking_line(trimmed) {
            i += 1;
            continue;
        }

        // Remove banner prints
        if is_banner_print(trimmed) {
            i += 1;
            continue;
        }

        // Keep other lines as-is
        result.push(line.to_string());
        i += 1;
    }

    eprintln!("DEBUG: Made {} changes", changes);
    result.join("\n")
}

/// Convert a single print line to SSpec syntax with docstring
fn convert_print_line(line: &str) -> Option<String> {
    if !line.contains("print(") {
        return None;
    }

    // Extract the content from print('...')
    let start = line.find(&['\'', '"'])?;
    let quote_char = line.chars().nth(start)?;
    let rest = &line[start + 1..];
    let end = rest.find(quote_char)?;
    let content = &rest[..end];

    // Trim leading whitespace to check the first keyword
    let trimmed = content.trim_start();

    // Check what keyword the content STARTS with (not just contains)
    // This prevents "it nests inside describe" from being treated as "describe"

    // Pattern: describe ... (no indentation)
    if trimmed.starts_with("describe ") || trimmed.starts_with("describe:") {
        return extract_and_convert(line, "describe", 0);
    }

    // Pattern:   context ... (2 spaces)
    if trimmed.starts_with("context ") || trimmed.starts_with("context:") {
        return extract_and_convert(line, "context", 4);
    }

    // Pattern:     it ... (4 spaces)
    if trimmed.starts_with("it ") || trimmed.starts_with("it:") {
        return extract_and_convert(line, "it", 8);
    }

    None
}

/// Extract text from print statement and convert to SSpec syntax
fn extract_and_convert(line: &str, keyword: &str, indent: usize) -> Option<String> {
    // Find the content between quotes
    let start = line.find(&['\'', '"'])?;
    let quote_char = line.chars().nth(start)?;
    let rest = &line[start + 1..];
    let end = rest.find(quote_char)?;
    let content = &rest[..end];

    // Remove leading spaces and keyword
    let mut text = content.trim_start();
    if text.starts_with(keyword) {
        text = &text[keyword.len()..].trim_start();
    }

    // Remove trailing colon if present
    text = text.trim_end_matches(':').trim();

    let indent_str = " ".repeat(indent);
    let docstring_indent = " ".repeat(indent + 4);

    Some(format!(
        "{}{} \"{}\":\n{}\"\"\"\n{}TODO: Add documentation here\n{}\"\"\"",
        indent_str, keyword, text, docstring_indent, docstring_indent, docstring_indent
    ))
}

/// Check if line is manual tracking (passed/failed variables)
fn is_manual_tracking_line(line: &str) -> bool {
    // IMPORTANT: Check for [PASS]/[FAIL] FIRST, before pattern conversion
    // This prevents "print('      [PASS] nests inside describe')" from being
    // converted to a describe block
    if line.contains("[PASS]") || line.contains("[FAIL]") {
        return true;
    }

    // Check for variable declarations/assignments
    if line.contains("passed") || line.contains("failed") {
        if line.contains("= 0") || line.contains("+ 1") {
            return true;
        }
    }

    false
}

/// Check if line is a banner print statement
fn is_banner_print(line: &str) -> bool {
    if !line.contains("print(") {
        return false;
    }

    // Check for repeated separator characters
    line.contains("====")
        || line.contains("----")
        || line.contains("####")
        || line.contains("****")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_convert_print_describe() {
        let input = "print('describe Docstring parsing:')";
        let output = convert_print_line(input).unwrap();
        assert!(output.contains(r#"describe "Docstring parsing":"#));
        assert!(output.contains("\"\"\""));
    }

    #[test]
    fn test_convert_print_context() {
        let input = "print('  context extracts code blocks:')";
        let output = convert_print_line(input).unwrap();
        assert!(output.contains(r#"context "extracts code blocks":"#));
        assert!(output.contains("\"\"\""));
    }

    #[test]
    fn test_convert_print_it() {
        let input = "print('    it finds code in docstrings:')";
        let output = convert_print_line(input).unwrap();
        assert!(output.contains(r#"it "finds code in docstrings":"#));
        assert!(output.contains("\"\"\""));
    }

    #[test]
    fn test_is_manual_tracking_line() {
        assert!(is_manual_tracking_line("var passed = 0"));
        assert!(is_manual_tracking_line("passed = passed + 1"));
        assert!(is_manual_tracking_line("print('      [PASS] finds code blocks')"));
        assert!(!is_manual_tracking_line("val passed_test = true"));
    }

    #[test]
    fn test_is_banner_print() {
        assert!(is_banner_print("print('============================================================')"));
        assert!(is_banner_print("print('------------------------------------------------------------')"));
        assert!(!is_banner_print("print('regular message')"));
    }

    #[test]
    fn test_full_migration() {
        let input = r#"var passed = 0
var failed = 0

print('describe Docstring parsing:')
print('  context extracts code blocks:')
print('    it finds code in docstrings:')

if ex.code == "1 + 1":
    print('      [PASS] finds code blocks')
    passed = passed + 1"#;

        let output = migrate_sspec_to_docstrings(input);

        // Should have proper SSpec structure
        assert!(output.contains(r#"describe "Docstring parsing":"#));
        assert!(output.contains(r#"context "extracts code blocks":"#));
        assert!(output.contains(r#"it "finds code in docstrings":"#));

        // Should have docstrings
        assert!(output.contains("\"\"\""));

        // Should NOT have manual tracking
        assert!(!output.contains("var passed"));
        assert!(!output.contains("[PASS]"));
    }

    // BUG FIX TESTS - Test edge cases discovered during bulk migration

    #[test]
    fn test_it_containing_describe_keyword() {
        // Bug: "it nests inside describe" was being converted to "describe"
        // because the old code checked line.contains("describe")
        let input = "print('    it nests inside describe:')";
        let output = convert_print_line(input).unwrap();

        // Should be converted to "it", not "describe"
        assert!(output.contains(r#"it "nests inside describe":"#));
        assert!(!output.starts_with("describe"));
    }

    #[test]
    fn test_pass_fail_not_converted_to_blocks() {
        // Bug: [PASS]/[FAIL] prints containing keywords were being converted
        let input1 = "print('      [PASS] nests inside describe')";
        let input2 = "print('      [FAIL] context not found')";

        // Should NOT be converted (returns None)
        assert!(convert_print_line(input1).is_none());
        assert!(convert_print_line(input2).is_none());

        // Should be filtered out by is_manual_tracking_line
        assert!(is_manual_tracking_line(input1));
        assert!(is_manual_tracking_line(input2));
    }

    #[test]
    fn test_describe_as_first_word_only() {
        let input = "print('describe User authentication:')";
        let output = convert_print_line(input).unwrap();
        assert!(output.contains(r#"describe "User authentication":"#));
    }

    #[test]
    fn test_context_with_describe_in_text() {
        // Text contains "describe" but starts with "context"
        let input = "print('  context when describing features:')";
        let output = convert_print_line(input).unwrap();

        // Should be "context", not "describe"
        assert!(output.contains(r#"context "when describing features":"#));
        assert!(!output.starts_with("describe"));
    }

    #[test]
    fn test_it_with_context_in_text() {
        // Text contains "context" but starts with "it"
        let input = "print('    it changes context dynamically:')";
        let output = convert_print_line(input).unwrap();

        // Should be "it", not "context"
        assert!(output.contains(r#"it "changes context dynamically":"#));
        assert!(!output.contains("context \""));
    }

    #[test]
    fn test_non_bdd_print_not_converted() {
        // Regular prints without BDD keywords
        let input1 = "print('Hello world')";
        let input2 = "print('Some random text')";
        let input3 = "print('Total: {passed} passed')";

        assert!(convert_print_line(input1).is_none());
        assert!(convert_print_line(input2).is_none());
        assert!(convert_print_line(input3).is_none());
    }

    #[test]
    fn test_keyword_in_middle_not_converted() {
        // Keyword appears in middle or end of text
        let input1 = "print('text with describe in it')";
        let input2 = "print('this has context somewhere')";

        assert!(convert_print_line(input1).is_none());
        assert!(convert_print_line(input2).is_none());
    }
}

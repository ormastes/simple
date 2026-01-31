use std::collections::HashMap;
use std::path::Path;

use crate::doctest::parser::parse_doctest_text;
use crate::doctest::types::DoctestExample;

/// Parse doctest examples from Markdown content that uses doctest code fences.
/// Supports both ```sdoctest and ```simple-doctest language hints.
///
/// Extracts section names from nearest markdown headings with sequential numbering.
/// Example: "## Stack Operations" with 2 code blocks yields:
///   - "Stack Operations #1"
///   - "Stack Operations #2"
pub fn parse_markdown_doctests(content: &str, source: impl AsRef<Path>) -> Vec<DoctestExample> {
    let mut examples = Vec::new();
    let mut in_block = false;
    let mut block = String::new();
    let mut block_start_line = 0usize;

    // Section tracking for doctest naming
    let mut current_heading: Option<String> = None;
    let mut section_counts: HashMap<String, usize> = HashMap::new();

    for (idx, line) in content.lines().enumerate() {
        let trimmed = line.trim_start();

        // Track markdown headings (any level: #, ##, ###, etc.)
        if trimmed.starts_with('#') && !in_block {
            let heading_text = trimmed.trim_start_matches('#').trim().to_string();
            if !heading_text.is_empty() {
                current_heading = Some(heading_text);
            }
        }

        // Check for doctest code fence opening with language hint
        if trimmed.starts_with("```sdoctest")
            || trimmed.starts_with("```simple-doctest")
            || trimmed.starts_with("```simple")
        {
            // Only enter block if the hint is for doctests (not other code blocks)
            if trimmed.starts_with("```sdoctest") || trimmed.starts_with("```simple-doctest") {
                in_block = true;
                block.clear();
                block_start_line = idx + 2; // next line after the fence
                continue;
            }
        }

        if trimmed.starts_with("```") && in_block {
            in_block = false;
            let mut block_examples = parse_doctest_text(&block, source.as_ref());

            // Assign section names to examples
            for ex in &mut block_examples {
                ex.start_line += block_start_line;
                if let Some(ref heading) = current_heading {
                    let count = section_counts.entry(heading.clone()).or_insert(0);
                    *count += 1;
                    ex.section_name = Some(format!("{} #{}", heading, count));
                }
            }

            examples.extend(block_examples);
            block.clear();
            continue;
        }

        if in_block {
            block.push_str(line);
            block.push('\n');
        }
    }

    examples
}

/// Parse doctest examples from Simple source files (.spl).
/// Looks for """ docstring blocks with nested ```sdoctest code fences.
/// Example:
/// """
/// Description
/// ```sdoctest
/// >>> code
/// output
/// ```
/// """
pub fn parse_spl_doctests(content: &str, source: impl AsRef<Path>) -> Vec<DoctestExample> {
    let mut examples = Vec::new();
    let mut in_docstring = false;
    let mut docstring = String::new();
    let mut docstring_start_line = 0usize;

    for (idx, line) in content.lines().enumerate() {
        let line_num = idx + 1;
        let trimmed = line.trim_start();

        // Check for docstring opening
        if trimmed.starts_with("\"\"\"") && !in_docstring {
            in_docstring = true;
            docstring.clear();
            docstring_start_line = line_num;

            // Handle inline docstring on same line (e.g., """ content """)
            let rest = &trimmed[3..];
            if rest.contains("\"\"\"") && !rest.trim().is_empty() {
                // Single-line docstring - not supported for now
                in_docstring = false;
            } else {
                docstring.push_str(rest);
                docstring.push('\n');
            }
            continue;
        }

        // Check for docstring closing
        if in_docstring && trimmed.starts_with("\"\"\"") {
            in_docstring = false;

            // Extract code fences from docstring
            let mut block_examples = parse_docstring_fences(&docstring, source.as_ref());
            for ex in &mut block_examples {
                ex.start_line += docstring_start_line;
            }
            examples.extend(block_examples);
            docstring.clear();
            continue;
        }

        if in_docstring {
            docstring.push_str(line);
            docstring.push('\n');
        }
    }

    examples
}

/// Parse code fences from within a docstring.
/// Looks for ```sdoctest and ```simple-doctest fences.
fn parse_docstring_fences(docstring: &str, source: impl AsRef<Path>) -> Vec<DoctestExample> {
    let mut examples = Vec::new();
    let mut in_fence = false;
    let mut fence_content = String::new();
    let mut fence_start_line = 0usize;

    for (idx, line) in docstring.lines().enumerate() {
        let line_num = idx + 1;
        let trimmed = line.trim_start();

        // Check for code fence opening
        if (trimmed.starts_with("```sdoctest") || trimmed.starts_with("```simple-doctest")) && !in_fence {
            in_fence = true;
            fence_content.clear();
            fence_start_line = line_num;
            continue;
        }

        // Check for code fence closing
        if trimmed.starts_with("```") && in_fence {
            in_fence = false;

            // Parse examples from fence content
            let mut fence_examples = parse_doctest_text(&fence_content, source.as_ref());
            for ex in &mut fence_examples {
                ex.start_line += fence_start_line;
            }
            examples.extend(fence_examples);
            fence_content.clear();
            continue;
        }

        if in_fence {
            // Use trimmed line to handle indented code blocks in docstrings
            fence_content.push_str(trimmed);
            fence_content.push('\n');
        }
    }

    examples
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_markdown_doctests() {
        let content = r#"
## Test Section

```sdoctest
>>> x = 5
>>> x
5
```
"#;
        let examples = parse_markdown_doctests(content, "test.md");
        // Each >>> line creates a separate example (Python doctest style)
        assert_eq!(examples.len(), 2);
        assert!(examples[0].section_name.is_some());
        assert_eq!(examples[0].section_name.as_ref().unwrap(), "Test Section #1");
        assert_eq!(examples[1].section_name.as_ref().unwrap(), "Test Section #2");
    }

    #[test]
    fn test_parse_spl_doctests() {
        let content = r#"
fn foo():
    """
    Example function
    ```sdoctest
    >>> foo()
    0
    ```
    """
    0
"#;
        let examples = parse_spl_doctests(content, "test.spl");
        // One >>> line with expected output = 1 example
        assert_eq!(examples.len(), 1);
        assert_eq!(examples[0].commands[0], "foo()");
    }
}

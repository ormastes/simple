use std::path::Path;

use crate::doctest::types::{DoctestExample, Expected};

/// Identify lines that should be treated as definitions/statements rather than expressions.
/// Shared with REPL logic so doctest execution mirrors interactive behavior.
pub fn is_definition_like(line: &str) -> bool {
    let trimmed = line.trim_start();

    if let Some(first) = trimmed.split_whitespace().next() {
        if matches!(
            first,
            "let"
                | "mut"
                | "fn"
                | "struct"
                | "class"
                | "enum"
                | "trait"
                | "impl"
                | "use"
                | "type"
                | "actor"
                | "import"
                | "for"
                | "while"
                | "if"
                | "match"
        ) {
            return true;
        }
    }

    let mut chars = trimmed.char_indices().peekable();
    while let Some((idx, ch)) = chars.next() {
        if ch != '=' {
            continue;
        }
        let prev = trimmed[..idx].chars().rev().find(|c| !c.is_whitespace());
        let next = chars.clone().map(|(_, c)| c).find(|c| !c.is_whitespace());

        let is_comparison = matches!(prev, Some('=') | Some('!') | Some('<') | Some('>')) || matches!(next, Some('='));
        if !is_comparison {
            return true;
        }
    }

    false
}

/// Parse doctest examples from a plain `.sdt`/docstring style string.
pub fn parse_doctest_text(content: &str, source: impl AsRef<Path>) -> Vec<DoctestExample> {
    let mut examples = Vec::new();
    let mut commands: Vec<String> = Vec::new();
    let mut expected: Vec<String> = Vec::new();
    let mut start_line = 0usize;
    let source_path = source.as_ref().to_path_buf();

    let finish_example = |examples: &mut Vec<DoctestExample>,
                          commands: &mut Vec<String>,
                          expected: &mut Vec<String>,
                          start_line: &mut usize| {
        if commands.is_empty() {
            return;
        }

        let expected_kind = if expected.is_empty() {
            Expected::Empty
        } else if let Some(first) = expected.first() {
            if let Some(rest) = first.strip_prefix("Error:") {
                Expected::Error(rest.trim().to_string())
            } else {
                Expected::Output(expected.join("\n"))
            }
        } else {
            Expected::Empty
        };

        examples.push(DoctestExample {
            source: source_path.clone(),
            start_line: *start_line,
            commands: commands.clone(),
            expected: expected_kind,
            section_name: None,
        });

        commands.clear();
        expected.clear();
        *start_line = 0;
    };

    for (idx, raw_line) in content.lines().enumerate() {
        let line_num = idx + 1;
        let line = raw_line.trim_end();

        if let Some(rest) = line.strip_prefix(">>>") {
            if !commands.is_empty() {
                finish_example(&mut examples, &mut commands, &mut expected, &mut start_line);
            }
            start_line = line_num;
            commands.push(rest.trim_start().to_string());
            continue;
        }

        if let Some(rest) = line.strip_prefix("...") {
            // Format is "... " (prompt with space) + indented content, or just "..." + content
            let content = rest.strip_prefix(' ').unwrap_or(rest);
            if let Some(last) = commands.last_mut() {
                last.push('\n');
                last.push_str(content);
            }
            continue;
        }

        if !commands.is_empty() {
            expected.push(line.to_string());
        }
    }

    if !commands.is_empty() {
        finish_example(&mut examples, &mut commands, &mut expected, &mut start_line);
    }

    examples
}

/// Check if a snippet contains an assignment expression
pub(crate) fn contains_assignment(snippet: &str) -> bool {
    // Simple heuristic: look for '=' that's not part of '==', '!=', '<=', '>='
    let chars: Vec<char> = snippet.chars().collect();
    for i in 0..chars.len() {
        if chars[i] == '=' {
            // Check if it's part of a comparison operator
            let before = if i > 0 { chars[i - 1] } else { ' ' };
            let after = if i + 1 < chars.len() { chars[i + 1] } else { ' ' };
            if before != '=' && before != '!' && before != '<' && before != '>' && after != '=' {
                return true;
            }
        }
    }
    false
}

/// Check if a snippet is a true definition that should be saved in prelude.
/// Control flow statements (if, while, for, match) should NOT be added to prelude
/// because they execute with side effects and shouldn't be re-run on each subsequent input.
pub(crate) fn is_prelude_definition(snippet: &str) -> bool {
    let trimmed = snippet.trim_start();

    // Check keyword-based definitions
    if let Some(first) = trimmed.split_whitespace().next() {
        // Only add actual definitions, not control flow
        if matches!(
            first,
            "let" | "mut" | "fn" | "struct" | "class" | "enum" | "trait" | "impl" | "use" | "type" | "actor" | "import"
        ) {
            return true;
        }
    }

    // Check for assignment (e.g., "a = 1") - need to save variable bindings
    contains_assignment(snippet)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_definition_like() {
        assert!(is_definition_like("let x = 5"));
        assert!(is_definition_like("fn foo():"));
        assert!(is_definition_like("struct Point:"));
        assert!(is_definition_like("x = 5"));

        assert!(!is_definition_like("x == 5"));
        assert!(!is_definition_like("x != 5"));
        assert!(!is_definition_like("print x"));
    }

    #[test]
    fn test_parse_doctest_text() {
        let content = r#"
>>> x = 5
>>> x
5
"#;
        let examples = parse_doctest_text(content, "test.sdt");
        assert_eq!(examples.len(), 1);
        assert_eq!(examples[0].commands.len(), 2);
        assert_eq!(examples[0].commands[0], "x = 5");
        assert_eq!(examples[0].commands[1], "x");
        assert!(matches!(examples[0].expected, Expected::Output(_)));
    }

    #[test]
    fn test_contains_assignment() {
        assert!(contains_assignment("x = 5"));
        assert!(contains_assignment("let x = 5"));
        assert!(!contains_assignment("x == 5"));
        assert!(!contains_assignment("x != 5"));
    }

    #[test]
    fn test_is_prelude_definition() {
        assert!(is_prelude_definition("let x = 5"));
        assert!(is_prelude_definition("fn foo():"));
        assert!(is_prelude_definition("x = 5"));

        assert!(!is_prelude_definition("if x:"));
        assert!(!is_prelude_definition("while x:"));
        assert!(!is_prelude_definition("for x in y:"));
    }
}

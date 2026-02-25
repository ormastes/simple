use std::fs;
use std::path::{Path, PathBuf};

use std::collections::HashMap;

use crate::interpreter::{Interpreter, RunConfig};

/// Expected outcome for a doctest example.
#[derive(Debug, Clone, PartialEq)]
pub enum Expected {
    Output(String),
    Error(String),
    Empty,
}

/// A single doctest example parsed from a source file.
#[derive(Debug, Clone, PartialEq)]
pub struct DoctestExample {
    pub source: PathBuf,
    pub start_line: usize,
    pub commands: Vec<String>,
    pub expected: Expected,
}

/// Result of running a doctest example.
#[derive(Debug, Clone, PartialEq)]
pub struct DoctestResult {
    pub example: DoctestExample,
    pub status: DoctestStatus,
    pub actual: String,
}

#[derive(Debug, Clone, PartialEq)]
pub enum DoctestStatus {
    Passed,
    Failed(String),
}

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

        let is_comparison = matches!(prev, Some('=') | Some('!') | Some('<') | Some('>'))
            || matches!(next, Some('='));
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

/// Parse doctest examples from Markdown content that uses doctest code fences.
/// Supports both ```sdoctest and ```simple-doctest language hints.
pub fn parse_markdown_doctests(content: &str, source: impl AsRef<Path>) -> Vec<DoctestExample> {
    let mut examples = Vec::new();
    let mut in_block = false;
    let mut block = String::new();
    let mut block_start_line = 0usize;

    for (idx, line) in content.lines().enumerate() {
        let trimmed = line.trim_start();

        // Check for doctest code fence opening with language hint
        if trimmed.starts_with("```sdoctest") || trimmed.starts_with("```simple-doctest") || trimmed.starts_with("```simple") {
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
            for ex in &mut block_examples {
                ex.start_line += block_start_line;
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
            fence_content.push_str(line);
            fence_content.push('\n');
        }
    }

    examples
}

/// Discover doctest examples from a path:
/// - `.sdt`: parsed directly
/// - `.md`: fenced code blocks
/// - `.spl`: """ docstring blocks with ```sdoctest fences
/// - directories: walks recursively for all supported formats
pub fn discover_doctests(path: &Path) -> std::io::Result<Vec<DoctestExample>> {
    let mut examples = Vec::new();

    if path.is_dir() {
        for entry in walkdir::WalkDir::new(path) {
            let entry = entry?;
            if entry.file_type().is_file() {
                let p = entry.path();
                let ext = p.extension().and_then(|s| s.to_str());
                match ext {
                    Some("sdt") => examples.extend(parse_doctest_text(&fs::read_to_string(p)?, p)),
                    Some("md") => examples.extend(parse_markdown_doctests(&fs::read_to_string(p)?, p)),
                    Some("spl") => examples.extend(parse_spl_doctests(&fs::read_to_string(p)?, p)),
                    _ => {}
                }
            }
        }
        return Ok(examples);
    }

    let ext = path.extension().and_then(|s| s.to_str());
    match ext {
        Some("sdt") => examples.extend(parse_doctest_text(&fs::read_to_string(path)?, path)),
        Some("md") => examples.extend(parse_markdown_doctests(&fs::read_to_string(path)?, path)),
        Some("spl") => examples.extend(parse_spl_doctests(&fs::read_to_string(path)?, path)),
        _ => {}
    }

    Ok(examples)
}

/// Run doctest examples and return results.
pub fn run_examples(examples: &[DoctestExample]) -> Vec<DoctestResult> {
    let mut results = Vec::new();
    let mut states: HashMap<PathBuf, EvalState> = HashMap::new();

    for example in examples {
        let state = states
            .entry(example.source.clone())
            .or_insert_with(|| EvalState {
                prelude: String::new(),
                interpreter: Interpreter::new_no_gc(),
            });
        results.push(run_example(example, state));
    }

    results
}

struct EvalState {
    prelude: String,
    interpreter: Interpreter,
}

fn run_example(example: &DoctestExample, state: &mut EvalState) -> DoctestResult {
    let mut outputs: Vec<String> = Vec::new();
    let mut halted = false;

    let config = RunConfig {
        in_memory: true,
        capture_output: true,
        ..Default::default()
    };

    for command in &example.commands {
        let is_def = is_definition_like(command);
        let source = build_source(&state.prelude, command, is_def);

        match state.interpreter.run(&source, config.clone()) {
            Ok(result) => {
                if is_def {
                    append_to_prelude(&mut state.prelude, command, true);
                }

                let stdout = result.stdout.trim_end();
                if !stdout.is_empty() {
                    outputs.push(stdout.to_string());
                } else if !is_def {
                    outputs.push(result.exit_code.to_string());
                }
            }
            Err(err) => {
                outputs.push(format!("Error: {err}"));
                halted = true;
            }
        }
        if halted {
            break;
        }
    }

    let actual = outputs.join("\n");

    let status = match match_matches(&actual, &example.expected) {
        Ok(()) => DoctestStatus::Passed,
        Err(msg) => DoctestStatus::Failed(msg),
    };

    DoctestResult {
        example: example.clone(),
        status,
        actual,
    }
}

pub fn build_source(prelude: &str, snippet: &str, is_def: bool) -> String {
    let mut src = String::new();
    if !prelude.is_empty() {
        src.push_str(prelude);
        if !prelude.ends_with('\n') {
            src.push('\n');
        }
    }

    if is_def {
        src.push_str(snippet);
        src.push('\n');
        if snippet.trim_end().ends_with(':') {
            src.push_str("    0\n");
        }
        // Add trailing newline for control flow statements that may have print side effects
        // (if, while, for, match blocks)
        let first_word = snippet.trim_start().split_whitespace().next().unwrap_or("");
        if matches!(first_word, "if" | "while" | "for" | "match") {
            src.push_str("print \"\\n\"\n");
        }
        src.push_str("main = 0\n");
    } else {
        let trimmed = snippet.trim_start();
        if trimmed.starts_with("print ") || trimmed.starts_with("println ") {
            src.push_str(snippet);
            src.push('\n');
            src.push_str("print \"\\n\"\n");
            src.push_str("main = 0\n");
        } else {
            // Print the expression value directly.
            // The interpreter does not support `let` bindings followed by
            // variable references, so we avoid the intermediate variable
            // pattern and just print the expression result.
            src.push_str("print ");
            src.push_str(snippet);
            src.push('\n');
            src.push_str("print \"\\n\"\n");
            src.push_str("main = 0\n");
        }
    }
    src
}

/// Check if a snippet contains an assignment expression
fn contains_assignment(snippet: &str) -> bool {
    // Simple heuristic: look for '=' that's not part of '==', '!=', '<=', '>='
    let chars: Vec<char> = snippet.chars().collect();
    for i in 0..chars.len() {
        if chars[i] == '=' {
            // Check if it's part of a comparison operator
            let before = if i > 0 { chars[i - 1] } else { ' ' };
            let after = if i + 1 < chars.len() {
                chars[i + 1]
            } else {
                ' '
            };
            if before != '=' && before != '!' && before != '<' && before != '>'
                && after != '='
            {
                return true;
            }
        }
    }
    false
}

/// Check if a snippet is a true definition that should be saved in prelude.
/// Control flow statements (if, while, for, match) should NOT be added to prelude
/// because they execute with side effects and shouldn't be re-run on each subsequent input.
fn is_prelude_definition(snippet: &str) -> bool {
    let trimmed = snippet.trim_start();

    // Check keyword-based definitions
    if let Some(first) = trimmed.split_whitespace().next() {
        // Only add actual definitions, not control flow
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
        ) {
            return true;
        }
    }

    // Check for assignment (e.g., "a = 1") - need to save variable bindings
    contains_assignment(snippet)
}

pub fn append_to_prelude(prelude: &mut String, snippet: &str, is_def: bool) {
    if !is_def {
        return;
    }
    // Only add true definitions to prelude, not control flow statements
    if !is_prelude_definition(snippet) {
        return;
    }
    prelude.push_str(snippet);
    prelude.push('\n');
    if snippet.trim_end().ends_with(':') {
        prelude.push_str("    0\n");
    }
}

fn match_matches(actual: &str, expected: &Expected) -> Result<(), String> {
    match expected {
        Expected::Empty => {
            if actual.trim().is_empty() {
                Ok(())
            } else {
                Err(format!("Expected no output, got: {actual}"))
            }
        }
        Expected::Output(pattern) => {
            if wildcard_match(actual.trim(), pattern.trim()) {
                Ok(())
            } else {
                Err(format!(
                    "Output mismatch:\n  Expected: {pattern}\n  Got: {actual}"
                ))
            }
        }
        Expected::Error(pattern) => {
            if actual.starts_with("Error:") && actual.contains(pattern) {
                Ok(())
            } else {
                Err(format!(
                    "Expected error containing '{pattern}', got: {actual}"
                ))
            }
        }
    }
}

fn wildcard_match(text: &str, pattern: &str) -> bool {
    wildcard_match_impl(text.as_bytes(), pattern.as_bytes(), 0, 0)
}

fn wildcard_match_impl(text: &[u8], pattern: &[u8], ti: usize, pi: usize) -> bool {
    if pi == pattern.len() {
        return ti == text.len();
    }
    if ti == text.len() {
        return pattern[pi..].iter().all(|&b| b == b'*');
    }

    let pc = pattern[pi];
    let tc = text[ti];

    if pc == b'*' {
        wildcard_match_impl(text, pattern, ti, pi + 1)
            || wildcard_match_impl(text, pattern, ti + 1, pi)
    } else if pc == b'.' || pc == tc {
        wildcard_match_impl(text, pattern, ti + 1, pi + 1)
    } else {
        false
    }
}

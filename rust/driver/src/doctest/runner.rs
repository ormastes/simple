use std::collections::HashMap;
use std::path::PathBuf;

use crate::interpreter::{Interpreter, RunConfig};

use crate::doctest::parser::{is_definition_like, is_prelude_definition};
use crate::doctest::types::{DoctestExample, DoctestResult, DoctestStatus, Expected};

/// Run doctest examples and return results.
pub fn run_examples(examples: &[DoctestExample]) -> Vec<DoctestResult> {
    let mut results = Vec::new();
    let mut states: HashMap<PathBuf, EvalState> = HashMap::new();

    for example in examples {
        let state = states.entry(example.source.clone()).or_insert_with(|| EvalState {
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
        if trimmed.starts_with("print ") {
            src.push_str(snippet);
            src.push('\n');
            src.push_str("print \"\\n\"\n");
            src.push_str("main = 0\n");
        } else {
            // Store result and only print value if not nil (like Python REPL)
            // But always print newline to separate outputs
            src.push_str("let __repl_val = ");
            src.push_str(snippet);
            src.push('\n');
            src.push_str("if __repl_val != nil:\n");
            src.push_str("    print __repl_val\n");
            src.push_str("print \"\\n\"\n");
            src.push_str("main = 0\n");
        }
    }
    src
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
                Err(format!("Output mismatch:\n  Expected: {pattern}\n  Got: {actual}"))
            }
        }
        Expected::Error(pattern) => {
            if actual.starts_with("Error:") && actual.contains(pattern) {
                Ok(())
            } else {
                Err(format!("Expected error containing '{pattern}', got: {actual}"))
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
        wildcard_match_impl(text, pattern, ti, pi + 1) || wildcard_match_impl(text, pattern, ti + 1, pi)
    } else if pc == b'.' || pc == tc {
        wildcard_match_impl(text, pattern, ti + 1, pi + 1)
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_source_definition() {
        let src = build_source("", "let x = 5", true);
        assert!(src.contains("let x = 5"));
        assert!(src.contains("main = 0"));
    }

    #[test]
    fn test_build_source_expression() {
        let src = build_source("", "1 + 1", false);
        assert!(src.contains("__repl_val"));
        assert!(src.contains("1 + 1"));
    }

    #[test]
    fn test_append_to_prelude() {
        let mut prelude = String::new();
        append_to_prelude(&mut prelude, "let x = 5", true);
        assert!(prelude.contains("let x = 5"));

        // Control flow should not be added
        let mut prelude2 = String::new();
        append_to_prelude(&mut prelude2, "if x:", true);
        assert!(prelude2.is_empty());
    }

    #[test]
    fn test_wildcard_match() {
        assert!(wildcard_match("hello", "hello"));
        assert!(wildcard_match("hello world", "hello*"));
        assert!(wildcard_match("hello world", "*world"));
        assert!(wildcard_match("hello world", "hello*world"));
        assert!(!wildcard_match("hello", "world"));
    }

    #[test]
    fn test_match_matches() {
        assert!(match_matches("", &Expected::Empty).is_ok());
        assert!(match_matches("hello", &Expected::Output("hello".to_string())).is_ok());
        assert!(match_matches("hello world", &Expected::Output("hello*".to_string())).is_ok());
        assert!(match_matches("Error: test", &Expected::Error("test".to_string())).is_ok());

        assert!(match_matches("hello", &Expected::Empty).is_err());
        assert!(match_matches("hello", &Expected::Output("world".to_string())).is_err());
        assert!(match_matches("hello", &Expected::Error("test".to_string())).is_err());
    }
}

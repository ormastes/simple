//! Interactive REPL (Read-Eval-Print Loop) for the Simple language.

use std::path::PathBuf;

use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

use simple_driver::doctest::{append_to_prelude, build_source, is_definition_like};
use simple_driver::runner::Runner;

/// Check if text has unbalanced brackets/parens/braces.
fn has_unbalanced_brackets(text: &str) -> bool {
    let mut paren = 0i32;
    let mut bracket = 0i32;
    let mut brace = 0i32;
    let mut in_string = false;
    let mut escape_next = false;

    for ch in text.chars() {
        if escape_next {
            escape_next = false;
            continue;
        }
        if ch == '\\' && in_string {
            escape_next = true;
            continue;
        }
        if ch == '"' {
            in_string = !in_string;
            continue;
        }
        if in_string {
            continue;
        }
        match ch {
            '(' => paren += 1,
            ')' => paren -= 1,
            '[' => bracket += 1,
            ']' => bracket -= 1,
            '{' => brace += 1,
            '}' => brace -= 1,
            _ => {}
        }
    }
    paren > 0 || bracket > 0 || brace > 0
}

/// Calculate the current indentation level based on accumulated lines.
/// Returns the expected indentation level for the next line.
fn calculate_indent_level(lines: &[String]) -> usize {
    let mut level = 0usize;
    for line in lines {
        let trimmed = line.trim_end();
        if trimmed.is_empty() {
            continue;
        }
        // Check current line's indentation
        let indent = line.len() - line.trim_start().len();
        let indent_level = indent / 4;

        // Adjust level based on actual indentation (handles dedent)
        if indent_level < level {
            level = indent_level;
        }

        // Lines ending with ':' increase the expected level
        if trimmed.ends_with(':') {
            level += 1;
        }
    }
    level
}

/// Find the indentation level for a matching if/elif/try/match block.
/// Used when we encounter else/elif/except/finally to find the right indentation.
fn find_matching_block_indent(lines: &[String]) -> usize {
    // Stack of (indent_level, is_if_like) for tracking nested blocks
    let mut block_stack: Vec<usize> = Vec::new();

    for line in lines {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }

        let indent = line.len() - line.trim_start().len();
        let indent_level = indent / 4;

        // Pop blocks that are at same or higher indent level (we've dedented past them)
        while let Some(&top) = block_stack.last() {
            if top >= indent_level {
                block_stack.pop();
            } else {
                break;
            }
        }

        // Check if this line starts a block that could have else/elif/except/finally
        let starts_if_block = trimmed.starts_with("if ")
            || trimmed.starts_with("elif ")
            || trimmed.starts_with("try:")
            || trimmed.starts_with("match ");

        if starts_if_block && trimmed.ends_with(':') {
            block_stack.push(indent_level);
        }
    }

    // Return the indent level of the most recent if-like block, or 0
    block_stack.pop().unwrap_or(0)
}

/// Check if accumulated lines need more input (incomplete block or unbalanced brackets).
fn needs_continuation(lines: &[String]) -> bool {
    let full_text = lines.join("\n");

    // Check for unbalanced brackets
    if has_unbalanced_brackets(&full_text) {
        return true;
    }

    // Check if last line ends with ':' (new block starting)
    if let Some(last) = lines.last() {
        if last.trim_end().ends_with(':') {
            return true;
        }
    }

    // Check if we're still inside an indented block
    // (indent level > 0 means block is not complete)
    calculate_indent_level(lines) > 0
}

pub fn run_repl(version: &str, mut runner: Runner) -> i32 {
    println!("Simple Language v{} - Interactive Mode", version);
    println!("Type expressions to evaluate. Use 'exit' or Ctrl-D to quit.");
    println!();

    let mut prelude = String::new();
    let mut rl = match DefaultEditor::new() {
        Ok(editor) => editor,
        Err(e) => {
            eprintln!("Failed to initialize REPL: {}", e);
            return 1;
        }
    };

    let history_path = dirs_next::home_dir()
        .map(|h| h.join(".simple_history"))
        .unwrap_or_else(|| PathBuf::from(".simple_history"));

    let _ = rl.load_history(&history_path);

    // Multi-line input state
    let mut accumulated_lines: Vec<String> = Vec::new();
    let mut in_multiline = false;

    loop {
        // Calculate prompt and auto-indent
        let (prompt, auto_indent) = if in_multiline {
            let level = calculate_indent_level(&accumulated_lines);
            let indent = "    ".repeat(level);
            (format!("... {}", indent), indent)
        } else {
            (">>> ".to_string(), String::new())
        };

        // Helper to execute accumulated input
        let execute_input = |input: &str, prelude: &mut String, runner: &mut Runner| {
            if input.trim().is_empty() {
                return;
            }
            
            let is_def = is_definition_like(input);
            let code = build_source(prelude, input, is_def);

            match runner.run_source_in_memory(&code) {
                Ok(_) => {
                    if is_def {
                        append_to_prelude(prelude, input, true);
                    }
                }
                Err(e) => eprintln!("Error: {}", e),
            }
        };

        match rl.readline(&prompt) {
            Ok(raw_line) => {
                // Handle line with auto-indent prepended for multiline
                let line = if in_multiline && !raw_line.starts_with(' ') && !raw_line.is_empty() {
                    // Check if line starts with dedent keywords (else, elif, except, finally, case)
                    let trimmed_input = raw_line.trim_start();
                    let is_else_like = trimmed_input.starts_with("else:")
                        || trimmed_input.starts_with("else ")
                        || trimmed_input.starts_with("elif ")
                        || trimmed_input.starts_with("except:")
                        || trimmed_input.starts_with("except ")
                        || trimmed_input.starts_with("finally:")
                        || trimmed_input.starts_with("case ");

                    if is_else_like {
                        // Find the matching if/elif/try level by looking for the last
                        // if/elif/try/match at a level less than current
                        let target_indent = find_matching_block_indent(&accumulated_lines);
                        format!("{}{}", "    ".repeat(target_indent), raw_line)
                    } else {
                        // Normal auto-indent
                        format!("{}{}", auto_indent, raw_line)
                    }
                } else {
                    raw_line.clone()
                };

                let trimmed = line.trim();

                // Check for exit commands
                if !in_multiline && (trimmed == "exit" || trimmed == "quit") {
                    break;
                }

                // Handle empty line
                if trimmed.is_empty() {
                    if in_multiline {
                        // Empty line ends multiline input
                        in_multiline = false;
                        let full_input = accumulated_lines.join("\n");
                        accumulated_lines.clear();

                        let _ = rl.add_history_entry(&full_input);
                        execute_input(&full_input, &mut prelude, &mut runner);
                    }
                    // Empty line when not in multiline - just continue
                    continue;
                }

                // Add line to accumulator
                accumulated_lines.push(line.clone());

                // Check if we need more input
                if needs_continuation(&accumulated_lines) {
                    in_multiline = true;
                    continue;
                }

                // Execute the complete input
                in_multiline = false;
                let full_input = accumulated_lines.join("\n");
                accumulated_lines.clear();

                let _ = rl.add_history_entry(&full_input);
                execute_input(&full_input, &mut prelude, &mut runner);
            }
            Err(ReadlineError::Interrupted) => {
                println!("^C");
                // Cancel multiline on Ctrl-C
                accumulated_lines.clear();
                in_multiline = false;
                continue;
            }
            Err(ReadlineError::Eof) => {
                println!();
                break;
            }
            Err(e) => {
                eprintln!("Error: {}", e);
                break;
            }
        }
    }

    let _ = rl.save_history(&history_path);
    0
}

//! Interactive REPL (Read-Eval-Print Loop) for the Simple language.

use std::path::PathBuf;

use rustyline::completion::Completer;
use rustyline::error::ReadlineError;
use rustyline::highlight::Highlighter;
use rustyline::hint::Hinter;
use rustyline::history::DefaultHistory;
use rustyline::validate::{ValidationContext, ValidationResult, Validator};
use rustyline::{Cmd, Config, Editor, EventContext, EventHandler, Helper, KeyEvent};
use rustyline::{Event, RepeatCount};
use rustyline::{KeyCode, Modifiers};

use simple_driver::doctest::{append_to_prelude, build_source, is_definition_like};
use simple_driver::runner::Runner;

/// Helper for REPL that handles smart indentation deletion
#[derive(Clone)]
struct ReplHelper;

impl Completer for ReplHelper {
    type Candidate = String;
}

impl Hinter for ReplHelper {
    type Hint = String;
}

impl Highlighter for ReplHelper {}

impl Validator for ReplHelper {
    fn validate(&self, _ctx: &mut ValidationContext) -> Result<ValidationResult, ReadlineError> {
        Ok(ValidationResult::Valid(None))
    }
}

impl Helper for ReplHelper {}

/// Tab handler that inserts 4 spaces for indentation
struct TabHandler;

impl rustyline::ConditionalEventHandler for TabHandler {
    fn handle(&self, _evt: &Event, _n: RepeatCount, _: bool, ctx: &EventContext) -> Option<Cmd> {
        if std::env::var("REPL_DEBUG").is_ok() {
            eprintln!("[REPL_DEBUG] Tab pressed");
            eprintln!("[REPL_DEBUG]   line: '{}'", ctx.line());
            eprintln!("[REPL_DEBUG]   pos: {}", ctx.pos());
            eprintln!("[REPL_DEBUG]   Action: Insert 4 spaces");
        }
        // Insert 4 spaces
        Some(Cmd::Insert(1, "    ".to_string()))
    }
}

/// Backspace handler for REPL
///
/// LIMITATION: Due to rustyline's architecture, we cannot make backspace delete
/// multiple characters (e.g., a full indent level of 4 spaces) in a single keypress.
///
/// The issue: rustyline's command execution overrides Movement::BackwardChar(n) repeat
/// counts with the event's repeat count (always 1 for single backspace press).
///
/// See doc/research/REPL_BACKSPACE_LIMITATION.md for full details.
///
/// WORKAROUND: Users should use Ctrl+U to delete full indents (4 spaces at once).
/// Regular backspace deletes one character at a time (standard behavior).
struct PythonBackspaceHandler;

impl rustyline::ConditionalEventHandler for PythonBackspaceHandler {
    fn handle(&self, _evt: &Event, n: RepeatCount, _: bool, ctx: &EventContext) -> Option<Cmd> {
        if std::env::var("REPL_DEBUG").is_ok() {
            eprintln!("[REPL_DEBUG] Backspace pressed (repeat: {})", n);
            eprintln!("[REPL_DEBUG]   line: '{}'", ctx.line());
            eprintln!("[REPL_DEBUG]   pos: {}", ctx.pos());

            // Check if in leading whitespace
            let line = ctx.line();
            let pos = ctx.pos();
            if pos > 0 && pos <= line.len() {
                let before_cursor = &line[..pos];
                let is_all_spaces = before_cursor.chars().all(|c| c == ' ');
                eprintln!("[REPL_DEBUG]   before_cursor: '{}'", before_cursor);
                eprintln!("[REPL_DEBUG]   all_spaces: {}", is_all_spaces);
            }
            eprintln!("[REPL_DEBUG]   Action: Default (delete 1 char) - rustyline limitation");
        }
        // Return None to use default backspace behavior (delete one character)
        // For full indent deletion, users should press Ctrl+U
        None
    }
}

/// Ctrl+U handler that deletes 4 spaces (dedent)
struct DedentHandler;

impl rustyline::ConditionalEventHandler for DedentHandler {
    fn handle(&self, _evt: &Event, _n: RepeatCount, _: bool, ctx: &EventContext) -> Option<Cmd> {
        let line = ctx.line();
        let pos = ctx.pos();

        if std::env::var("REPL_DEBUG").is_ok() {
            eprintln!("[REPL_DEBUG] Ctrl+U pressed");
            eprintln!("[REPL_DEBUG]   line: '{}'", line);
            eprintln!("[REPL_DEBUG]   pos: {}", pos);
        }

        // Check if we can delete 4 spaces before cursor
        if pos >= 4 && line[pos - 4..pos] == *"    " {
            if std::env::var("REPL_DEBUG").is_ok() {
                eprintln!("[REPL_DEBUG]   Action: Delete 4 spaces");
            }
            // Delete 4 spaces
            Some(Cmd::Kill(rustyline::Movement::BackwardChar(4)))
        } else if pos > 0 {
            // Delete what we can (less than 4 spaces)
            let spaces_before = line[..pos].chars().rev().take_while(|&c| c == ' ').count();
            if spaces_before > 0 {
                if std::env::var("REPL_DEBUG").is_ok() {
                    eprintln!("[REPL_DEBUG]   Action: Delete {} spaces", spaces_before);
                }
                Some(Cmd::Kill(rustyline::Movement::BackwardChar(
                    spaces_before.min(pos),
                )))
            } else {
                if std::env::var("REPL_DEBUG").is_ok() {
                    eprintln!("[REPL_DEBUG]   Action: No spaces to delete");
                }
                None // Do nothing if no spaces before cursor
            }
        } else {
            if std::env::var("REPL_DEBUG").is_ok() {
                eprintln!("[REPL_DEBUG]   Action: At start of line");
            }
            None
        }
    }
}

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
    let config = Config::builder()
        .auto_add_history(false) // We'll add history manually
        .edit_mode(rustyline::EditMode::Emacs) // Ensure we're in a mode that supports bindings
        .build();
    let mut rl: Editor<ReplHelper, DefaultHistory> = match Editor::with_config(config) {
        Ok(mut editor) => {
            editor.set_helper(Some(ReplHelper));

            // Bind Tab to insert 4 spaces (indentation)
            editor.bind_sequence(
                KeyEvent::from('\t'), // Tab key
                EventHandler::Conditional(Box::new(TabHandler)),
            );

            // Bind Ctrl+U to dedent (delete 4 spaces)
            editor.bind_sequence(
                KeyEvent::ctrl('u'), // Ctrl+U for dedent (Unindent)
                EventHandler::Conditional(Box::new(DedentHandler)),
            );

            // Bind backspace to Python-style behavior
            // Delete whole indent if line is only spaces, else delete one char
            // Try multiple backspace representations
            editor.bind_sequence(
                KeyEvent(KeyCode::Backspace, rustyline::Modifiers::NONE),
                EventHandler::Conditional(Box::new(PythonBackspaceHandler)),
            );
            editor.bind_sequence(
                KeyEvent(KeyCode::Delete, rustyline::Modifiers::NONE),
                EventHandler::Conditional(Box::new(PythonBackspaceHandler)),
            );

            editor
        }
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
            ("... ".to_string(), indent)
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

        // Read line with pre-filled indentation for multiline mode
        let readline_result = if in_multiline && !auto_indent.is_empty() {
            rl.readline_with_initial(&prompt, (&auto_indent, ""))
        } else {
            rl.readline(&prompt)
        };

        match readline_result {
            Ok(line) => {
                if std::env::var("REPL_DEBUG").is_ok() {
                    eprintln!("[REPL_DEBUG] Line accepted: '{}'", line);
                    eprintln!("[REPL_DEBUG]   in_multiline: {}", in_multiline);
                    eprintln!("[REPL_DEBUG]   accumulated_lines: {:?}", accumulated_lines);
                }

                let trimmed = line.trim();

                // Check for exit commands
                if !in_multiline && (trimmed == "exit" || trimmed == "quit") {
                    break;
                }

                // Handle empty line
                if trimmed.is_empty() {
                    if in_multiline {
                        if std::env::var("REPL_DEBUG").is_ok() {
                            eprintln!("[REPL_DEBUG] Empty line in multiline - executing accumulated input");
                        }
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

                if std::env::var("REPL_DEBUG").is_ok() {
                    eprintln!("[REPL_DEBUG] Added to accumulator: {:?}", accumulated_lines);
                }

                // Check if we need more input
                if needs_continuation(&accumulated_lines) {
                    if std::env::var("REPL_DEBUG").is_ok() {
                        eprintln!(
                            "[REPL_DEBUG] Needs continuation - entering/staying in multiline mode"
                        );
                    }
                    in_multiline = true;
                    continue;
                }

                // Execute the complete input
                if std::env::var("REPL_DEBUG").is_ok() {
                    eprintln!("[REPL_DEBUG] Input complete - executing");
                }
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

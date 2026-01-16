//! TUI-based REPL using crossterm
//!
//! This REPL provides:
//! - Smart backspace: deletes full indent (4 spaces) when in leading whitespace
//! - Full terminal control via crossterm (raw mode, cursor positioning, colors)
//! - Direct keyboard event handling (no abstraction layer)
//! - Efficient rendering with queue!() and execute!() macros

use super::editor::{EditorResult, LineEditor};
use super::keybindings::KeyBindings;
use crossterm::{
    cursor,
    event::{self, Event},
    execute, queue,
    style::{Color, Print, ResetColor, SetForegroundColor},
    terminal::{self, Clear, ClearType},
};
use simple_driver::doctest::{append_to_prelude, build_source, is_definition_like};
use simple_driver::runner::Runner;
use std::io::{self, Write};

/// Run the TUI-based REPL
pub fn run_tui_repl(version: &str, mut runner: Runner) -> i32 {
    // Setup terminal
    if let Err(e) = setup_terminal() {
        eprintln!("Failed to setup terminal: {}", e);
        return 1;
    }

    // Check for debug mode
    let debug_mode = std::env::var("TUI_DEBUG").is_ok();

    // Show startup message (use \r\n for raw mode)
    print!("Simple Language v{} - Interactive Mode (TUI)\r\n", version);
    print!("Using TUI mode with smart indentation:\r\n");
    print!("  - Tab: Insert 4 spaces\r\n");
    print!("  - Backspace: Delete indent (4 spaces) or 1 character\r\n");
    print!("  - Ctrl+U: Delete indent or to start of line\r\n");
    print!("  - Ctrl+C: Cancel input\r\n");
    print!("  - Ctrl+D: Exit\r\n");
    if debug_mode {
        print!("  [DEBUG MODE ENABLED]\r\n");
    }
    print!("\r\n");
    io::stdout().flush().ok();

    let mut editor = LineEditor::new();
    editor.set_debug_mode(debug_mode);
    let keybindings = KeyBindings::new();
    let mut prelude = String::new();

    // Track previous line count to detect when we just entered multiline mode
    let mut prev_line_count = 0;

    let exit_code = loop {
        // Render prompt
        let prompt = if editor.is_multiline() { "... " } else { ">>> " };

        if let Err(e) = render_prompt(prompt, &editor) {
            eprintln!("Render error: {}", e);
            break 1;
        }

        // Wait for key event
        match event::read() {
            Ok(Event::Key(key_event)) => {
                // Get action from keybindings
                let action = keybindings.get_action(key_event);

                // Apply action to editor
                match editor.apply_action(action) {
                    EditorResult::Continue => {
                        // Check if we JUST entered multiline mode (line count increased)
                        let current_line_count = editor.lines().len();
                        if editor.is_multiline() && current_line_count > prev_line_count {
                            // Show the line that was just completed before switching to ... prompt
                            let last_line = editor.lines().last().map(|s| s.as_str()).unwrap_or("");
                            let mut stdout = io::stdout();
                            queue!(stdout, cursor::MoveToColumn(0), Clear(ClearType::CurrentLine)).ok();

                            // Use correct prompt: ">>>" for first line, "..." for continuation
                            let line_prompt = if current_line_count == 1 { ">>> " } else { "... " };
                            queue!(stdout, SetForegroundColor(Color::Green), Print(line_prompt), ResetColor).ok();
                            queue!(stdout, Print(last_line), Print("\r\n")).ok();
                            stdout.flush().ok();
                            // Update prev_line_count
                            prev_line_count = current_line_count;
                            // Prompt will be updated to "... " on next loop iteration
                        }
                    }
                    EditorResult::Accepted(input) => {
                        // Show the final line before moving to next line
                        let last_line = input.lines().last().unwrap_or("");
                        let mut stdout = io::stdout();
                        queue!(stdout, cursor::MoveToColumn(0), Clear(ClearType::CurrentLine)).ok();

                        // Determine which prompt to show
                        let line_prompt = if input.lines().count() > 1 { "... " } else { ">>> " };
                        queue!(stdout, SetForegroundColor(Color::Green), Print(line_prompt), ResetColor).ok();
                        queue!(stdout, Print(last_line), Print("\r\n")).ok();
                        stdout.flush().ok();

                        // Disable raw mode temporarily for output
                        terminal::disable_raw_mode().ok();

                        // Execute input
                        if !input.trim().is_empty() {
                            execute_input(&input, &mut prelude, &mut runner);
                        }

                        // Re-enable raw mode
                        terminal::enable_raw_mode().ok();

                        // Reset line count (exited multiline mode)
                        prev_line_count = 0;
                    }
                    EditorResult::Cancelled => {
                        let mut stdout = io::stdout();
                        queue!(stdout, cursor::MoveToColumn(0), Print("^C\r\n")).ok();
                        stdout.flush().ok();
                        // Editor already reset
                        // Reset line count (cancelled multiline mode)
                        prev_line_count = 0;
                    }
                    EditorResult::Exit => {
                        let mut stdout = io::stdout();
                        queue!(stdout, Print("\r\n")).ok();
                        stdout.flush().ok();
                        break 0;
                    }
                }
            }
            Ok(_) => {
                // Ignore other events (mouse, resize, etc.)
            }
            Err(e) => {
                eprintln!("Event read error: {}", e);
                break 1;
            }
        }
    };

    // Cleanup terminal
    if let Err(e) = cleanup_terminal() {
        eprintln!("Failed to cleanup terminal: {}", e);
    }

    exit_code
}

/// Setup terminal for TUI mode
fn setup_terminal() -> io::Result<()> {
    terminal::enable_raw_mode()?;
    execute!(io::stdout(), cursor::Show)?;
    Ok(())
}

/// Cleanup terminal after TUI mode
fn cleanup_terminal() -> io::Result<()> {
    terminal::disable_raw_mode()?;
    execute!(io::stdout(), cursor::Show)?;
    Ok(())
}

/// Identity function - just return the string as-is (spaces remain spaces)
fn make_indent_visible(s: &str) -> &str {
    s
}

/// Render the prompt and current editor state
fn render_prompt(prompt: &str, editor: &LineEditor) -> io::Result<()> {
    let mut stdout = io::stdout();

    // Debug: log rendering
    if std::env::var("TUI_DEBUG").is_ok() {
        eprintln!(
            "[DEBUG] RENDER: Clearing line, redrawing prompt + buffer '{}'",
            editor.buffer()
        );
    }

    // Move to start of line and clear
    queue!(stdout, cursor::MoveToColumn(0), Clear(ClearType::CurrentLine))?;

    // Print prompt
    queue!(stdout, SetForegroundColor(Color::Green), Print(prompt), ResetColor)?;

    // Print buffer (spaces remain as spaces)
    queue!(stdout, Print(editor.buffer()))?;

    // Move cursor to correct position
    let cursor_col = prompt.len() as u16 + editor.cursor() as u16;
    queue!(stdout, cursor::MoveToColumn(cursor_col))?;

    if std::env::var("TUI_DEBUG").is_ok() {
        eprintln!("[DEBUG] RENDER: Complete, cursor at column {}", cursor_col);
    }

    stdout.flush()?;
    Ok(())
}

/// Execute input in the interpreter
fn execute_input(input: &str, prelude: &mut String, runner: &mut Runner) {
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
}

//! TUI REPL Indentation Bug Reproduction Test
//!
//! This test reproduces two bugs:
//! 1. TUI does not add automatic indentation after ':'
//! 2. When typing in indented area, it rewrites previous line instead of current line

use portable_pty::{native_pty_system, CommandBuilder, PtySize};
use std::io::{Read, Write};
use std::path::PathBuf;
use std::thread;
use std::time::Duration;

/// Helper to manage PTY session
struct PtySession {
    reader: Box<dyn Read + Send>,
    writer: Box<dyn Write + Send>,
}

impl PtySession {
    fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let binary = PathBuf::from(env!("CARGO_BIN_EXE_simple"));
        let pty_system = native_pty_system();
        let pair = pty_system.openpty(PtySize {
            rows: 24,
            cols: 80,
            pixel_width: 0,
            pixel_height: 0,
        })?;

        let mut cmd = CommandBuilder::new(&binary);
        cmd.arg("--tui");
        cmd.env("TERM", "xterm-256color");
        cmd.env("TUI_DEBUG", "1"); // Enable debug logging

        let _child = pair.slave.spawn_command(cmd)?;
        drop(pair.slave);

        let reader = pair.master.try_clone_reader()?;
        let writer = pair.master.take_writer()?;

        Ok(Self { reader, writer })
    }

    fn send_text(&mut self, text: &str) -> Result<(), Box<dyn std::error::Error>> {
        self.writer.write_all(text.as_bytes())?;
        self.writer.flush()?;
        thread::sleep(Duration::from_millis(50));
        Ok(())
    }

    fn send_enter(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.writer.write_all(b"\r")?;
        self.writer.flush()?;
        thread::sleep(Duration::from_millis(100));
        Ok(())
    }

    fn send_ctrl_d(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.writer.write_all(&[4])?; // Ctrl+D
        self.writer.flush()?;
        thread::sleep(Duration::from_millis(100));
        Ok(())
    }

    fn read_output(&mut self, timeout_ms: u64) -> Result<String, Box<dyn std::error::Error>> {
        let mut output = Vec::new();
        let mut buf = [0u8; 4096];
        let deadline = std::time::Instant::now() + Duration::from_millis(timeout_ms);

        while std::time::Instant::now() < deadline {
            thread::sleep(Duration::from_millis(10));
            match self.reader.read(&mut buf) {
                Ok(0) => break,
                Ok(n) => output.extend_from_slice(&buf[..n]),
                Err(e) if e.kind() == std::io::ErrorKind::WouldBlock => continue,
                Err(e) => return Err(Box::new(e)),
            }
        }

        Ok(String::from_utf8_lossy(&output).to_string())
    }

    fn wait_for_prompt(&mut self, timeout_ms: u64) -> Result<(), Box<dyn std::error::Error>> {
        let output = self.read_output(timeout_ms)?;
        if !output.contains(">>>") && !output.contains("...") {
            return Err("Timeout waiting for prompt".into());
        }
        Ok(())
    }
}

#[test]
#[cfg(feature = "tui")]
fn test_tui_indentation_bug_reproduction() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== Reproducing TUI Indentation Bugs ===\n");

    let mut session = PtySession::new()?;
    session.wait_for_prompt(2000)?;

    println!("Step 1: Type 'if x > 0:' + Enter");
    session.send_text("if x > 0:")?;
    session.send_enter()?;
    let output1 = session.read_output(300)?;

    println!("Output after first Enter:");
    println!("{}", output1);
    println!();

    // BUG 1: Check if auto-indentation is present
    if output1.contains("...     ") {
        println!("✅ Auto-indentation IS present (4 spaces after '...')");
    } else {
        println!("❌ BUG 1 REPRODUCED: Auto-indentation MISSING after ':'");
        println!("   Expected: '...     ' (with 4 spaces)");
        println!("   Got: '... ' (no auto-indent)");
    }
    println!();

    println!("Step 2: Type 'print' (should appear on CURRENT line with indent)");
    session.send_text("p")?;
    let output2 = session.read_output(200)?;

    println!("Output after typing 'p':");
    println!("{}", output2);
    println!();

    session.send_text("rint")?;
    let output3 = session.read_output(200)?;

    println!("Output after typing 'rint':");
    println!("{}", output3);
    println!();

    // BUG 2: Check if text appears on correct line
    if output3.contains("... print") || output3.contains("...     print") {
        println!("✅ Text appears on CURRENT line (correct)");
    } else if output3.contains("if x > 0:print") || output3.contains("if x > 0: print") {
        println!("❌ BUG 2 REPRODUCED: Text appears on PREVIOUS line instead of current line");
        println!("   Expected: '... print' (on current line)");
        println!("   Got: Text merged with previous line");
    } else {
        println!("⚠️  UNKNOWN STATE: Cannot determine where text appeared");
        println!(
            "   Output: {}",
            output3.lines().take(5).collect::<Vec<_>>().join("\n")
        );
    }
    println!();

    session.send_ctrl_d()?;

    println!("=== Bug Reproduction Complete ===");
    println!("\nExpected behavior:");
    println!("1. After 'if x > 0:' + Enter, should show '...     ' (4 spaces auto-indent)");
    println!("2. Typing 'print' should show '...     print' (text on CURRENT line)");
    println!("\nActual behavior:");
    println!("1. Shows '... ' (no auto-indent)");
    println!("2. Text may appear on wrong line or be invisible");

    Ok(())
}

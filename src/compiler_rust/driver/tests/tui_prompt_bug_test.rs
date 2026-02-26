//! Test to reproduce TUI prompt bug: "..." changes to ">>>" after second if statement

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
        // Find the binary in target directory
        let binary = std::env::var("CARGO_BIN_EXE_simple")
            .map(PathBuf::from)
            .unwrap_or_else(|_| {
                // Fallback: look in target/debug
                let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
                PathBuf::from(manifest_dir).join("../../../target/debug/simple")
            });
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
fn test_tui_prompt_bug_two_if_statements() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== BUG REPRODUCTION: Prompt changes from ... to >>> after second if ===\n");

    let mut session = PtySession::new()?;
    session.wait_for_prompt(2000)?;

    // Step 1: Type "if 1:" + Enter
    println!("Step 1: Type 'if 1:' + Enter");
    session.send_text("if 1:")?;
    session.send_enter()?;
    let output1 = session.read_output(300)?;

    println!("Output after first if:");
    println!("{}", output1);
    println!();

    // Check for "..." prompt (should be in multiline mode)
    if output1.contains("...") {
        println!("✅ First prompt is '...' (correct - in multiline mode)");
    } else if output1.contains(">>>") {
        println!("❌ BUG: First prompt is '>>>' (should be '...')");
    }
    println!();

    // Step 2: Type "    if 1:" + Enter
    println!("Step 2: Type '    if 1:' + Enter");
    session.send_text("    if 1:")?;
    session.send_enter()?;
    let output2 = session.read_output(300)?;

    println!("Output after second if:");
    println!("{}", output2);
    println!();

    // Check for "..." prompt (should STILL be in multiline mode)
    let lines: Vec<&str> = output2.lines().collect();
    let last_few_lines = lines.iter().rev().take(5).rev().collect::<Vec<_>>();

    println!("Last few lines:");
    for line in &last_few_lines {
        println!("  {}", line);
    }
    println!();

    // Look for the prompt in the output
    let has_continuation_prompt = output2.contains("...");
    let has_main_prompt = output2.contains(">>>");

    if has_continuation_prompt && !has_main_prompt {
        println!("✅ PASS: Prompt is still '...' (correct)");
    } else if has_main_prompt {
        println!("❌ BUG REPRODUCED: Prompt changed to '>>>' after second if statement!");
        println!("   Expected: '...' (continuation prompt)");
        println!("   Got: '>>>' (main prompt)");
        println!();
        println!("   This indicates multiline mode was incorrectly exited or");
        println!("   the line count tracking caused incorrect prompt rendering.");
    } else {
        println!("⚠️  UNKNOWN: Could not determine prompt state");
    }

    session.send_ctrl_d()?;

    println!("\n=== Bug Reproduction Complete ===");

    Ok(())
}

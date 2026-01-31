//! Bug reproduction test for rustyline REPL backspace limitation
//!
//! This test demonstrates the documented limitation where rustyline's
//! Movement::BackwardChar(n) with n>1 gets overridden to n=1 by
//! movement.redo(event_repeat_count).
//!
//! Expected behavior: Backspace should delete 4 spaces when in leading whitespace
//! Actual behavior: Backspace only deletes 1 space (rustyline limitation)

use portable_pty::{native_pty_system, CommandBuilder, PtySize};
use std::io::{Read, Write};
use std::path::PathBuf;
use std::thread;
use std::time::Duration;

/// Helper to interact with PTY
struct PtySession {
    reader: Box<dyn Read + Send>,
    writer: Box<dyn Write + Send>,
}

impl PtySession {
    fn new(use_tui: bool) -> Result<Self, Box<dyn std::error::Error>> {
        // Find the binary in target directory
        let binary = std::env::var("CARGO_BIN_EXE_simple_old")
            .map(PathBuf::from)
            .unwrap_or_else(|_| {
                let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
                PathBuf::from(manifest_dir).join("../../../target/debug/simple_old")
            });
        if !binary.exists() {
            return Err(format!("Binary not found at {:?}", binary).into());
        }

        let pty_system = native_pty_system();
        let pair = pty_system.openpty(PtySize {
            rows: 24,
            cols: 80,
            pixel_width: 0,
            pixel_height: 0,
        })?;

        let mut cmd = CommandBuilder::new(&binary);
        if use_tui {
            cmd.arg("--tui");
        }
        cmd.env("TERM", "xterm-256color");

        let _child = pair.slave.spawn_command(cmd)?;
        drop(pair.slave);

        let reader = pair.master.try_clone_reader()?;
        let writer = pair.master.take_writer()?;

        Ok(Self { reader, writer })
    }

    fn wait_for_prompt(&mut self, timeout_ms: u64) -> Result<String, Box<dyn std::error::Error>> {
        thread::sleep(Duration::from_millis(timeout_ms));
        let mut buf = [0u8; 8192];
        match self.reader.read(&mut buf) {
            Ok(n) if n > 0 => Ok(String::from_utf8_lossy(&buf[..n]).to_string()),
            Ok(_) => Ok(String::new()),
            Err(e) => Err(e.into()),
        }
    }

    fn send_key(&mut self, key: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
        self.writer.write_all(key)?;
        self.writer.flush()?;
        Ok(())
    }

    fn send_tab(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.send_key(b"\t")
    }

    fn send_backspace(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.send_key(b"\x7f")
    }

    fn send_ctrl_d(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.send_key(b"\x04")
    }

    fn read_output(&mut self, wait_ms: u64) -> Result<String, Box<dyn std::error::Error>> {
        thread::sleep(Duration::from_millis(wait_ms));
        let mut buf = [0u8; 8192];
        match self.reader.read(&mut buf) {
            Ok(n) if n > 0 => Ok(String::from_utf8_lossy(&buf[..n]).to_string()),
            Ok(_) => Ok(String::new()),
            Err(e) => Err(e.into()),
        }
    }
}

#[test]
fn test_rustyline_backspace_bug_reproduction() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n╔════════════════════════════════════════════════════════╗");
    println!("║  BUG REPRODUCTION: rustyline Backspace Limitation     ║");
    println!("╚════════════════════════════════════════════════════════╝\n");

    let mut session = PtySession::new(false)?; // false = default rustyline REPL

    // Wait for REPL to start
    println!("Waiting for REPL startup...");
    let startup = session.wait_for_prompt(1000)?;
    println!("Startup output received");

    // Test: Tab inserts 4 spaces
    println!("\n=== Step 1: Press Tab (expect 4 spaces inserted) ===");
    session.send_tab()?;
    let after_tab = session.read_output(200)?;
    println!("After Tab: {}", after_tab.escape_debug());

    // Test: Backspace should delete 4 spaces, but only deletes 1 (BUG)
    println!("\n=== Step 2: Press Backspace (expect 4 spaces deleted) ===");
    session.send_backspace()?;
    let after_backspace = session.read_output(200)?;
    println!("After Backspace: {}", after_backspace.escape_debug());

    // Analyze the result
    println!("\n=== Analysis ===");

    // Check if the prompt still has spaces (indicating the bug)
    if after_backspace.contains("   ") || after_backspace.contains("\t") {
        println!("❌ BUG CONFIRMED: Backspace only deleted 1 space");
        println!("   Expected: All 4 spaces deleted");
        println!("   Actual: 3 spaces remain (rustyline limitation)");
        println!("\n   Root cause: rustyline's Movement::BackwardChar(4)");
        println!("               gets overridden to BackwardChar(1) by");
        println!("               movement.redo(event_repeat_count)");
        println!("\n   Solution: Use TUI REPL with --tui flag");
    } else if after_backspace.contains(">>> ") && !after_backspace.contains("    ") {
        println!("✅ UNEXPECTED: Backspace deleted indent correctly");
        println!("   This suggests rustyline behavior may have changed");
        println!("   or custom key handler is working");
    } else {
        println!("⚠️  UNCLEAR: Could not determine backspace behavior");
        println!("   Output: {}", after_backspace);
    }

    // Press backspace 3 more times to fully clear (workaround)
    println!("\n=== Step 3: Press Backspace 3 more times (workaround) ===");
    for i in 1..=3 {
        session.send_backspace()?;
        let output = session.read_output(100)?;
        println!("After backspace #{}: {}", i, output.escape_debug());
    }

    // Exit REPL
    println!("\n=== Exiting REPL ===");
    session.send_ctrl_d()?;
    thread::sleep(Duration::from_millis(500));

    println!("\n╔════════════════════════════════════════════════════════╗");
    println!("║  CONCLUSION                                            ║");
    println!("╠════════════════════════════════════════════════════════╣");
    println!("║  This bug is a known rustyline architectural          ║");
    println!("║  limitation documented in:                            ║");
    println!("║  doc/research/REPL_BACKSPACE_LIMITATION.md            ║");
    println!("║                                                        ║");
    println!("║  Workaround: Use TUI REPL with --tui flag             ║");
    println!("║  Command: ./target/release/simple --tui               ║");
    println!("╚════════════════════════════════════════════════════════╝\n");

    Ok(())
}

#[test]
fn test_rustyline_tab_behavior() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== Testing rustyline Tab Behavior ===\n");

    let mut session = PtySession::new(false)?;
    session.wait_for_prompt(1000)?;

    // Test that Tab inserts 4 spaces
    println!("Pressing Tab...");
    session.send_tab()?;
    let output = session.read_output(200)?;

    println!("Output after Tab:");
    println!("  Raw: {:?}", output.as_bytes());
    println!("  Display: {}", output.escape_debug());

    // Check if 4 spaces were inserted
    if output.contains("    ") || output.chars().filter(|&c| c == ' ').count() >= 4 {
        println!("✅ Tab correctly inserts 4 spaces");
    } else {
        println!("❌ Tab did not insert 4 spaces");
        println!("   This may indicate a different tab behavior");
    }

    session.send_ctrl_d()?;
    Ok(())
}

#[test]
fn test_rustyline_multiple_tabs_and_backspaces() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== Testing Multiple Tabs + Backspaces ===\n");

    let mut session = PtySession::new(false)?;
    session.wait_for_prompt(1000)?;

    // Press Tab twice (8 spaces total)
    println!("Pressing Tab twice (expect 8 spaces)...");
    session.send_tab()?;
    session.read_output(100)?;
    session.send_tab()?;
    let after_tabs = session.read_output(200)?;
    println!("After 2 Tabs: {}", after_tabs.escape_debug());

    // Press Backspace once (should delete 4, but only deletes 1)
    println!("\nPressing Backspace once (expect 4 spaces deleted)...");
    session.send_backspace()?;
    let after_backspace = session.read_output(200)?;
    println!("After 1 Backspace: {}", after_backspace.escape_debug());

    // Analyze: should have 4 spaces left (if bug exists)
    let space_count = after_backspace.chars().filter(|&c| c == ' ').count();
    println!("\nAnalysis:");
    println!("  Spaces remaining: ~{}", space_count);
    if space_count >= 7 {
        println!("  ❌ BUG: Only 1 space deleted (7 remain)");
    } else if space_count >= 4 {
        println!("  ✅ Partial: ~4 spaces deleted");
    } else {
        println!("  ⚠️  Unexpected behavior");
    }

    session.send_ctrl_d()?;
    Ok(())
}

#[test]
fn test_rustyline_backspace_after_text() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n=== Testing Backspace After Text ===\n");

    let mut session = PtySession::new(false)?;
    session.wait_for_prompt(1000)?;

    // Tab + text
    println!("Pressing Tab + typing 'hello'...");
    session.send_tab()?;
    session.read_output(100)?;
    session.send_key(b"hello")?;
    let after_text = session.read_output(200)?;
    println!("After Tab + 'hello': {}", after_text.escape_debug());

    // Backspace should delete only 'o' (normal behavior)
    println!("\nPressing Backspace (should delete only 'o')...");
    session.send_backspace()?;
    let after_backspace = session.read_output(200)?;
    println!("After Backspace: {}", after_backspace.escape_debug());

    if after_backspace.contains("hell") && !after_backspace.contains("hello") {
        println!("✅ Backspace correctly deleted only 1 character after text");
    } else {
        println!("❌ Unexpected backspace behavior after text");
    }

    session.send_ctrl_d()?;
    Ok(())
}

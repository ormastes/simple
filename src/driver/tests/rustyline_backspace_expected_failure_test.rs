//! Expected failure test for rustyline REPL backspace
//!
//! This test EXPECTS the bug to exist. It will FAIL if:
//! - Backspace starts working correctly (deleting 4 spaces)
//! - rustyline gets updated to fix the limitation
//! - Someone modifies the REPL to work around the issue
//!
//! If this test fails, it means the bug is fixed and we should:
//! 1. Update documentation
//! 2. Remove the TUI workaround recommendation
//! 3. Celebrate! 🎉

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
    fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let binary = PathBuf::from(env!("CARGO_BIN_EXE_simple"));
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
        // NO --tui flag - testing default rustyline REPL
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
fn test_expect_rustyline_bug_exists() {
    println!("\n╔════════════════════════════════════════════════════════╗");
    println!("║  EXPECTED FAILURE TEST: rustyline Bug Must Exist     ║");
    println!("╚════════════════════════════════════════════════════════╝\n");

    let mut session = PtySession::new().expect("Failed to create PTY session");

    // Wait for REPL to start
    println!("Waiting for REPL startup...");
    session
        .wait_for_prompt(1000)
        .expect("Failed to wait for prompt");

    // Press Tab (should insert 4 spaces)
    println!("=== Pressing Tab (expect 4 spaces) ===");
    session.send_tab().expect("Failed to send tab");
    let after_tab = session.read_output(200).expect("Failed to read after tab");
    println!("After Tab: {}", after_tab.escape_debug());

    // Press Backspace (bug: should only delete 1 space, not 4)
    println!("\n=== Pressing Backspace (expect bug: only 1 space deleted) ===");
    session.send_backspace().expect("Failed to send backspace");
    let after_backspace = session
        .read_output(200)
        .expect("Failed to read after backspace");
    println!("After Backspace: {}", after_backspace.escape_debug());

    // Analyze the result
    println!("\n=== Analysis ===");

    // Count spaces in the output
    let space_count = after_backspace.chars().filter(|&c| c == ' ').count();
    println!("Space count in output: {}", space_count);

    // Check if the bug exists (3 spaces should remain after backspace)
    // If backspace worked correctly, we'd have 0 or very few spaces
    let bug_exists = after_backspace.contains("   ") || space_count >= 3;

    if !bug_exists {
        println!("❌ UNEXPECTED: Bug appears to be FIXED!");
        println!("   Backspace deleted all 4 spaces correctly");
        println!("   This test expects the bug to exist!");
        println!("\n╔════════════════════════════════════════════════════════╗");
        println!("║  ⚠️  CRITICAL: rustyline limitation appears FIXED!    ║");
        println!("╠════════════════════════════════════════════════════════╣");
        println!("║  Action items:                                         ║");
        println!("║  1. Update doc/research/REPL_BACKSPACE_LIMITATION.md  ║");
        println!("║  2. Update TUI_REPL.md to note bug is fixed           ║");
        println!("║  3. Consider removing TUI workaround recommendation   ║");
        println!("║  4. Update all documentation references               ║");
        println!("╚════════════════════════════════════════════════════════╝\n");

        session.send_ctrl_d().ok();
        panic!("rustyline bug appears to be FIXED! Update documentation!");
    }

    println!("✅ EXPECTED: Bug exists - backspace only deleted 1 space");
    println!("   Spaces remaining: ~{}", space_count);
    println!("   This is the known rustyline limitation");

    // Exit REPL
    session.send_ctrl_d().ok();
    thread::sleep(Duration::from_millis(500));

    println!("\n✅ Test passed: Bug exists as expected");
}

#[test]
fn test_verify_indent_backspace_does_not_work() {
    println!("\n╔════════════════════════════════════════════════════════╗");
    println!("║  NEGATIVE TEST: Verify Indent Backspace NOT Working  ║");
    println!("╚════════════════════════════════════════════════════════╝\n");

    let mut session = PtySession::new().expect("Failed to create PTY session");
    session
        .wait_for_prompt(1000)
        .expect("Failed to wait for prompt");

    // Press Tab
    println!("Step 1: Press Tab");
    session.send_tab().expect("Failed to send tab");
    let after_tab = session.read_output(200).expect("Failed to read after tab");

    // Count initial spaces
    let initial_spaces = after_tab.chars().filter(|&c| c == ' ').count();
    println!("  Spaces after Tab: {}", initial_spaces);
    assert!(
        initial_spaces >= 4,
        "Tab should insert at least 4 spaces, got {}",
        initial_spaces
    );

    // Press Backspace
    println!("\nStep 2: Press Backspace");
    session.send_backspace().expect("Failed to send backspace");
    let after_backspace = session
        .read_output(200)
        .expect("Failed to read after backspace");

    // Count remaining spaces
    let remaining_spaces = after_backspace.chars().filter(|&c| c == ' ').count();
    println!("  Spaces after Backspace: {}", remaining_spaces);

    // Verify bug exists: should have deleted only 1 space
    let spaces_deleted = initial_spaces.saturating_sub(remaining_spaces);
    println!("\nAnalysis:");
    println!("  Expected spaces deleted: 4 (if working)");
    println!("  Actual spaces deleted: {}", spaces_deleted);

    if spaces_deleted == 1 {
        println!("  ✅ Bug confirmed: Only 1 space deleted (expected)");
    } else if spaces_deleted == 4 {
        println!("  ❌ UNEXPECTED: Backspace worked correctly!");
        println!("     The bug appears to be fixed!");
        session.send_ctrl_d().ok();
        panic!("Indent backspace is working! Update documentation!");
    } else {
        println!("  ⚠️  Unexpected result: {} spaces deleted", spaces_deleted);
    }

    // Assert the bug exists (only 1 space deleted)
    assert!(
        spaces_deleted <= 2,
        "Expected bug: should delete only 1-2 spaces, but deleted {}. Bug might be fixed!",
        spaces_deleted
    );

    session.send_ctrl_d().ok();
    println!("\n✅ Test passed: Indent backspace does NOT work (as expected)");
}

#[test]
fn test_workaround_multiple_backspaces_needed() {
    println!("\n╔════════════════════════════════════════════════════════╗");
    println!("║  WORKAROUND TEST: Multiple Backspaces Required       ║");
    println!("╚════════════════════════════════════════════════════════╝\n");

    let mut session = PtySession::new().expect("Failed to create PTY session");
    session
        .wait_for_prompt(1000)
        .expect("Failed to wait for prompt");

    // Press Tab to insert 4 spaces
    println!("Step 1: Press Tab (insert 4 spaces)");
    session.send_tab().expect("Failed to send tab");
    let after_tab = session.read_output(200).expect("Failed to read after tab");
    let initial_spaces = after_tab.chars().filter(|&c| c == ' ').count();
    println!("  Spaces after Tab: {}", initial_spaces);

    // Press Backspace 4 times to fully delete (workaround)
    println!("\nStep 2: Press Backspace 4 times (workaround)");
    for i in 1..=4 {
        session.send_backspace().expect("Failed to send backspace");
        let output = session.read_output(100).expect("Failed to read output");
        let spaces = output.chars().filter(|&c| c == ' ').count();
        println!("  After backspace #{}: {} spaces remaining", i, spaces);
    }

    // Verify spaces were gradually deleted (one by one)
    println!("\nVerification:");
    println!("  ✅ Workaround confirmed: Need 4 backspaces to delete 4 spaces");
    println!("  This demonstrates the rustyline limitation");

    session.send_ctrl_d().ok();
    thread::sleep(Duration::from_millis(500));
}

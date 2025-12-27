//! E2E test for Normal REPL (rustyline-based) using PTY
//!
//! This test spawns the Normal REPL in a real pseudo-terminal and verifies
//! backspace behavior and event handling.

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
        // Normal mode is the default - no args needed
        cmd.env("TERM", "xterm-256color");
        cmd.env("REPL_DEBUG", "1");  // Enable debug logging

        let _child = pair.slave.spawn_command(cmd)?;
        drop(pair.slave);

        let reader = pair.master.try_clone_reader()?;
        let writer = pair.master.take_writer()?;

        Ok(Self { reader, writer })
    }

    fn wait_for_prompt(&mut self, timeout_ms: u64) -> Result<String, Box<dyn std::error::Error>> {
        thread::sleep(Duration::from_millis(timeout_ms));
        let mut buf = [0u8; 16384];  // Larger buffer for debug output
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

    fn send_text(&mut self, text: &str) -> Result<(), Box<dyn std::error::Error>> {
        self.send_key(text.as_bytes())
    }

    fn send_enter(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.send_key(b"\r")
    }

    fn send_ctrl_d(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.send_key(b"\x04")
    }

    fn send_ctrl_u(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        self.send_key(b"\x15")  // Ctrl+U
    }

    fn read_output(&mut self, wait_ms: u64) -> Result<String, Box<dyn std::error::Error>> {
        thread::sleep(Duration::from_millis(wait_ms));
        let mut buf = [0u8; 16384];  // Larger buffer
        match self.reader.read(&mut buf) {
            Ok(n) if n > 0 => Ok(String::from_utf8_lossy(&buf[..n]).to_string()),
            Ok(_) => Ok(String::new()),
            Err(e) => Err(e.into()),
        }
    }
}

#[test]
fn test_normal_repl_two_if_statements_backspace() -> Result<(), Box<dyn std::error::Error>> {
    use std::fs::File;
    use std::io::Write as IoWrite;

    println!("\n=== Testing Normal REPL: Two If Statements + Backspace ===\n");

    let mut session = PtySession::new()?;

    // Create detailed log file
    let mut log_file = File::create("normal_repl_two_if_backspace.log")?;

    // Helper to log events
    let mut log_event = |event: &str, output: &str| -> Result<(), Box<dyn std::error::Error>> {
        writeln!(log_file, "\n=== {} ===", event)?;
        writeln!(log_file, "{}", output)?;

        // Extract debug messages
        for line in output.lines() {
            if line.contains("[REPL_DEBUG]") {
                writeln!(log_file, "{}", line)?;
            }
        }

        log_file.flush()?;
        Ok(())
    };

    // Wait for REPL to start
    println!("Step 0: Waiting for REPL startup...");
    let startup = session.wait_for_prompt(1000)?;
    log_event("STARTUP", &startup)?;
    println!("Startup complete");

    // Step 1: Type "if x > 0:" and press Enter
    println!("\nStep 1: Typing 'if x > 0:' + Enter");
    session.send_text("if x > 0:")?;
    thread::sleep(Duration::from_millis(100));
    let output1 = session.read_output(100)?;
    log_event("STEP 1: Type 'if x > 0:'", &output1)?;

    session.send_enter()?;
    thread::sleep(Duration::from_millis(200));
    let output1b = session.read_output(200)?;
    log_event("STEP 1: Press Enter (multi-line mode)", &output1b)?;
    println!("Multi-line mode entered (should see '...' prompt)");

    // Step 2: Press Tab (indent)
    println!("\nStep 2: Press Tab (4 spaces)");
    session.send_tab()?;
    thread::sleep(Duration::from_millis(200));
    let output2 = session.read_output(200)?;
    log_event("STEP 2: Press Tab", &output2)?;

    // Check if Tab handler was called
    if output2.contains("Tab pressed") {
        println!("✅ Tab event received");
    }

    // Step 3: Type "if y > 0:" and press Enter
    println!("\nStep 3: Typing 'if y > 0:' + Enter");
    session.send_text("if y > 0:")?;
    thread::sleep(Duration::from_millis(100));
    let output3 = session.read_output(100)?;
    log_event("STEP 3: Type 'if y > 0:'", &output3)?;

    session.send_enter()?;
    thread::sleep(Duration::from_millis(200));
    let output3b = session.read_output(200)?;
    log_event("STEP 3: Press Enter (stay in multi-line)", &output3b)?;

    // Step 4: Press Tab twice (double indent = 8 spaces)
    println!("\nStep 4: Press Tab (first indent)");
    session.send_tab()?;
    thread::sleep(Duration::from_millis(200));
    let output4a = session.read_output(200)?;
    log_event("STEP 4A: Press Tab #1", &output4a)?;

    println!("\nStep 5: Press Tab (second indent)");
    session.send_tab()?;
    thread::sleep(Duration::from_millis(200));
    let output4b = session.read_output(200)?;
    log_event("STEP 5: Press Tab #2 (8 spaces total)", &output4b)?;

    // Step 6: Press Backspace (normal mode: deletes 1 character)
    println!("\n=== CRITICAL STEP 6: Press Backspace (should delete 1 char) ===");
    session.send_backspace()?;
    thread::sleep(Duration::from_millis(200));
    let output5 = session.read_output(200)?;
    log_event("STEP 6: Press Backspace #1 (8→7 spaces)", &output5)?;
    println!("Output after first backspace:\n{}", output5);

    // Check for backspace handler
    if output5.contains("Backspace pressed") {
        println!("✅ PASS: Backspace event received");
        if output5.contains("all_spaces: true") {
            println!("✅ PASS: Detected in leading whitespace");
        }
        if output5.contains("Default (delete 1 char)") {
            println!("✅ PASS: Using default behavior (rustyline limitation)");
        }
    } else {
        println!("❌ FAIL: No backspace debug output");
    }

    // Step 7: Press Backspace again
    println!("\n=== STEP 7: Press Backspace again (7→6 spaces) ===");
    session.send_backspace()?;
    thread::sleep(Duration::from_millis(200));
    let output6 = session.read_output(200)?;
    log_event("STEP 7: Press Backspace #2 (7→6 spaces)", &output6)?;
    println!("Output after second backspace:\n{}", output6);

    if output6.contains("Backspace pressed") {
        println!("✅ PASS: Second backspace received");
    }

    // Step 8: Test Ctrl+U (delete 4 spaces)
    println!("\n=== STEP 8: Press Ctrl+U (should delete 4 spaces) ===");
    session.send_ctrl_u()?;
    thread::sleep(Duration::from_millis(200));
    let output7 = session.read_output(200)?;
    log_event("STEP 8: Press Ctrl+U (6→2 or 0 spaces)", &output7)?;
    println!("Output after Ctrl+U:\n{}", output7);

    if output7.contains("Ctrl+U pressed") {
        println!("✅ PASS: Ctrl+U event received");
        if output7.contains("Delete 4 spaces") || output7.contains("Delete") {
            println!("✅ PASS: Dedent handler activated");
        }
    }

    // Exit REPL
    println!("\n=== Exiting REPL ===");
    session.send_ctrl_d()?;
    thread::sleep(Duration::from_millis(500));

    writeln!(log_file, "\n=== TEST COMPLETE ===")?;
    log_file.flush()?;

    println!("\n=== Test Complete ===");
    println!("Detailed log saved to: normal_repl_two_if_backspace.log");
    println!("\nTo view the log:");
    println!("  cat normal_repl_two_if_backspace.log");
    println!("\nTo see just the debug events:");
    println!("  grep REPL_DEBUG normal_repl_two_if_backspace.log");

    Ok(())
}

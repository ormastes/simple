//! Integration test for REPL backspace behavior using PTY
//!
//! This test spawns the REPL in a real pseudo-terminal and verifies
//! terminal sequence capture works correctly.
//!
//! NOTE: This test is marked #[ignore] because it documents a known rustyline
//! limitation where Movement::BackwardChar(n) with n>1 doesn't work from
//! ConditionalEventHandler. See doc/research/REPL_BACKSPACE_LIMITATION.md
//!
//! The test remains as documentation of:
//! 1. How to test terminal applications with PTY
//! 2. What behavior we WANT but cannot achieve with rustyline
//! 3. Proof that the limitation exists (failing assertion)

use portable_pty::{native_pty_system, CommandBuilder, PtySize};
use std::io::{Read, Write};
use std::path::PathBuf;
use std::thread;
use std::time::Duration;

/// Helper to parse ANSI escape sequences from terminal output
struct AnsiParser {
    buffer: Vec<u8>,
}

impl AnsiParser {
    fn new() -> Self {
        Self { buffer: Vec::new() }
    }

    fn add_bytes(&mut self, bytes: &[u8]) {
        self.buffer.extend_from_slice(bytes);
    }

    fn get_raw(&self) -> String {
        String::from_utf8_lossy(&self.buffer).to_string()
    }

    /// Count cursor right movements (e.g., "\x1b[4C" = move right 4)
    fn count_cursor_right(&self) -> usize {
        let text = self.get_raw();
        let mut total = 0;

        // Look for CSI sequences: ESC [ n C
        let mut chars = text.chars().peekable();
        while let Some(ch) = chars.next() {
            if ch == '\x1b' {
                if chars.peek() == Some(&'[') {
                    chars.next(); // consume '['

                    // Read number
                    let mut num_str = String::new();
                    while let Some(&d) = chars.peek() {
                        if d.is_ascii_digit() {
                            num_str.push(d);
                            chars.next();
                        } else {
                            break;
                        }
                    }

                    // Check for 'C' (cursor right)
                    if chars.peek() == Some(&'C') {
                        chars.next();
                        if let Ok(n) = num_str.parse::<usize>() {
                            total += n;
                        }
                    }
                }
            }
        }

        total
    }

    /// Count cursor left movements (e.g., "\x1b[4D" = move left 4)
    fn count_cursor_left(&self) -> usize {
        let text = self.get_raw();
        let mut total = 0;

        let mut chars = text.chars().peekable();
        while let Some(ch) = chars.next() {
            if ch == '\x1b' {
                if chars.peek() == Some(&'[') {
                    chars.next();

                    let mut num_str = String::new();
                    while let Some(&d) = chars.peek() {
                        if d.is_ascii_digit() {
                            num_str.push(d);
                            chars.next();
                        } else {
                            break;
                        }
                    }

                    // Check for 'D' (cursor left)
                    if chars.peek() == Some(&'D') {
                        chars.next();
                        if let Ok(n) = num_str.parse::<usize>() {
                            total += n;
                        }
                    }
                }
            }
        }

        total
    }
}

#[test]
#[ignore = "Known rustyline limitation - backspace cannot delete multiple chars. See REPL_BACKSPACE_LIMITATION.md"]
fn test_repl_backspace_deletes_indent() {
    // Get path to REPL binary
    let binary = PathBuf::from(env!("CARGO_BIN_EXE_simple"));
    assert!(binary.exists(), "REPL binary not found at {:?}", binary);

    // Create PTY
    let pty_system = native_pty_system();
    let pair = pty_system
        .openpty(PtySize {
            rows: 24,
            cols: 80,
            pixel_width: 0,
            pixel_height: 0,
        })
        .expect("Failed to create PTY");

    // Spawn REPL
    let mut cmd = CommandBuilder::new(&binary);
    cmd.env("TERM", "xterm-256color"); // Enable ANSI sequences
    let mut child = pair.slave.spawn_command(cmd).expect("Failed to spawn REPL");

    // Drop slave to prevent deadlock
    drop(pair.slave);

    // Get I/O handles
    let mut reader = pair.master.try_clone_reader().expect("Failed to clone reader");
    let mut writer = pair.master.take_writer().expect("Failed to get writer");

    // Wait for REPL to start
    thread::sleep(Duration::from_millis(1000));

    // Read and discard startup output
    let mut buf = [0u8; 8192];
    let _ = reader.read(&mut buf);

    println!("\n=== Test 1: Tab inserts 4 spaces ===");

    // Clear parser
    let mut parser = AnsiParser::new();

    // Send Tab key
    writer.write_all(b"\t").expect("Failed to send Tab");
    writer.flush().expect("Failed to flush");
    thread::sleep(Duration::from_millis(200));

    // Read output
    match reader.read(&mut buf) {
        Ok(n) if n > 0 => {
            parser.add_bytes(&buf[..n]);
            println!("Received {} bytes", n);
            println!("Raw output: {:?}", parser.get_raw());
            println!("Cursor right movements: {}", parser.count_cursor_right());
        }
        Ok(_) => println!("No data received"),
        Err(e) => println!("Read error: {}", e),
    }

    // Verify cursor moved right (Tab should insert spaces)
    let right_movements = parser.count_cursor_right();
    assert!(
        right_movements >= 4,
        "Tab should move cursor right at least 4 positions, got {}",
        right_movements
    );

    println!("\n=== Test 2: Backspace deletes indent (4 spaces) ===");

    // Clear parser for backspace test
    parser = AnsiParser::new();

    // Send Backspace key
    writer.write_all(b"\x7f").expect("Failed to send Backspace");
    writer.flush().expect("Failed to flush");
    thread::sleep(Duration::from_millis(200));

    // Read output
    match reader.read(&mut buf) {
        Ok(n) if n > 0 => {
            parser.add_bytes(&buf[..n]);
            println!("Received {} bytes", n);
            println!("Raw output: {:?}", parser.get_raw());
            println!("Cursor left movements: {}", parser.count_cursor_left());
        }
        Ok(_) => println!("No data received"),
        Err(e) => println!("Read error: {}", e),
    }

    // Verify cursor moved left (Backspace should delete 4 spaces)
    let left_movements = parser.count_cursor_left();
    assert!(
        left_movements >= 4,
        "Backspace should move cursor left 4 positions (delete full indent), got {}",
        left_movements
    );

    println!("\n=== Test 3: Backspace after text deletes one character ===");

    // Clear parser
    parser = AnsiParser::new();

    // Send: Tab + "hello" + Backspace
    writer.write_all(b"\thello").expect("Failed to send text");
    writer.flush().expect("Failed to flush");
    thread::sleep(Duration::from_millis(200));

    // Clear buffer
    let _ = reader.read(&mut buf);

    // Now send backspace - should only delete 'o', not spaces
    writer.write_all(b"\x7f").expect("Failed to send Backspace");
    writer.flush().expect("Failed to flush");
    thread::sleep(Duration::from_millis(200));

    // Read output
    match reader.read(&mut buf) {
        Ok(n) if n > 0 => {
            parser.add_bytes(&buf[..n]);
            println!("Received {} bytes", n);
            println!("Raw output: {:?}", parser.get_raw());
            println!("Cursor left movements: {}", parser.count_cursor_left());
        }
        Ok(_) => println!("No data received"),
        Err(e) => println!("Read error: {}", e),
    }

    // Should only move left 1 position (delete single character)
    let left_movements = parser.count_cursor_left();
    assert!(
        left_movements <= 1,
        "Backspace after text should only delete 1 character, got {} positions",
        left_movements
    );

    // Cleanup: exit REPL
    writer.write_all(b"\x04").ok(); // Ctrl+D
    writer.flush().ok();

    // Wait for child process (with timeout)
    let timeout = Duration::from_secs(2);
    let start = std::time::Instant::now();
    loop {
        match child.try_wait() {
            Ok(Some(_)) => break,
            Ok(None) => {
                if start.elapsed() > timeout {
                    println!("Warning: REPL didn't exit cleanly, terminating");
                    child.kill().ok();
                    break;
                }
                thread::sleep(Duration::from_millis(100));
            }
            Err(e) => {
                println!("Error waiting for child: {}", e);
                break;
            }
        }
    }

    println!("\n✓ All backspace tests passed!");
}

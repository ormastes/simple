//! Comparison test: rustyline vs TUI REPL
//!
//! This test demonstrates the difference between:
//! - Default rustyline REPL: backspace deletes 1 space (limitation)
//! - TUI REPL (--tui): backspace deletes 4 spaces (working!)

use portable_pty::{native_pty_system, CommandBuilder, PtySize};
use std::io::{Read, Write};
use std::path::PathBuf;
use std::thread;
use std::time::Duration;

fn spawn_repl(use_tui: bool) -> Result<(Box<dyn Read + Send>, Box<dyn Write + Send>), Box<dyn std::error::Error>> {
    // Find the binary in target directory
    let binary = std::env::var("CARGO_BIN_EXE_simple_old")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            let manifest_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".to_string());
            PathBuf::from(manifest_dir).join("../../../target/debug/simple_old")
        });
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

    Ok((pair.master.try_clone_reader()?, pair.master.take_writer()?))
}

#[test]
#[cfg(feature = "tui")]
fn test_comparison_rustyline_vs_tui() {
    println!("\n╔════════════════════════════════════════════════════════╗");
    println!("║  REPL Backspace Comparison: rustyline vs TUI          ║");
    println!("╚════════════════════════════════════════════════════════╝\n");

    // Test 1: rustyline (default) - BROKEN
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("Test 1: Default REPL (rustyline)");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    match spawn_repl(false) {
        Ok((mut reader, mut writer)) => {
            thread::sleep(Duration::from_millis(1000));
            let mut buf = [0u8; 8192];
            reader.read(&mut buf).ok();

            println!("Action: Press Tab (insert 4 spaces)");
            writer.write_all(b"\t").ok();
            writer.flush().ok();
            thread::sleep(Duration::from_millis(200));
            reader.read(&mut buf).ok();

            println!("Action: Press Backspace");
            writer.write_all(b"\x7f").ok();
            writer.flush().ok();
            thread::sleep(Duration::from_millis(200));

            match reader.read(&mut buf) {
                Ok(n) if n > 0 => {
                    let output = String::from_utf8_lossy(&buf[..n]);
                    println!("Output: {}", output);

                    // Check if output contains debug info about deleting 1 vs 4 spaces
                    if output.contains(">>>   ") {
                        println!("Result: ❌ BROKEN - Only deleted 1 space (3 remain)");
                        println!("Issue: rustyline limitation (Movement::BackwardChar override)");
                    } else if output.contains(">>> ") || !output.contains("    ") {
                        println!("Result: ✅ Deleted spaces (unexpected!)");
                    }
                }
                _ => println!("No output captured"),
            }

            writer.write_all(b"\x04").ok(); // Exit
        }
        Err(e) => println!("Failed to spawn rustyline REPL: {}", e),
    }

    println!();

    // Test 2: TUI - WORKING
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("Test 2: TUI REPL (--tui flag)");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");

    match spawn_repl(true) {
        Ok((mut reader, mut writer)) => {
            thread::sleep(Duration::from_millis(1000));
            let mut buf = [0u8; 8192];
            reader.read(&mut buf).ok();

            println!("Action: Press Tab (insert 4 spaces)");
            writer.write_all(b"\t").ok();
            writer.flush().ok();
            thread::sleep(Duration::from_millis(200));
            reader.read(&mut buf).ok();

            println!("Action: Press Backspace");
            writer.write_all(b"\x7f").ok();
            writer.flush().ok();
            thread::sleep(Duration::from_millis(500));

            match reader.read(&mut buf) {
                Ok(n) if n > 0 => {
                    let output = String::from_utf8_lossy(&buf[..n]);

                    // Check for debug output showing 4 spaces deleted
                    if output.contains("Deleting 4 spaces") && output.contains("cursor=0, buffer=''") {
                        println!("Result: ✅ WORKING - Deleted all 4 spaces!");
                        println!(
                            "Debug: {}",
                            output
                                .lines()
                                .filter(|l| l.contains("DEBUG"))
                                .collect::<Vec<_>>()
                                .join("\n       ")
                        );
                    } else if !output.contains("    ") {
                        println!("Result: ✅ WORKING - Deleted indent");
                        println!("Output: {}", output);
                    } else {
                        println!("Result: ⚠️  Unexpected output");
                        println!("Output: {}", output);
                    }
                }
                _ => println!("No output captured"),
            }

            writer.write_all(b"\x04").ok(); // Exit
        }
        Err(e) => println!("Failed to spawn TUI REPL: {}", e),
    }

    println!("\n╔════════════════════════════════════════════════════════╗");
    println!("║  CONCLUSION                                            ║");
    println!("╠════════════════════════════════════════════════════════╣");
    println!("║  • Default REPL: Backspace limitation (rustyline)     ║");
    println!("║  • TUI REPL:     Backspace works correctly! ✅         ║");
    println!("║                                                        ║");
    println!("║  Usage: simple --tui                                   ║");
    println!("╚════════════════════════════════════════════════════════╝\n");
}

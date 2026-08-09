//! Cross-platform process execution for the compiler.

use std::io;
use std::process::{Command, Output};

/// Run a command and capture its output.
pub fn run(program: &str, args: &[&str]) -> io::Result<Output> {
    Command::new(program).args(args).output()
}

/// Run a shell command and capture its output.
pub fn shell(cmd: &str) -> io::Result<Output> {
    if cfg!(target_os = "windows") {
        Command::new("cmd").args(["/C", cmd]).output()
    } else {
        Command::new("sh").args(["-c", cmd]).output()
    }
}

/// Run a command and return its stdout as a string (trimmed).
pub fn run_stdout(program: &str, args: &[&str]) -> io::Result<String> {
    let output = run(program, args)?;
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

//! Simple Language Logging
//!
//! This crate provides structured logging for the Simple language compiler and runtime.
//!
//! # Modules
//!
//! - [`parse`] - Compile-time logging for lexer and parser
//! - [`run_time`] - Runtime logging for interpreter and compiled code
//!
//! # Usage
//!
//! ```ignore
//! use simple_log::{init, parse, run_time};
//!
//! // Initialize logging (call once at startup)
//! simple_log::init();
//!
//! // Compile-time logging
//! parse::token("Identifier", "foo", 1, 5);
//! parse::ast_node("FunctionDef", "main");
//!
//! // Runtime logging
//! run_time::call("main", &[]);
//! run_time::gc_start();
//! ```
//!
//! # Environment Variables
//!
//! Control logging with `SIMPLE_LOG` or `RUST_LOG`:
//!
//! ```bash
//! # All logs at info level
//! SIMPLE_LOG=info ./simple run program.spl
//!
//! # Parse logs only
//! SIMPLE_LOG=simple_log::parse=debug ./simple run program.spl
//!
//! # Runtime GC logs
//! SIMPLE_LOG=simple_log::run_time::gc=trace ./simple run program.spl
//!
//! # Multiple targets
//! SIMPLE_LOG=simple_log::parse=debug,simple_log::run_time::gc=info ./simple run program.spl
//! ```
//!
//! # Log Levels
//!
//! - `error` - Errors that may cause failure
//! - `warn` - Warnings about potential issues
//! - `info` - High-level events (file processing, GC cycles)
//! - `debug` - Detailed events (AST nodes, function calls)
//! - `trace` - Very detailed events (tokens, allocations)

pub mod parse;
pub mod run_time;

use tracing_subscriber::{fmt, layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

/// Initialize structured logging with env-based filtering.
///
/// - Controlled by `SIMPLE_LOG`/`RUST_LOG` env vars (e.g., `SIMPLE_LOG=info`).
/// - Uses span-based, structured logging via `tracing`.
///
/// # Example
///
/// ```ignore
/// fn main() {
///     simple_log::init();
///     // ... rest of program
/// }
/// ```
pub fn init() {
    let env_filter = EnvFilter::try_from_env("SIMPLE_LOG")
        .or_else(|_| EnvFilter::try_from_env("RUST_LOG"))
        .unwrap_or_else(|_| EnvFilter::new("info"));

    let fmt_layer = fmt::layer().with_target(true).with_line_number(true);
    tracing_subscriber::registry().with(env_filter).with(fmt_layer).init();
}

/// Initialize logging with a custom filter string.
///
/// # Example
///
/// ```ignore
/// simple_log::init_with_filter("simple_log::parse=debug,simple_log::run_time=info");
/// ```
pub fn init_with_filter(filter: &str) {
    let env_filter = EnvFilter::new(filter);
    let fmt_layer = fmt::layer().with_target(true).with_line_number(true);
    tracing_subscriber::registry().with(env_filter).with(fmt_layer).init();
}

/// Initialize logging with compact output (no timestamps, minimal format).
///
/// Useful for testing or when piping output.
pub fn init_compact() {
    let env_filter = EnvFilter::try_from_env("SIMPLE_LOG")
        .or_else(|_| EnvFilter::try_from_env("RUST_LOG"))
        .unwrap_or_else(|_| EnvFilter::new("info"));

    let fmt_layer = fmt::layer().with_target(true).with_level(true).without_time().compact();

    tracing_subscriber::registry().with(env_filter).with(fmt_layer).init();
}

/// Initialize logging to both stdout and a file with automatic rotation.
///
/// This function enables dual logging:
/// - **stdout**: INFO level and above (for user-facing messages)
/// - **file**: TRACE level and above (for diagnostics)
///
/// # Arguments
///
/// * `log_dir` - Directory for log files (defaults to `.simple/logs`)
/// * `filter` - Optional filter string (defaults to "info")
///
/// # File Rotation
///
/// Log files are rotated daily with the format `simple.log.YYYY-MM-DD`.
/// Use `cleanup_old_logs()` to remove old logs.
///
/// # Example
///
/// ```ignore
/// simple_log::init_dual(None, None)?; // Uses default .simple/logs directory
/// simple_log::cleanup_old_logs(std::path::Path::new(".simple/logs"), 7)?;
/// ```
pub fn init_dual(log_dir: Option<&std::path::Path>, filter: Option<&str>) -> std::io::Result<()> {
    use std::fs;
    use std::path::Path;
    use tracing_subscriber::fmt::writer::MakeWriterExt;

    let log_dir = log_dir.unwrap_or_else(|| Path::new(".simple/logs"));
    fs::create_dir_all(log_dir)?;

    let file_appender = tracing_appender::rolling::daily(log_dir, "simple.log");
    let (non_blocking, _guard) = tracing_appender::non_blocking(file_appender);

    // Leak the guard to keep the file writer alive for program lifetime
    std::mem::forget(_guard);

    // Parse filter from environment or use provided/default
    let env_filter = if let Some(f) = filter {
        EnvFilter::new(f)
    } else {
        EnvFilter::try_from_env("SIMPLE_LOG")
            .or_else(|_| EnvFilter::try_from_env("RUST_LOG"))
            .unwrap_or_else(|_| EnvFilter::new("info"))
    };

    // Write INFO+ to stdout, TRACE+ to file
    let stdout = std::io::stdout.with_max_level(tracing::Level::INFO);
    let file = non_blocking.with_max_level(tracing::Level::TRACE);

    let fmt_layer = fmt::layer()
        .with_target(true)
        .with_line_number(true)
        .with_thread_ids(true)
        .with_writer(stdout.and(file));

    tracing_subscriber::registry().with(env_filter).with(fmt_layer).init();

    Ok(())
}

/// Remove log files older than the specified number of days.
///
/// # Arguments
///
/// * `log_dir` - Directory containing log files
/// * `keep_days` - Number of days to keep (files older than this are deleted)
///
/// # Example
///
/// ```ignore
/// // Keep only the last 7 days of logs
/// simple_log::cleanup_old_logs(std::path::Path::new(".simple/logs"), 7)?;
/// ```
pub fn cleanup_old_logs(log_dir: &std::path::Path, keep_days: u64) -> std::io::Result<()> {
    use std::time::{Duration, SystemTime};

    if !log_dir.exists() {
        return Ok(()); // Nothing to clean up
    }

    let cutoff = SystemTime::now()
        .checked_sub(Duration::from_secs(keep_days * 86400))
        .unwrap_or(SystemTime::UNIX_EPOCH);

    for entry in std::fs::read_dir(log_dir)? {
        let entry = entry?;
        let path = entry.path();

        // Only process files (not directories)
        if !path.is_file() {
            continue;
        }

        // Skip if filename doesn't match our log pattern
        if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
            if !name.starts_with("simple.log") {
                continue;
            }
        }

        // Get file modification time
        let metadata = entry.metadata()?;
        if let Ok(modified) = metadata.modified() {
            if modified < cutoff {
                // File is older than keep_days, delete it
                if let Err(e) = std::fs::remove_file(&path) {
                    tracing::warn!(
                        path = %path.display(),
                        error = %e,
                        "Failed to remove old log file"
                    );
                }
            }
        }
    }

    Ok(())
}

/// Initialize logging to a file.
///
/// # Arguments
///
/// * `path` - Path to the log file
/// * `filter` - Optional filter string (defaults to "info")
#[cfg(feature = "file")]
pub fn init_file(path: &std::path::Path, filter: Option<&str>) -> std::io::Result<()> {
    use std::fs::File;
    use tracing_subscriber::fmt::writer::MakeWriterExt;

    let file = File::create(path)?;
    let env_filter = EnvFilter::new(filter.unwrap_or("info"));

    let fmt_layer = fmt::layer()
        .with_target(true)
        .with_line_number(true)
        .with_ansi(false)
        .with_writer(file);

    tracing_subscriber::registry().with(env_filter).with(fmt_layer).init();

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_modules_accessible() {
        // Just verify modules are accessible
        let _ = parse::token;
        let _ = run_time::call;
    }
}

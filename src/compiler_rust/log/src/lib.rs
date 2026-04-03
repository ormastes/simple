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

use std::path::{Path, PathBuf};
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
    use tracing_subscriber::fmt::writer::MakeWriterExt;

    let log_dir = resolve_log_dir(log_dir)?;

    let file_appender = std::panic::catch_unwind(|| tracing_appender::rolling::daily(&log_dir, "simple.log"))
        .map_err(|_| std::io::Error::new(std::io::ErrorKind::Other, "failed to initialize rolling log appender"))?;
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

/// Pick a writable log directory without panicking if the preferred location is not usable.
pub fn resolve_log_dir(log_dir: Option<&Path>) -> std::io::Result<PathBuf> {
    let preferred = log_dir.unwrap_or_else(|| Path::new(".simple/logs"));
    let default_dir = PathBuf::from(".simple/logs");
    let temp_dir = std::env::temp_dir().join("simple_logs");
    let mut candidates = vec![preferred.to_path_buf()];

    if preferred != default_dir.as_path() {
        candidates.push(default_dir);
    }
    if candidates.iter().all(|path| path != &temp_dir) {
        candidates.push(temp_dir);
    }

    let mut last_error = None;
    for candidate in candidates {
        match ensure_log_dir_writable(&candidate) {
            Ok(()) => return Ok(candidate),
            Err(err) => last_error = Some(err),
        }
    }

    Err(last_error.unwrap_or_else(|| {
        std::io::Error::new(std::io::ErrorKind::PermissionDenied, "no writable log directory available")
    }))
}

fn ensure_log_dir_writable(log_dir: &Path) -> std::io::Result<()> {
    use std::fs::{self, OpenOptions};
    use std::io::Write;

    fs::create_dir_all(log_dir)?;
    let probe_path = log_dir.join(format!(".simple-log-probe-{}", std::process::id()));
    let mut probe = OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .open(&probe_path)?;
    probe.write_all(b"ok")?;
    drop(probe);
    let _ = fs::remove_file(&probe_path);
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

#[cfg(test)]
mod tests {
    use super::resolve_log_dir;
    use std::fs;

    #[test]
    fn resolve_log_dir_uses_preferred_directory_when_writable() {
        let temp = tempfile::tempdir().unwrap();
        let preferred = temp.path().join("logs");
        let resolved = resolve_log_dir(Some(&preferred)).unwrap();
        assert_eq!(resolved, preferred);
    }

    #[test]
    fn resolve_log_dir_falls_back_when_preferred_is_not_a_directory() {
        let temp = tempfile::tempdir().unwrap();
        let blocking_file = temp.path().join("not-a-dir");
        fs::write(&blocking_file, "blocked").unwrap();

        let resolved = resolve_log_dir(Some(&blocking_file)).unwrap();
        assert_ne!(resolved, blocking_file);
    }
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

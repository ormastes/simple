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
    tracing_subscriber::registry()
        .with(env_filter)
        .with(fmt_layer)
        .init();
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
    tracing_subscriber::registry()
        .with(env_filter)
        .with(fmt_layer)
        .init();
}

/// Initialize logging with compact output (no timestamps, minimal format).
///
/// Useful for testing or when piping output.
pub fn init_compact() {
    let env_filter = EnvFilter::try_from_env("SIMPLE_LOG")
        .or_else(|_| EnvFilter::try_from_env("RUST_LOG"))
        .unwrap_or_else(|_| EnvFilter::new("info"));

    let fmt_layer = fmt::layer()
        .with_target(true)
        .with_level(true)
        .without_time()
        .compact();

    tracing_subscriber::registry()
        .with(env_filter)
        .with(fmt_layer)
        .init();
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

    tracing_subscriber::registry()
        .with(env_filter)
        .with(fmt_layer)
        .init();

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

//! Runtime initialization for the Simple CLI
//!
//! This module handles the initialization sequence for the Simple driver:
//! - Logging setup (dual logging in debug mode)
//! - Interpreter handler registration
//! - Panic hook installation
//! - Signal handler setup

use crate::StartupMetrics;
use std::path::PathBuf;

/// Initialize logging system based on build mode
///
/// In debug mode: Enables dual logging (stdout + file) with optional log directory
/// In release mode: Simple stdout-only logging
pub fn init_logging(metrics: &mut StartupMetrics) {
    let log_start = std::time::Instant::now();

    // Enable dual logging (stdout + file) in debug mode only for diagnostics
    #[cfg(debug_assertions)]
    {
        let log_dir = std::env::var("SIMPLE_LOG_DIR").ok().map(PathBuf::from);
        let log_filter = std::env::var("SIMPLE_LOG")
            .ok()
            .or_else(|| std::env::var("RUST_LOG").ok());

        if let Err(e) = simple_log::init_dual(log_dir.as_deref(), log_filter.as_deref()) {
            eprintln!("warning: failed to initialize file logging: {}", e);
            simple_log::init(); // Fallback to stdout only
        }

        // Cleanup old logs (keep 7 days) - non-fatal if it fails
        let _ = simple_log::cleanup_old_logs(std::path::Path::new(".simple/logs"), 7);
    }

    // In release mode, use simple stdout-only logging
    #[cfg(not(debug_assertions))]
    simple_log::init();

    metrics.record(crate::StartupPhase::LoggingInit, log_start.elapsed());
}

/// Initialize interpreter handlers for hybrid execution
pub fn init_interpreter_handlers(metrics: &mut StartupMetrics) {
    let handler_start = std::time::Instant::now();
    simple_compiler::interpreter_ffi::init_interpreter_handlers();
    metrics.record(crate::StartupPhase::HandlerInit, handler_start.elapsed());
}

/// Install panic hook for detailed crash diagnostics (debug mode only)
pub fn init_panic_hook(metrics: &mut StartupMetrics) {
    let panic_start = std::time::Instant::now();

    #[cfg(debug_assertions)]
    std::panic::set_hook(Box::new(|panic_info| {
        use std::backtrace::Backtrace;
        use std::io::Write;

        let backtrace = Backtrace::force_capture();

        let location = panic_info
            .location()
            .map(|l| format!("{}:{}:{}", l.file(), l.line(), l.column()))
            .unwrap_or_else(|| "unknown".to_string());

        let message = if let Some(s) = panic_info.payload().downcast_ref::<&str>() {
            s.to_string()
        } else if let Some(s) = panic_info.payload().downcast_ref::<String>() {
            s.clone()
        } else {
            "unknown panic".to_string()
        };

        // Log to file via tracing
        tracing::error!(
            message = %message,
            location = %location,
            backtrace = %backtrace,
            "PANIC"
        );

        // Also print to stderr for immediate visibility
        let mut stderr = std::io::stderr();
        let _ = writeln!(stderr, "\n=== PANIC ===");
        let _ = writeln!(stderr, "Message: {}", message);
        let _ = writeln!(stderr, "Location: {}", location);
        let _ = writeln!(stderr, "\nBacktrace:\n{}", backtrace);
        let _ = writeln!(stderr, "=============\n");
        let _ = stderr.flush();
    }));

    metrics.record(crate::StartupPhase::PanicHookInit, panic_start.elapsed());
}

/// Install signal handlers for graceful interrupt (Ctrl-C) - debug mode only
pub fn init_signal_handlers(metrics: &mut StartupMetrics) {
    let signal_start = std::time::Instant::now();

    #[cfg(debug_assertions)]
    simple_compiler::interpreter::init_signal_handlers();

    metrics.record(crate::StartupPhase::SignalHandlerInit, signal_start.elapsed());
}

/// Run all initialization phases in sequence
pub fn init_runtime(metrics: &mut StartupMetrics) {
    init_logging(metrics);
    init_interpreter_handlers(metrics);
    init_panic_hook(metrics);
    init_signal_handlers(metrics);
}

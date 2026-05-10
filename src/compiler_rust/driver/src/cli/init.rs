//! Runtime initialization for the Simple CLI
//!
//! This module handles the initialization sequence for the Simple driver:
//! - Logging setup (dual logging in debug mode)
//! - Interpreter handler registration
//! - Panic hook installation
//! - Signal handler setup

use crate::StartupMetrics;
use std::path::PathBuf;
use std::fs;
use walkdir::WalkDir;

/// Initialize logging system.
///
/// Enables dual logging (stdout + file) by default for all build modes.
/// Log directory: `SIMPLE_LOG_DIR` env var, or `.simple/logs/` (local project).
/// Set `SIMPLE_LOG_FILE=0` to disable file logging.
pub fn init_logging(metrics: &mut StartupMetrics) {
    let log_start = std::time::Instant::now();

    let file_disabled = std::env::var("SIMPLE_LOG_FILE")
        .map(|v| v == "0" || v.eq_ignore_ascii_case("false") || v.eq_ignore_ascii_case("off"))
        .unwrap_or(false);

    if !file_disabled {
        let requested_log_dir = std::env::var("SIMPLE_LOG_DIR").ok().map(PathBuf::from);
        let log_filter = std::env::var("SIMPLE_LOG")
            .ok()
            .or_else(|| std::env::var("RUST_LOG").ok());
        let resolved_log_dir = crate::log::resolve_log_dir(requested_log_dir.as_deref());

        if let Err(e) = crate::log::init_dual(resolved_log_dir.as_deref().ok(), log_filter.as_deref()) {
            eprintln!("warning: failed to initialize file logging: {}", e);
            crate::log::init(); // Fallback to stdout only
        }

        if let Ok(log_dir) = resolved_log_dir {
            // Cleanup old logs (keep 7 days) - non-fatal if it fails
            let _ = crate::log::cleanup_old_logs(&log_dir, 7);
        }
    } else {
        crate::log::init();
    }

    metrics.record(crate::StartupPhase::LoggingInit, log_start.elapsed());
}

/// Initialize interpreter handlers for hybrid execution
pub fn init_interpreter_handlers(metrics: &mut StartupMetrics) {
    let handler_start = std::time::Instant::now();
    simple_compiler::interpreter_ffi::init_interpreter_handlers();
    metrics.record(crate::StartupPhase::HandlerInit, handler_start.elapsed());
}

/// Install panic hook for detailed crash diagnostics (all build modes).
/// Writes crash report to stderr, tracing log, AND a dedicated crash file.
pub fn init_panic_hook(metrics: &mut StartupMetrics) {
    let panic_start = std::time::Instant::now();

    std::panic::set_hook(Box::new(|panic_info| {
        use std::backtrace::Backtrace;
        use std::io::Write;

        // Extract message early so we can check for broken pipe
        let message = if let Some(s) = panic_info.payload().downcast_ref::<&str>() {
            s.to_string()
        } else if let Some(s) = panic_info.payload().downcast_ref::<String>() {
            s.clone()
        } else {
            "unknown panic".to_string()
        };

        // Broken pipe is normal MCP/CLI shutdown — exit cleanly without crash log
        if message.contains("Broken pipe") || message.contains("os error 32") {
            std::process::exit(0);
        }

        let backtrace = Backtrace::force_capture();

        let location = panic_info
            .location()
            .map(|l| format!("{}:{}:{}", l.file(), l.line(), l.column()))
            .unwrap_or_else(|| "unknown".to_string());

        let timestamp = chrono::Utc::now().format("%Y-%m-%dT%H:%M:%SZ").to_string();
        let pid = std::process::id();

        // Log to file via tracing
        tracing::error!(
            message = %message,
            location = %location,
            backtrace = %backtrace,
            "PANIC"
        );

        // Print to stderr for immediate visibility
        let mut stderr = std::io::stderr();
        let _ = writeln!(stderr, "\n=== PANIC ===");
        let _ = writeln!(stderr, "Time: {}", timestamp);
        let _ = writeln!(stderr, "PID: {}", pid);
        let _ = writeln!(stderr, "Message: {}", message);
        let _ = writeln!(stderr, "Location: {}", location);
        let _ = writeln!(stderr, "\nBacktrace:\n{}", backtrace);
        let _ = writeln!(stderr, "=============\n");
        let _ = stderr.flush();

        // Write crash log file (best-effort)
        write_crash_log(&timestamp, pid, &message, &location, &format!("{}", backtrace));
    }));

    metrics.record(crate::StartupPhase::PanicHookInit, panic_start.elapsed());
}

/// Write a crash log file to `.simple/logs/` or system temp directory.
fn write_crash_log(timestamp: &str, pid: u32, message: &str, location: &str, backtrace: &str) {
    use std::io::Write;

    let crash_dir = std::env::var("SIMPLE_LOG_DIR").map(PathBuf::from).unwrap_or_else(|_| {
        let local = PathBuf::from(".simple/logs");
        if local.exists() || fs::create_dir_all(&local).is_ok() {
            local
        } else {
            std::env::temp_dir().join("simple_logs")
        }
    });
    let _ = fs::create_dir_all(&crash_dir);

    let crash_file = crash_dir.join(format!("crash_{}.log", pid));
    let mut f = match fs::OpenOptions::new().create(true).append(true).open(&crash_file) {
        Ok(f) => f,
        Err(_) => return,
    };

    let _ = writeln!(f, "=== SIMPLE CRASH REPORT ===");
    let _ = writeln!(f, "Time: {}", timestamp);
    let _ = writeln!(f, "PID: {}", pid);
    let _ = writeln!(f, "Version: {}", env!("CARGO_PKG_VERSION"));
    let _ = writeln!(f, "OS: {} {}", std::env::consts::OS, std::env::consts::ARCH);
    let _ = writeln!(f, "Message: {}", message);
    let _ = writeln!(f, "Location: {}", location);
    let _ = writeln!(f, "\nBacktrace:\n{}", backtrace);
    let _ = writeln!(f, "===========================\n");

    eprintln!("[crash] report written to {}", crash_file.display());
}

/// Install signal handlers for graceful interrupt (Ctrl-C) - all build modes.
pub fn init_signal_handlers(metrics: &mut StartupMetrics) {
    let signal_start = std::time::Instant::now();
    simple_compiler::interpreter::init_signal_handlers();
    metrics.record(crate::StartupPhase::SignalHandlerInit, signal_start.elapsed());
}

/// Initialize execution limit from environment variables
///
/// Reads SIMPLE_EXECUTION_LIMIT to set the limit (0 = disabled)
/// Reads SIMPLE_EXECUTION_LIMIT_ENABLED to enable/disable checking
pub fn init_execution_limit(metrics: &mut StartupMetrics) {
    let limit_start = std::time::Instant::now();

    // Read limit from env (default: 10 million, 0 = no limit)
    if let Ok(limit_str) = std::env::var("SIMPLE_EXECUTION_LIMIT") {
        if let Ok(limit) = limit_str.parse::<u64>() {
            simple_compiler::set_execution_limit(limit);
            if limit == 0 {
                // Setting limit to 0 also disables checking
                simple_compiler::set_execution_limit_enabled(false);
            }
        }
    }

    // Allow explicit enable/disable
    if let Ok(enabled_str) = std::env::var("SIMPLE_EXECUTION_LIMIT_ENABLED") {
        let enabled = matches!(enabled_str.to_lowercase().as_str(), "1" | "true" | "yes");
        simple_compiler::set_execution_limit_enabled(enabled);
    }

    metrics.record(crate::StartupPhase::ExecutionLimitInit, limit_start.elapsed());
}

/// Clean up stale temporary database files from crashed writes
/// This removes any .sdn.tmp and .cache.tmp files left over from interrupted atomic writes
pub fn cleanup_stale_db_files(metrics: &mut StartupMetrics) {
    let cleanup_start = std::time::Instant::now();

    // Check for stale .sdn.tmp and .cache.tmp files in common database locations
    let db_locations = vec![
        PathBuf::from("doc/todo"),
        PathBuf::from("doc/feature"),
        PathBuf::from("doc/task"),
        PathBuf::from(".simple"),
    ];

    for location in db_locations {
        if !location.exists() {
            continue;
        }

        // Search for .tmp files (atomic write artifacts)
        if let Ok(entries) = fs::read_dir(&location) {
            for entry in entries.flatten() {
                let path = entry.path();
                if path.extension().is_some_and(|ext| ext == "tmp") {
                    let _ = fs::remove_file(&path);
                }
            }
        }

        // Also check subdirectories recursively (for nested database files)
        WalkDir::new(&location)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.file_type().is_file())
            .for_each(|entry| {
                let path = entry.path();
                if path.extension().is_some_and(|ext| ext == "tmp") {
                    let _ = fs::remove_file(path);
                }
            });
    }

    metrics.record(crate::StartupPhase::DbCleanup, cleanup_start.elapsed());
}

/// Initialize stack overflow detection from environment variables
///
/// Reads SIMPLE_STACK_OVERFLOW_DETECTION to enable/disable (default: on in debug, off in release)
/// Reads SIMPLE_MAX_RECURSION_DEPTH to set the limit (default: 1000)
pub fn init_stack_overflow_detection(metrics: &mut StartupMetrics) {
    let start = std::time::Instant::now();

    if let Ok(val) = std::env::var("SIMPLE_STACK_OVERFLOW_DETECTION") {
        let enabled = matches!(val.to_lowercase().as_str(), "1" | "true" | "yes");
        simple_compiler::set_stack_overflow_detection_enabled(enabled);
    }

    if let Ok(val) = std::env::var("SIMPLE_MAX_RECURSION_DEPTH") {
        if let Ok(limit) = val.parse::<u64>() {
            simple_compiler::set_max_recursion_depth(limit);
        }
    }

    metrics.record(crate::StartupPhase::StackOverflowInit, start.elapsed());
}

/// Initialize timeout watchdog from environment variables
///
/// Reads SIMPLE_TIMEOUT_SECONDS to set wall-clock timeout (0 = disabled, default: 0)
pub fn init_timeout_watchdog(metrics: &mut StartupMetrics) {
    let start = std::time::Instant::now();

    if let Ok(val) = std::env::var("SIMPLE_TIMEOUT_SECONDS") {
        if let Ok(secs) = val.parse::<u64>() {
            if secs > 0 {
                simple_compiler::start_watchdog(secs);
            }
        }
    }

    metrics.record(crate::StartupPhase::TimeoutInit, start.elapsed());
}

/// Run all initialization phases in sequence
pub fn init_runtime(metrics: &mut StartupMetrics) {
    init_logging(metrics);
    cleanup_stale_db_files(metrics);
    crate::repl_runner_ffi::register();
    init_interpreter_handlers(metrics);
    init_panic_hook(metrics);
    init_signal_handlers(metrics);
    init_execution_limit(metrics);
    init_stack_overflow_detection(metrics);
    init_timeout_watchdog(metrics);
}

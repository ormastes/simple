//! Logging initialization (inlined from simple-log crate)

use tracing_subscriber::{fmt, layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

/// Initialize structured logging with env-based filtering.
pub fn init() {
    let env_filter = EnvFilter::try_from_env("SIMPLE_LOG")
        .or_else(|_| EnvFilter::try_from_env("RUST_LOG"))
        .unwrap_or_else(|_| EnvFilter::new("info"));

    let fmt_layer = fmt::layer().with_target(true).with_line_number(true);
    tracing_subscriber::registry().with(env_filter).with(fmt_layer).init();
}

/// Initialize dual logging (stdout + file).
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

    let env_filter = if let Some(f) = filter {
        EnvFilter::new(f)
    } else {
        EnvFilter::try_from_env("SIMPLE_LOG")
            .or_else(|_| EnvFilter::try_from_env("RUST_LOG"))
            .unwrap_or_else(|_| EnvFilter::new("info"))
    };

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
pub fn cleanup_old_logs(log_dir: &std::path::Path, keep_days: u64) -> std::io::Result<()> {
    use std::time::{Duration, SystemTime};

    if !log_dir.exists() {
        return Ok(());
    }

    let cutoff = SystemTime::now()
        .checked_sub(Duration::from_secs(keep_days * 86400))
        .unwrap_or(SystemTime::UNIX_EPOCH);

    for entry in std::fs::read_dir(log_dir)? {
        let entry = entry?;
        let path = entry.path();

        if !path.is_file() {
            continue;
        }

        if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
            if !name.starts_with("simple.log") {
                continue;
            }
        }

        let metadata = entry.metadata()?;
        if let Ok(modified) = metadata.modified() {
            if modified < cutoff {
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

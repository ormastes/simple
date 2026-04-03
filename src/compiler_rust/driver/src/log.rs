//! Logging initialization (inlined from simple-log crate)

use std::path::{Path, PathBuf};
use tracing_subscriber::{fmt, layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

/// Initialize structured logging with env-based filtering (stderr only).
pub fn init() {
    let env_filter = EnvFilter::try_from_env("SIMPLE_LOG")
        .or_else(|_| EnvFilter::try_from_env("RUST_LOG"))
        .unwrap_or_else(|_| EnvFilter::new("info"));

    let fmt_layer = fmt::layer()
        .with_target(true)
        .with_line_number(true)
        .with_writer(std::io::stderr);
    tracing_subscriber::registry().with(env_filter).with(fmt_layer).init();
}

/// Initialize dual logging (stdout + file).
pub fn init_dual(log_dir: Option<&std::path::Path>, filter: Option<&str>) -> std::io::Result<()> {
    use std::fs;
    use tracing_subscriber::fmt::writer::MakeWriterExt;

    let log_dir = resolve_log_dir(log_dir)?;

    let file_appender = std::panic::catch_unwind(|| tracing_appender::rolling::daily(&log_dir, "simple.log"))
        .map_err(|_| std::io::Error::new(std::io::ErrorKind::Other, "failed to initialize rolling log appender"))?;
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

    let stderr = std::io::stderr.with_max_level(tracing::Level::INFO);
    let file = non_blocking.with_max_level(tracing::Level::TRACE);

    let fmt_layer = fmt::layer()
        .with_target(true)
        .with_line_number(true)
        .with_thread_ids(true)
        .with_writer(stderr.and(file));

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

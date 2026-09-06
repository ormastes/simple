//! Logging initialization (inlined from simple-log crate)

use std::path::{Path, PathBuf};
use tracing_subscriber::{fmt, layer::SubscriberExt, util::SubscriberInitExt, EnvFilter};

/// Initialize structured logging with env-based filtering (stderr only).
pub fn init() {
    let env_filter = EnvFilter::try_from_env("SIMPLE_LOG")
        .or_else(|_| EnvFilter::try_from_env("RUST_LOG"))
        .unwrap_or_else(|_| EnvFilter::new("error"));

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
        .map_err(|_| std::io::Error::other("failed to initialize rolling log appender"))?;
    let (non_blocking, _guard) = tracing_appender::non_blocking(file_appender);

    // Leak the guard to keep the file writer alive for program lifetime
    std::mem::forget(_guard);

    let env_filter = if let Some(f) = filter {
        EnvFilter::new(f)
    } else {
        EnvFilter::try_from_env("SIMPLE_LOG")
            .or_else(|_| EnvFilter::try_from_env("RUST_LOG"))
            .unwrap_or_else(|_| EnvFilter::new("error"))
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
        std::io::Error::new(
            std::io::ErrorKind::PermissionDenied,
            "no writable log directory available",
        )
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

        // Filter by NAME first — no metadata syscall for non-candidates.
        // A backlog of unrelated files (e.g. 10k crash_*.log) previously cost
        // one statx per entry per process start.
        let file_name = entry.file_name();
        let Some(name) = file_name.to_str() else {
            continue;
        };
        if !is_cleanup_candidate(name) {
            continue;
        }

        let path = entry.path();
        if !entry.file_type().map(|t| t.is_file()).unwrap_or(false) {
            continue;
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

/// Name filter for `cleanup_old_logs`: decides candidacy from the file NAME
/// alone, before any metadata syscall.
fn is_cleanup_candidate(name: &str) -> bool {
    name.starts_with("simple.log")
        || (name.starts_with("crash_") && name.ends_with(".log"))
        || name.starts_with(".simple-log-probe-")
}

#[cfg(test)]
mod tests {
    use super::{cleanup_old_logs, is_cleanup_candidate, resolve_log_dir};
    use std::fs;
    use std::path::Path;
    use std::time::SystemTime;

    fn make_old(p: &Path) {
        fs::write(p, "x").unwrap();
        let f = fs::File::options().write(true).open(p).unwrap();
        f.set_modified(SystemTime::UNIX_EPOCH).unwrap();
    }

    // REPRO shape: many non-candidate entries + few candidates; only
    // candidates are touched. The stat count itself isn't observable here,
    // so candidacy is additionally pinned by the predicate tests below.
    #[test]
    fn cleanup_ignores_bulk_non_candidates() {
        let temp = tempfile::tempdir().unwrap();
        let dir = temp.path();
        for i in 0..50 {
            make_old(&dir.join(format!("unrelated_{i}.txt")));
        }
        make_old(&dir.join("simple.log.old"));
        make_old(&dir.join("crash_7.log"));

        cleanup_old_logs(dir, 7).unwrap();

        assert!(!dir.join("simple.log.old").exists());
        assert!(!dir.join("crash_7.log").exists());
        assert_eq!(fs::read_dir(dir).unwrap().count(), 50);
    }

    #[test]
    fn cleanup_empty_dir_is_ok() {
        let temp = tempfile::tempdir().unwrap();
        cleanup_old_logs(temp.path(), 7).unwrap();
        assert_eq!(fs::read_dir(temp.path()).unwrap().count(), 0);
    }

    #[test]
    fn cleanup_missing_dir_is_ok() {
        let temp = tempfile::tempdir().unwrap();
        cleanup_old_logs(&temp.path().join("nope"), 7).unwrap();
    }

    #[test]
    fn cleanup_dir_with_only_candidates_empties_it() {
        let temp = tempfile::tempdir().unwrap();
        let dir = temp.path();
        make_old(&dir.join("simple.log.1"));
        make_old(&dir.join("crash_a.log"));
        make_old(&dir.join(".simple-log-probe-1"));
        cleanup_old_logs(dir, 7).unwrap();
        assert_eq!(fs::read_dir(dir).unwrap().count(), 0);
    }

    #[test]
    fn cleanup_retains_candidate_newer_than_cutoff() {
        let temp = tempfile::tempdir().unwrap();
        let dir = temp.path();
        fs::write(dir.join("simple.log.fresh"), "x").unwrap(); // mtime = now
        make_old(&dir.join("simple.log.stale"));
        cleanup_old_logs(dir, 7).unwrap();
        assert!(dir.join("simple.log.fresh").exists());
        assert!(!dir.join("simple.log.stale").exists());
    }

    // Matching is prefix-based (plus .log suffix for crash_), NOT substring.
    #[test]
    fn candidate_predicate_matches_intended_names() {
        assert!(is_cleanup_candidate("simple.log"));
        assert!(is_cleanup_candidate("simple.log.2020-01-01"));
        assert!(is_cleanup_candidate("crash_123.log"));
        assert!(is_cleanup_candidate(".simple-log-probe-abc"));

        // Pattern appearing mid-name must NOT match.
        assert!(!is_cleanup_candidate("my_simple.log"));
        assert!(!is_cleanup_candidate("old_crash_123.log"));
        assert!(!is_cleanup_candidate("x.simple-log-probe-1"));
        // crash_ prefix without .log suffix must NOT match.
        assert!(!is_cleanup_candidate("crash_123.txt"));
        assert!(!is_cleanup_candidate("crash_"));
        assert!(!is_cleanup_candidate("unrelated.txt"));
        assert!(!is_cleanup_candidate(""));
    }

    #[test]
    fn cleanup_removes_only_old_matching_files() {
        let temp = tempfile::tempdir().unwrap();
        let dir = temp.path();
        for name in [
            "simple.log.2020-01-01",
            "crash_123.log",
            ".simple-log-probe-999",
            "unrelated.txt",
        ] {
            let p = dir.join(name);
            fs::write(&p, "x").unwrap();
            let f = fs::File::options().write(true).open(&p).unwrap();
            f.set_modified(std::time::SystemTime::UNIX_EPOCH).unwrap();
        }
        // Recent candidate must survive.
        fs::write(dir.join("simple.log"), "x").unwrap();

        cleanup_old_logs(dir, 7).unwrap();

        assert!(!dir.join("simple.log.2020-01-01").exists());
        assert!(!dir.join("crash_123.log").exists());
        assert!(!dir.join(".simple-log-probe-999").exists());
        assert!(dir.join("unrelated.txt").exists());
        assert!(dir.join("simple.log").exists());
    }

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

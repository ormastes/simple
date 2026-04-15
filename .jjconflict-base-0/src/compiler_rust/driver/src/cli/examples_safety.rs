//! Shared safety policy for direct execution and compilation of example files.

use std::path::{Component, Path};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use simple_common::fault_detection::reset_timeout;
use simple_compiler::{start_watchdog, stop_watchdog};

const DEFAULT_EXAMPLES_TIMEOUT_SECS: u64 = 10;
const EXAMPLES_CHILD_ENV: &str = "SIMPLE_EXAMPLE_ISOLATED_CHILD";

pub fn is_examples_path(path: &Path) -> bool {
    path.components().any(|component| match component {
        Component::Normal(name) => name == "examples",
        _ => false,
    })
}

pub fn examples_timeout_secs() -> u64 {
    std::env::var("SIMPLE_TIMEOUT_SECONDS")
        .ok()
        .and_then(|value| value.parse::<u64>().ok())
        .filter(|value| *value > 0)
        .unwrap_or(DEFAULT_EXAMPLES_TIMEOUT_SECS)
}

fn should_apply_examples_timeout(path: &Path) -> bool {
    is_examples_path(path) && std::env::var_os("SIMPLE_TIMEOUT_SECONDS").is_none()
}

fn should_isolate_example_process(path: &Path) -> bool {
    is_examples_path(path) && std::env::var_os(EXAMPLES_CHILD_ENV).is_none()
}

pub fn timeout_error_message(path: &Path, timeout_secs: u64) -> String {
    format!("example timed out after {}s: {}", timeout_secs, path.display())
}

pub fn is_timeout_error(message: &str) -> bool {
    let lower = message.to_ascii_lowercase();
    lower.contains("timeout exceeded") || lower.contains("timed out") || lower.contains("e3005")
}

pub struct ExamplesWatchdogGuard {
    active: bool,
}

impl ExamplesWatchdogGuard {
    pub fn for_path(path: &Path) -> Self {
        if should_apply_examples_timeout(path) {
            start_watchdog(examples_timeout_secs());
            Self { active: true }
        } else {
            Self { active: false }
        }
    }

    pub fn is_active(&self) -> bool {
        self.active
    }

    pub fn timeout_secs(&self) -> u64 {
        examples_timeout_secs()
    }
}

pub fn run_isolated_example_file(path: &Path, gc_log: bool, gc_off: bool, args: &[String]) -> Option<i32> {
    if !should_isolate_example_process(path) {
        return None;
    }

    let exe = match std::env::current_exe() {
        Ok(path) => path,
        Err(err) => {
            eprintln!("error: failed to resolve current executable: {}", err);
            return Some(1);
        }
    };

    let mut cmd = Command::new(exe);
    cmd.env(EXAMPLES_CHILD_ENV, "1")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());

    if gc_log {
        cmd.arg("--gc-log");
    }
    if gc_off {
        cmd.arg("--gc=off");
    }

    cmd.arg(path);
    for arg in args.iter().skip(1) {
        cmd.arg(arg);
    }

    let timeout_secs = examples_timeout_secs();
    Some(run_child_with_timeout(
        cmd,
        path,
        Duration::from_secs(timeout_secs),
        timeout_secs,
    ))
}

fn run_child_with_timeout(mut cmd: Command, path: &Path, timeout: Duration, timeout_secs: u64) -> i32 {
    let mut child = match cmd.spawn() {
        Ok(child) => child,
        Err(err) => {
            eprintln!("error: failed to start example: {}", err);
            return 1;
        }
    };

    let start = Instant::now();
    let mut timed_out = false;
    loop {
        match child.try_wait() {
            Ok(Some(_)) => break,
            Ok(None) => {
                if start.elapsed() >= timeout {
                    timed_out = true;
                    let _ = child.kill();
                    break;
                }
                thread::sleep(Duration::from_millis(100));
            }
            Err(err) => {
                eprintln!("error: failed while waiting for example: {}", err);
                let _ = child.kill();
                return 1;
            }
        }
    }

    let output = match child.wait_with_output() {
        Ok(output) => output,
        Err(err) => {
            eprintln!("error: failed to collect example output: {}", err);
            return 1;
        }
    };

    if !output.stdout.is_empty() {
        print!("{}", String::from_utf8_lossy(&output.stdout));
    }
    if !output.stderr.is_empty() {
        eprint!("{}", String::from_utf8_lossy(&output.stderr));
    }

    if timed_out {
        eprintln!("error: {}", timeout_error_message(path, timeout_secs));
        return 1;
    }

    output.status.code().unwrap_or(101)
}

impl Drop for ExamplesWatchdogGuard {
    fn drop(&mut self) {
        if self.active {
            stop_watchdog();
            reset_timeout();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::OsString;
    use std::path::PathBuf;
    use std::sync::{Mutex, OnceLock};

    fn env_lock() -> &'static Mutex<()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
    }

    struct EnvVarGuard {
        key: &'static str,
        previous: Option<OsString>,
    }

    impl EnvVarGuard {
        fn clear(key: &'static str) -> Self {
            let previous = std::env::var_os(key);
            std::env::remove_var(key);
            Self { key, previous }
        }

        fn set(key: &'static str, value: &str) -> Self {
            let previous = std::env::var_os(key);
            std::env::set_var(key, value);
            Self { key, previous }
        }
    }

    impl Drop for EnvVarGuard {
        fn drop(&mut self) {
            match &self.previous {
                Some(value) => std::env::set_var(self.key, value),
                None => std::env::remove_var(self.key),
            }
        }
    }

    #[test]
    fn detects_examples_paths() {
        assert!(is_examples_path(&PathBuf::from(
            "examples/03_concurrency/async_basics.spl"
        )));
        assert!(is_examples_path(&PathBuf::from(
            "/tmp/worktree/examples/03_concurrency/async_basics.spl"
        )));
        assert!(!is_examples_path(&PathBuf::from("src/app/main.spl")));
    }

    #[test]
    fn default_timeout_is_repo_defined_when_env_missing() {
        let _lock = env_lock().lock().expect("lock");
        let _env = EnvVarGuard::clear("SIMPLE_TIMEOUT_SECONDS");
        assert_eq!(examples_timeout_secs(), DEFAULT_EXAMPLES_TIMEOUT_SECS);
    }

    #[test]
    fn env_timeout_override_is_respected() {
        let _lock = env_lock().lock().expect("lock");
        let _env = EnvVarGuard::set("SIMPLE_TIMEOUT_SECONDS", "17");
        assert_eq!(examples_timeout_secs(), 17);
    }

    #[test]
    fn timeout_detection_matches_common_messages() {
        assert!(is_timeout_error("compile failed: timeout exceeded"));
        assert!(is_timeout_error("Runtime error E3005: timed out"));
        assert!(!is_timeout_error("parse error: expected identifier"));
    }
}

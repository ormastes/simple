//! Shared safety policy for direct execution and compilation of example files.

use std::io::Read as _;
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

fn examples_timeout_disabled() -> bool {
    std::env::var("SIMPLE_TIMEOUT_SECONDS")
        .ok()
        .and_then(|value| value.parse::<u64>().ok())
        == Some(0)
}

fn should_apply_examples_timeout(path: &Path) -> bool {
    is_examples_path(path) && std::env::var_os("SIMPLE_TIMEOUT_SECONDS").is_none()
}

fn should_isolate_example_process(path: &Path) -> bool {
    is_examples_path(path) && std::env::var_os(EXAMPLES_CHILD_ENV).is_none() && !examples_timeout_disabled()
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

fn spawn_pipe_tee<R, W>(mut pipe: R, mut writer: W) -> thread::JoinHandle<()>
where
    R: std::io::Read + Send + 'static,
    W: std::io::Write + Send + 'static,
{
    thread::spawn(move || {
        let mut buf = [0; 8192];
        loop {
            match pipe.read(&mut buf) {
                Ok(0) => break,
                Ok(n) => {
                    let _ = writer.write_all(&buf[..n]);
                    let _ = writer.flush();
                }
                Err(err) if err.kind() == std::io::ErrorKind::Interrupted => continue,
                Err(_) => break,
            }
        }
    })
}

fn run_child_with_timeout(mut cmd: Command, path: &Path, timeout: Duration, timeout_secs: u64) -> i32 {
    run_child_with_timeout_and_writers(cmd, path, timeout, timeout_secs, std::io::stdout(), std::io::stderr())
}

fn run_child_with_timeout_and_writers<WOut, WErr>(
    mut cmd: Command,
    path: &Path,
    timeout: Duration,
    timeout_secs: u64,
    stdout_writer: WOut,
    stderr_writer: WErr,
) -> i32
where
    WOut: std::io::Write + Send + 'static,
    WErr: std::io::Write + Send + 'static,
{
    let mut child = match cmd.spawn() {
        Ok(child) => child,
        Err(err) => {
            eprintln!("error: failed to start example: {}", err);
            return 1;
        }
    };

    // Tee both pipes to the parent on dedicated threads while the timeout loop
    // polls the child. Continuing to drain after a parent write fails prevents
    // a full pipe from blocking the child and deadlocking the timeout path.
    let stdout_handle = child.stdout.take().map(|pipe| spawn_pipe_tee(pipe, stdout_writer));
    let stderr_handle = child.stderr.take().map(|pipe| spawn_pipe_tee(pipe, stderr_writer));

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

    let _ = stdout_handle.map(|handle| handle.join());
    let _ = stderr_handle.map(|handle| handle.join());

    let status = match child.wait() {
        Ok(status) => status,
        Err(err) => {
            eprintln!("error: failed to collect example output: {}", err);
            return 1;
        }
    };

    if timed_out {
        eprintln!("error: {}", timeout_error_message(path, timeout_secs));
        return 1;
    }

    status.code().unwrap_or(101)
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
    use std::io::Write as _;
    use std::path::PathBuf;
    use std::sync::{Arc, Condvar, Mutex, OnceLock};

    const TEST_CHILD_ENV: &str = "SIMPLE_DRIVER_EXAMPLES_SAFETY_TEST_CHILD";
    const CHILD_STDOUT: &[u8] = b"examples child stdout marker\n";
    const CHILD_STDERR: &[u8] = b"examples child stderr marker\n";

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

    #[derive(Clone, Default)]
    struct SharedWriter {
        bytes: Arc<Mutex<Vec<u8>>>,
        ready: Arc<Condvar>,
    }

    impl SharedWriter {
        fn bytes(&self) -> Vec<u8> {
            self.bytes.lock().expect("shared output").clone()
        }

        fn wait_for(&self, expected: &[u8]) -> bool {
            let deadline = Instant::now() + Duration::from_secs(10);
            let mut bytes = self.bytes.lock().expect("shared output");
            while !contains(&bytes, expected) {
                let remaining = deadline.saturating_duration_since(Instant::now());
                if remaining.is_zero() {
                    return false;
                }
                let (next, result) = self.ready.wait_timeout(bytes, remaining).expect("shared output wait");
                bytes = next;
                if result.timed_out() {
                    break;
                }
            }
            contains(&bytes, expected)
        }
    }

    impl std::io::Write for SharedWriter {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            self.bytes.lock().expect("shared output").extend_from_slice(buf);
            self.ready.notify_all();
            Ok(buf.len())
        }

        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    fn contains(bytes: &[u8], expected: &[u8]) -> bool {
        bytes.windows(expected.len()).any(|window| window == expected)
    }

    fn process_command(mode: &str) -> Command {
        let mut cmd = Command::new(std::env::current_exe().expect("current test executable"));
        cmd.env(TEST_CHILD_ENV, mode)
            .arg("examples_safety_process_test_child")
            .arg("--test-threads=1")
            .arg("--nocapture")
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
        cmd
    }

    fn assert_routed_output(stdout: &SharedWriter, stderr: &SharedWriter) {
        let stdout_bytes = stdout.bytes();
        let stderr_bytes = stderr.bytes();
        assert!(
            contains(&stdout_bytes, CHILD_STDOUT),
            "stdout missing marker: {}",
            String::from_utf8_lossy(&stdout_bytes)
        );
        assert!(
            contains(&stderr_bytes, CHILD_STDERR),
            "stderr missing marker: {}",
            String::from_utf8_lossy(&stderr_bytes)
        );
        assert!(!contains(&stdout_bytes, CHILD_STDERR));
        assert!(!contains(&stderr_bytes, CHILD_STDOUT));
    }

    #[test]
    fn examples_safety_process_test_child() {
        let Ok(mode) = std::env::var(TEST_CHILD_ENV) else {
            return;
        };

        let mut stdout = std::io::stdout();
        stdout.write_all(CHILD_STDOUT).expect("child stdout");
        stdout.flush().expect("child stdout flush");
        let mut stderr = std::io::stderr();
        stderr.write_all(CHILD_STDERR).expect("child stderr");
        stderr.flush().expect("child stderr flush");

        match mode.as_str() {
            "sleep" => thread::sleep(Duration::from_secs(60)),
            "exit-23" => std::process::exit(23),
            _ => panic!("unknown process test mode: {}", mode),
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
    fn zero_timeout_disables_example_isolation_watchdog() {
        let _lock = env_lock().lock().expect("lock");
        let _timeout_env = EnvVarGuard::set("SIMPLE_TIMEOUT_SECONDS", "0");
        let _child_env = EnvVarGuard::clear(EXAMPLES_CHILD_ENV);
        assert!(!should_isolate_example_process(&PathBuf::from(
            "examples/ui/simple_browser.spl"
        )));
    }

    #[test]
    fn timeout_detection_matches_common_messages() {
        assert!(is_timeout_error("compile failed: timeout exceeded"));
        assert!(is_timeout_error("Runtime error E3005: timed out"));
        assert!(!is_timeout_error("parse error: expected identifier"));
    }

    #[test]
    fn pipe_tee_streams_real_process_output_before_kill() {
        let mut child = process_command("sleep").spawn().expect("spawn child");
        let stdout = SharedWriter::default();
        let stderr = SharedWriter::default();
        let stdout_handle = spawn_pipe_tee(child.stdout.take().expect("child stdout"), stdout.clone());
        let stderr_handle = spawn_pipe_tee(child.stderr.take().expect("child stderr"), stderr.clone());

        let stdout_seen = stdout.wait_for(CHILD_STDOUT);
        let stderr_seen = stderr.wait_for(CHILD_STDERR);
        let child_was_running = child.try_wait().expect("child status").is_none();
        let _ = child.kill();
        let _ = child.wait();
        stdout_handle.join().expect("stdout tee");
        stderr_handle.join().expect("stderr tee");

        assert!(stdout_seen, "stdout was not streamed before kill");
        assert!(stderr_seen, "stderr was not streamed before kill");
        assert!(child_was_running, "child exited before output was observed");
        assert_routed_output(&stdout, &stderr);
    }

    #[test]
    fn timeout_kills_real_process_and_retains_routed_output() {
        let stdout = SharedWriter::default();
        let stderr = SharedWriter::default();
        let status = run_child_with_timeout_and_writers(
            process_command("sleep"),
            Path::new("examples/timeout_test.spl"),
            Duration::from_secs(5),
            5,
            stdout.clone(),
            stderr.clone(),
        );

        assert_eq!(status, 1);
        assert_routed_output(&stdout, &stderr);
    }

    #[test]
    fn normal_real_process_retains_output_and_exit_status() {
        let stdout = SharedWriter::default();
        let stderr = SharedWriter::default();
        let status = run_child_with_timeout_and_writers(
            process_command("exit-23"),
            Path::new("examples/normal_test.spl"),
            Duration::from_secs(30),
            30,
            stdout.clone(),
            stderr.clone(),
        );

        assert_eq!(status, 23);
        assert_routed_output(&stdout, &stderr);
    }
}

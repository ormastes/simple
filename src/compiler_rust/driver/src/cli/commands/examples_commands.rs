//! Examples validation command handlers.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::thread;
use std::time::{Duration, Instant};

#[derive(Debug, Clone)]
struct ExamplesCheckConfig {
    root: PathBuf,
    timeout: Duration,
    run_mode: bool,
    report_path: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CheckKind {
    Ok,
    Error,
    Timeout,
    Crash,
}

#[derive(Debug, Clone)]
struct CheckResult {
    kind: CheckKind,
    code: Option<i32>,
    preview: String,
}

#[derive(Debug, Clone)]
struct ExampleGroup {
    label: String,
    files: Vec<PathBuf>,
}

#[derive(Debug, Clone, Default)]
struct GroupStats {
    total: usize,
    ok: usize,
    error: usize,
    timeout: usize,
    crash: usize,
}

impl GroupStats {
    fn record(&mut self, kind: &CheckKind) {
        self.total += 1;
        match kind {
            CheckKind::Ok => self.ok += 1,
            CheckKind::Error => self.error += 1,
            CheckKind::Timeout => self.timeout += 1,
            CheckKind::Crash => self.crash += 1,
        }
    }

    fn has_failures(&self) -> bool {
        self.error > 0 || self.timeout > 0 || self.crash > 0
    }
}

pub fn handle_examples_check(args: &[String]) -> i32 {
    let config = match parse_examples_check_args(args) {
        Ok(config) => config,
        Err(message) => {
            if message.is_empty() {
                print_examples_check_help();
                return 0;
            }
            eprintln!("error: {}", message);
            eprintln!();
            print_examples_check_help();
            return 1;
        }
    };

    let exe = match std::env::current_exe() {
        Ok(path) => path,
        Err(err) => {
            eprintln!("error: failed to resolve current executable: {}", err);
            return 1;
        }
    };

    let groups = match collect_example_groups(&config.root) {
        Ok(groups) => groups,
        Err(err) => {
            eprintln!("error: {}", err);
            return 1;
        }
    };

    let temp_dir = match tempfile::tempdir() {
        Ok(dir) => dir,
        Err(err) => {
            eprintln!("error: failed to create temp dir: {}", err);
            return 1;
        }
    };

    let mut total_stats = GroupStats::default();
    let mut report = ExamplesReport::new(config.clone());
    report.push_header();

    for group in groups {
        println!("=== {} ===", group.label);
        let mut group_stats = GroupStats::default();
        let mut failures: Vec<(PathBuf, CheckResult)> = Vec::new();

        for (idx, file) in group.files.iter().enumerate() {
            let result = run_example_check(&exe, file, idx, &config, temp_dir.path());
            group_stats.record(&result.kind);
            total_stats.record(&result.kind);
            if result.kind != CheckKind::Ok {
                failures.push((file.clone(), result));
            }
        }

        print_group_summary(&group.label, &group_stats);
        print_group_failures(&group.label, &failures);
        report.push_group(&group.label, &group_stats, &failures);
        println!();
    }

    print_summary(&total_stats, &config.report_path);
    if let Err(err) = report.write() {
        eprintln!("error: failed to write report {}: {}", config.report_path.display(), err);
        return 1;
    }

    if total_stats.has_failures() {
        1
    } else {
        0
    }
}

fn parse_examples_check_args(args: &[String]) -> Result<ExamplesCheckConfig, String> {
    let mut root = PathBuf::from("examples");
    let mut timeout_secs = 10u64;
    let mut run_mode = false;
    let mut report_path = PathBuf::from("doc/09_report/session/examples_check_latest.md");

    let mut i = 1usize;
    while i < args.len() {
        match args[i].as_str() {
            "-h" | "--help" => return Err(String::new()),
            "--run" => run_mode = true,
            "--compile" => run_mode = false,
            "--timeout" => {
                let Some(value) = args.get(i + 1) else {
                    return Err("--timeout requires a number".to_string());
                };
                timeout_secs = value
                    .parse::<u64>()
                    .map_err(|_| "--timeout requires a positive integer".to_string())?;
                i += 1;
            }
            other if other.starts_with("--timeout=") => {
                let value = other.trim_start_matches("--timeout=");
                timeout_secs = value
                    .parse::<u64>()
                    .map_err(|_| "--timeout requires a positive integer".to_string())?;
            }
            "--report" => {
                let Some(value) = args.get(i + 1) else {
                    return Err("--report requires a path".to_string());
                };
                report_path = PathBuf::from(value);
                i += 1;
            }
            other if other.starts_with("--report=") => {
                let value = other.trim_start_matches("--report=");
                report_path = PathBuf::from(value);
            }
            other if other.starts_with('-') => {
                return Err(format!("unknown option '{}'", other));
            }
            other => root = PathBuf::from(other),
        }
        i += 1;
    }

    Ok(ExamplesCheckConfig {
        root,
        timeout: Duration::from_secs(timeout_secs.max(1)),
        run_mode,
        report_path,
    })
}

fn collect_example_groups(root: &Path) -> Result<Vec<ExampleGroup>, String> {
    if !root.exists() {
        return Err(format!("path not found: {}", root.display()));
    }

    if root.is_file() {
        return Ok(vec![ExampleGroup {
            label: root.display().to_string(),
            files: vec![root.to_path_buf()],
        }]);
    }

    let mut child_dirs: Vec<PathBuf> = fs::read_dir(root)
        .map_err(|e| format!("failed to read {}: {}", root.display(), e))?
        .filter_map(|entry| entry.ok().map(|e| e.path()))
        .filter(|path| path.is_dir() && !is_hidden(path))
        .collect();
    child_dirs.sort();

    if root.file_name().and_then(|s| s.to_str()) == Some("examples") && !child_dirs.is_empty() {
        let mut groups = Vec::new();
        for dir in child_dirs {
            let files = collect_spl_files(&dir)?;
            if !files.is_empty() {
                groups.push(ExampleGroup {
                    label: dir.display().to_string(),
                    files,
                });
            }
        }
        return Ok(groups);
    }

    Ok(vec![ExampleGroup {
        label: root.display().to_string(),
        files: collect_spl_files(root)?,
    }])
}

fn collect_spl_files(root: &Path) -> Result<Vec<PathBuf>, String> {
    let mut files = Vec::new();
    collect_spl_files_into(root, &mut files)?;
    files.sort();
    Ok(files)
}

fn collect_spl_files_into(root: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
    for entry in fs::read_dir(root).map_err(|e| format!("failed to read {}: {}", root.display(), e))? {
        let path = entry
            .map_err(|e| format!("failed to read {}: {}", root.display(), e))?
            .path();
        if is_hidden(&path) {
            continue;
        }
        if path.is_dir() {
            collect_spl_files_into(&path, files)?;
        } else if path.extension().and_then(|s| s.to_str()) == Some("spl") {
            files.push(path);
        }
    }
    Ok(())
}

fn run_example_check(
    exe: &Path,
    file: &Path,
    idx: usize,
    config: &ExamplesCheckConfig,
    temp_root: &Path,
) -> CheckResult {
    let mut cmd = Command::new(exe);
    if config.run_mode {
        cmd.arg(file);
    } else {
        let out = temp_root.join(format!("example_check_{}.smf", idx));
        cmd.arg("compile")
            .arg(file)
            .arg("-o")
            .arg(out)
            .env("SIMPLE_COMPILE_RUST", "1");
    }

    let mut child = match cmd.stdout(Stdio::piped()).stderr(Stdio::piped()).spawn() {
        Ok(child) => child,
        Err(err) => {
            return CheckResult {
                kind: CheckKind::Crash,
                code: None,
                preview: format!("spawn failed: {}", err),
            };
        }
    };

    let start = Instant::now();
    let mut timed_out = false;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break Some(status),
            Ok(None) => {
                if start.elapsed() >= config.timeout {
                    timed_out = true;
                    let _ = child.kill();
                    break None;
                }
                thread::sleep(Duration::from_millis(100));
            }
            Err(err) => {
                return CheckResult {
                    kind: CheckKind::Crash,
                    code: None,
                    preview: format!("wait failed: {}", err),
                };
            }
        }
    };

    let output = match child.wait_with_output() {
        Ok(output) => output,
        Err(err) => {
            return CheckResult {
                kind: if timed_out {
                    CheckKind::Timeout
                } else {
                    CheckKind::Crash
                },
                code: None,
                preview: format!("output capture failed: {}", err),
            };
        }
    };

    if timed_out {
        return CheckResult {
            kind: CheckKind::Timeout,
            code: None,
            preview: preview_output(&output.stdout, &output.stderr, "timed out"),
        };
    }

    classify_status(status.expect("status set when not timed out"), &output)
}

fn classify_status(status: ExitStatus, output: &std::process::Output) -> CheckResult {
    if status.success() {
        return CheckResult {
            kind: CheckKind::Ok,
            code: status.code(),
            preview: String::new(),
        };
    }

    let code = status.code();
    let kind = match code {
        Some(1) => CheckKind::Error,
        Some(_) => CheckKind::Crash,
        None => CheckKind::Crash,
    };

    CheckResult {
        kind,
        code,
        preview: preview_output(&output.stdout, &output.stderr, "failed without diagnostics"),
    }
}

fn print_group_summary(label: &str, stats: &GroupStats) {
    println!(
        "SUMMARY {} total={} ok={} error={} timeout={} crash={}",
        label,
        stats.total,
        stats.ok,
        stats.error,
        stats.timeout,
        stats.crash
    );
}

fn print_group_failures(label: &str, failures: &[(PathBuf, CheckResult)]) {
    for (file, result) in failures {
        let code_text = result
            .code
            .map(|c| c.to_string())
            .unwrap_or_else(|| "signal".to_string());
        println!(
            "FAIL {} {} code={} {}",
            label,
            file.display(),
            code_text,
            result.preview
        );
    }
}

fn print_summary(stats: &GroupStats, report_path: &Path) {
    println!(
        "SUMMARY total={} ok={} error={} timeout={} crash={}",
        stats.total, stats.ok, stats.error, stats.timeout, stats.crash
    );
    println!("Report: {}", report_path.display());
}

struct ExamplesReport {
    path: PathBuf,
    content: String,
}

impl ExamplesReport {
    fn new(config: ExamplesCheckConfig) -> Self {
        Self {
            path: config.report_path,
            content: String::new(),
        }
    }

    fn push_header(&mut self) {
        self.content.push_str("# Examples Check\n\n");
    }

    fn push_group(&mut self, label: &str, stats: &GroupStats, failures: &[(PathBuf, CheckResult)]) {
        self.content.push_str(&format!("## {}\n\n", label));
        self.content.push_str(&format!("- Total: `{}`\n", stats.total));
        self.content.push_str(&format!("- Ok: `{}`\n", stats.ok));
        self.content.push_str(&format!("- Error: `{}`\n", stats.error));
        self.content.push_str(&format!("- Timeout: `{}`\n", stats.timeout));
        self.content.push_str(&format!("- Crash: `{}`\n", stats.crash));
        if failures.is_empty() {
            self.content.push_str("\nAll files passed.\n\n");
            return;
        }

        self.content.push_str("\n### Failures\n\n");
        for (file, result) in failures {
            let code_text = result
                .code
                .map(|c| c.to_string())
                .unwrap_or_else(|| "signal".to_string());
            self.content.push_str(&format!(
                "- `{}` `{}` code={} {}\n",
                file.display(),
                kind_label(&result.kind),
                code_text,
                result.preview
            ));
        }
        self.content.push('\n');
    }

    fn write(&self) -> Result<(), std::io::Error> {
        if let Some(parent) = self.path.parent() {
            fs::create_dir_all(parent)?;
        }
        fs::write(&self.path, &self.content)
    }
}

fn preview_output(stdout: &[u8], stderr: &[u8], fallback: &str) -> String {
    let stderr_text = String::from_utf8_lossy(stderr);
    if let Some(line) = stderr_text.lines().find(|line| !line.trim().is_empty()) {
        return line.trim().to_string();
    }
    let stdout_text = String::from_utf8_lossy(stdout);
    if let Some(line) = stdout_text.lines().find(|line| !line.trim().is_empty()) {
        return line.trim().to_string();
    }
    fallback.to_string()
}

fn kind_label(kind: &CheckKind) -> &'static str {
    match kind {
        CheckKind::Ok => "ok",
        CheckKind::Error => "error",
        CheckKind::Timeout => "timeout",
        CheckKind::Crash => "crash",
    }
}

fn is_hidden(path: &Path) -> bool {
    path.file_name()
        .and_then(|name| name.to_str())
        .map(|name| name.starts_with('.'))
        .unwrap_or(false)
}

fn print_examples_check_help() {
    eprintln!("Validate examples with isolation and timeout containment.");
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  simple examples-check [path] [--compile|--run] [--timeout <secs>]");
    eprintln!("  simple examples-check [path] [--compile|--run] [--timeout <secs>] [--report <path>]");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  --compile         Compile each example in a child process (default)");
    eprintln!("  --run             Run each example in a child process");
    eprintln!("  --timeout <secs>  Wall-clock timeout per file (default: 10)");
    eprintln!("  --report <path>   Markdown report output path");
    eprintln!("  -h, --help        Show this help");
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Output;

    #[cfg(unix)]
    use std::os::unix::process::ExitStatusExt;

    #[test]
    fn parse_examples_check_defaults() {
        let config = parse_examples_check_args(&["examples-check".to_string()]).expect("parse");
        assert_eq!(config.root, PathBuf::from("examples"));
        assert_eq!(config.timeout, Duration::from_secs(10));
        assert!(!config.run_mode);
        assert_eq!(
            config.report_path,
            PathBuf::from("doc/09_report/session/examples_check_latest.md")
        );
    }

    #[test]
    fn parse_examples_check_custom_values() {
        let config = parse_examples_check_args(&[
            "examples-check".to_string(),
            "examples/02_language_features".to_string(),
            "--run".to_string(),
            "--timeout=7".to_string(),
        ])
        .expect("parse");
        assert_eq!(config.root, PathBuf::from("examples/02_language_features"));
        assert_eq!(config.timeout, Duration::from_secs(7));
        assert!(config.run_mode);
    }

    #[test]
    fn parse_examples_check_report_path() {
        let config = parse_examples_check_args(&[
            "examples-check".to_string(),
            "examples".to_string(),
            "--report=tmp/examples_check.md".to_string(),
        ])
        .expect("parse");
        assert_eq!(config.report_path, PathBuf::from("tmp/examples_check.md"));
    }

    #[test]
    fn preview_prefers_stderr() {
        let preview = preview_output(b"stdout line\n", b"stderr line\n", "fallback");
        assert_eq!(preview, "stderr line");
    }

    #[cfg(unix)]
    #[test]
    fn classify_status_code_1_is_error() {
        let output = Output {
            status: std::process::ExitStatus::from_raw(1 << 8),
            stdout: Vec::new(),
            stderr: b"parse error".to_vec(),
        };
        let result = classify_status(output.status, &output);
        assert_eq!(result.kind, CheckKind::Error);
        assert_eq!(result.code, Some(1));
        assert_eq!(result.preview, "parse error");
    }

    #[cfg(unix)]
    #[test]
    fn classify_status_signal_is_crash() {
        let output = Output {
            status: std::process::ExitStatus::from_raw(11),
            stdout: Vec::new(),
            stderr: b"segfault".to_vec(),
        };
        let result = classify_status(output.status, &output);
        assert_eq!(result.kind, CheckKind::Crash);
        assert_eq!(result.code, None);
        assert_eq!(result.preview, "segfault");
    }
}

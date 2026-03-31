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

    let mut total_files = 0usize;
    let mut total_ok = 0usize;
    let mut total_failed = 0usize;

    for group in groups {
        println!("=== {} ===", group.label);
        let mut group_ok = 0usize;
        let mut first_failure: Option<(PathBuf, CheckResult)> = None;

        for (idx, file) in group.files.iter().enumerate() {
            total_files += 1;
            let result = run_example_check(&exe, file, idx, &config, temp_dir.path());
            if result.kind == CheckKind::Ok {
                group_ok += 1;
                total_ok += 1;
            } else if first_failure.is_none() {
                total_failed += 1;
                first_failure = Some((file.clone(), result));
            }
        }

        if let Some((file, result)) = first_failure {
            let code_text = result
                .code
                .map(|c| c.to_string())
                .unwrap_or_else(|| "signal".to_string());
            println!(
                "FIRST_FAIL {} {} code={} {}",
                kind_label(&result.kind),
                file.display(),
                code_text,
                result.preview
            );
        } else {
            println!("OK all {} files", group_ok);
        }
        println!();
    }

    println!("SUMMARY total={} ok={} failed={}", total_files, total_ok, total_failed);

    if total_failed == 0 {
        0
    } else {
        1
    }
}

fn parse_examples_check_args(args: &[String]) -> Result<ExamplesCheckConfig, String> {
    let mut root = PathBuf::from("examples");
    let mut timeout_secs = 10u64;
    let mut run_mode = false;

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
    eprintln!();
    eprintln!("Options:");
    eprintln!("  --compile         Compile each example in a child process (default)");
    eprintln!("  --run             Run each example in a child process");
    eprintln!("  --timeout <secs>  Wall-clock timeout per file (default: 10)");
    eprintln!("  -h, --help        Show this help");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_examples_check_defaults() {
        let config = parse_examples_check_args(&["examples-check".to_string()]).expect("parse");
        assert_eq!(config.root, PathBuf::from("examples"));
        assert_eq!(config.timeout, Duration::from_secs(10));
        assert!(!config.run_mode);
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
    fn preview_prefers_stderr() {
        let preview = preview_output(b"stdout line\n", b"stderr line\n", "fallback");
        assert_eq!(preview, "stderr line");
    }
}

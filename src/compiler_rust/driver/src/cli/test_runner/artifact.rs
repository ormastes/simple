//! Per-test artifact emission.

use std::fs;
use std::path::{Path, PathBuf};

use serde::Serialize;

use super::types::{IndividualTestResult, TestFileResult};

const ARTIFACT_ROOT: &str = "build/test-artifacts";

pub struct ExecutionArtifacts<'a> {
    pub stdout: Option<&'a str>,
    pub stderr: Option<&'a str>,
    pub combined: Option<&'a str>,
    pub log_note: Option<&'a str>,
}

impl<'a> ExecutionArtifacts<'a> {
    pub fn none() -> Self {
        Self {
            stdout: None,
            stderr: None,
            combined: None,
            log_note: None,
        }
    }
}

pub fn write_test_artifacts(
    source_path: &Path,
    result: &TestFileResult,
    artifacts: ExecutionArtifacts<'_>,
) -> Result<PathBuf, String> {
    let output_dir = artifact_dir_for_path(source_path);
    fs::create_dir_all(&output_dir)
        .map_err(|e| format!("failed to create artifact dir {}: {}", output_dir.display(), e))?;

    let summary_path = output_dir.join("summary.txt");
    fs::write(&summary_path, build_summary_text(source_path, result))
        .map_err(|e| format!("failed to write {}: {}", summary_path.display(), e))?;

    let log_path = output_dir.join("run.log");
    let log_content = build_log_text(result, &artifacts);
    fs::write(&log_path, &log_content).map_err(|e| format!("failed to write {}: {}", log_path.display(), e))?;

    if let Some(stdout) = artifacts.stdout {
        let stdout_path = output_dir.join("stdout.log");
        fs::write(&stdout_path, stdout).map_err(|e| format!("failed to write {}: {}", stdout_path.display(), e))?;
    }
    if let Some(stderr) = artifacts.stderr {
        let stderr_path = output_dir.join("stderr.log");
        fs::write(&stderr_path, stderr).map_err(|e| format!("failed to write {}: {}", stderr_path.display(), e))?;
    }
    if let Some(combined) = artifacts.combined {
        let combined_path = output_dir.join("combined.log");
        fs::write(&combined_path, combined)
            .map_err(|e| format!("failed to write {}: {}", combined_path.display(), e))?;
    }

    let output_path = output_dir.join("output.log");
    fs::write(&output_path, &log_content).map_err(|e| format!("failed to write {}: {}", output_path.display(), e))?;

    write_result_json_at_dir(source_path, result, &output_dir)?;

    Ok(output_dir)
}

pub fn write_result_json(source_path: &Path, result: &TestFileResult) -> Result<PathBuf, String> {
    let output_dir = artifact_dir_for_path(source_path);
    fs::create_dir_all(&output_dir)
        .map_err(|e| format!("failed to create artifact dir {}: {}", output_dir.display(), e))?;
    write_result_json_at_dir(source_path, result, &output_dir)?;
    Ok(output_dir)
}

fn build_summary_text(source_path: &Path, result: &TestFileResult) -> String {
    let mut lines = vec![
        format!("Source: {}", source_path.display()),
        format!("Artifact Directory: {}", artifact_dir_for_path(source_path).display()),
        format!("Passed: {}", result.passed),
        format!("Failed: {}", result.failed),
        format!("Skipped: {}", result.skipped),
        format!("Ignored: {}", result.ignored),
        format!("DurationMs: {}", result.duration_ms),
        format!("Status: {}", if result.failed == 0 { "passed" } else { "failed" }),
    ];

    if let Some(error) = &result.error {
        lines.push(format!("Error: {}", error));
    }

    lines.push(String::new());
    lines.push("Individual Results:".to_string());

    if result.individual_results.is_empty() {
        lines.push("- none captured".to_string());
    } else {
        for item in &result.individual_results {
            lines.push(format!("- {}", format_individual_result(item)));
        }
    }

    lines.join("\n")
}

fn build_log_text(result: &TestFileResult, artifacts: &ExecutionArtifacts<'_>) -> String {
    if let Some(combined) = artifacts.combined {
        return combined.to_string();
    }

    let mut lines = Vec::new();
    if let Some(note) = artifacts.log_note {
        lines.push(note.to_string());
    } else {
        lines.push("No captured runner output available for this execution path.".to_string());
    }
    lines.push(String::new());
    lines.push(format!("passed={}", result.passed));
    lines.push(format!("failed={}", result.failed));
    lines.push(format!("skipped={}", result.skipped));
    lines.push(format!("ignored={}", result.ignored));
    lines.push(format!("duration_ms={}", result.duration_ms));
    if let Some(error) = &result.error {
        lines.push(format!("error={}", error));
    }
    lines.join("\n")
}

fn write_result_json_at_dir(source_path: &Path, result: &TestFileResult, output_dir: &Path) -> Result<(), String> {
    let result_json_path = output_dir.join("result.json");
    let result_json = ResultJson::from_parts(source_path, result, output_dir);
    let json = serde_json::to_string_pretty(&result_json)
        .map_err(|e| format!("failed to serialize {}: {}", result_json_path.display(), e))?;
    fs::write(&result_json_path, json).map_err(|e| format!("failed to write {}: {}", result_json_path.display(), e))?;
    Ok(())
}

fn format_individual_result(item: &IndividualTestResult) -> String {
    let status = if item.skipped {
        "SKIP"
    } else if item.passed {
        "PASS"
    } else {
        "FAIL"
    };

    if item.group.is_empty() {
        format!("{} {}", status, item.name)
    } else {
        format!("{} {} > {}", status, item.group, item.name)
    }
}

fn artifact_dir_for_path(source_path: &Path) -> PathBuf {
    PathBuf::from(ARTIFACT_ROOT).join(spec_relative_dir(source_path))
}

fn spec_relative_dir(source_path: &Path) -> PathBuf {
    let mut components = source_path.components();
    let mut relative_parts: Vec<String> = Vec::new();
    let mut found_test_root = false;

    while let Some(component) = components.next() {
        let part = component.as_os_str().to_string_lossy();
        if found_test_root {
            relative_parts.push(part.to_string());
        } else if part == "test" {
            found_test_root = true;
        }
    }

    if relative_parts.is_empty() {
        let stem = source_path.file_stem().and_then(|s| s.to_str()).unwrap_or("spec");
        return PathBuf::from(strip_test_suffix(stem));
    }

    if let Some(last) = relative_parts.pop() {
        let last_stem = Path::new(&last)
            .file_stem()
            .and_then(|s| s.to_str())
            .map(strip_test_suffix)
            .unwrap_or(last);
        relative_parts.push(last_stem);
    }

    let mut relative = PathBuf::new();
    for part in relative_parts {
        relative.push(part);
    }
    relative
}

fn strip_test_suffix(stem: &str) -> String {
    stem.strip_suffix("_spec")
        .or_else(|| stem.strip_suffix("_test"))
        .unwrap_or(stem)
        .to_string()
}

#[derive(Debug, Serialize)]
struct ResultJson<'a> {
    schema_version: u8,
    source_path: PathBuf,
    artifact_directory: PathBuf,
    status: &'a str,
    counts: ResultCounts,
    error: Option<&'a str>,
    individual_results: &'a [IndividualTestResult],
    artifacts: ResultArtifacts,
}

#[derive(Debug, Serialize)]
struct ResultCounts {
    passed: usize,
    failed: usize,
    skipped: usize,
    ignored: usize,
    duration_ms: u64,
}

#[derive(Debug, Serialize)]
struct ResultArtifacts {
    summary_txt: PathBuf,
    result_json: PathBuf,
    run_log: Option<PathBuf>,
    output_log: Option<PathBuf>,
    stdout_log: Option<PathBuf>,
    stderr_log: Option<PathBuf>,
    combined_log: Option<PathBuf>,
}

impl<'a> ResultJson<'a> {
    fn from_parts(source_path: &Path, result: &'a TestFileResult, output_dir: &Path) -> Self {
        let status = if result.failed == 0 { "passed" } else { "failed" };
        Self {
            schema_version: 1,
            source_path: source_path.to_path_buf(),
            artifact_directory: output_dir.to_path_buf(),
            status,
            counts: ResultCounts {
                passed: result.passed,
                failed: result.failed,
                skipped: result.skipped,
                ignored: result.ignored,
                duration_ms: result.duration_ms,
            },
            error: result.error.as_deref(),
            individual_results: &result.individual_results,
            artifacts: ResultArtifacts {
                summary_txt: output_dir.join("summary.txt"),
                result_json: output_dir.join("result.json"),
                run_log: output_dir
                    .join("run.log")
                    .is_file()
                    .then_some(output_dir.join("run.log")),
                output_log: output_dir
                    .join("output.log")
                    .is_file()
                    .then_some(output_dir.join("output.log")),
                stdout_log: output_dir
                    .join("stdout.log")
                    .is_file()
                    .then_some(output_dir.join("stdout.log")),
                stderr_log: output_dir
                    .join("stderr.log")
                    .is_file()
                    .then_some(output_dir.join("stderr.log")),
                combined_log: output_dir
                    .join("combined.log")
                    .is_file()
                    .then_some(output_dir.join("combined.log")),
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spec_relative_dir_prefers_test_root() {
        let rel = spec_relative_dir(Path::new("test/app/web_dashboard/tmux_rest_api_spec.spl"));
        assert_eq!(
            rel.to_string_lossy().replace('\\', "/"),
            "app/web_dashboard/tmux_rest_api"
        );
    }

    #[test]
    fn test_build_summary_text_includes_counts() {
        let result = TestFileResult {
            path: PathBuf::from("test/example_spec.spl"),
            passed: 2,
            failed: 1,
            skipped: 0,
            ignored: 0,
            duration_ms: 42,
            error: Some("boom".to_string()),
            individual_results: vec![],
        };
        let summary = build_summary_text(Path::new("test/example_spec.spl"), &result);
        assert!(summary.contains("Passed: 2"));
        assert!(summary.contains("Error: boom"));
    }

    #[test]
    fn test_write_result_json_creates_manifest() {
        let temp_dir = tempfile::tempdir().expect("tempdir");
        let source_path = temp_dir.path().join("test/example_spec.spl");
        let result = TestFileResult {
            path: source_path.clone(),
            passed: 2,
            failed: 1,
            skipped: 0,
            ignored: 0,
            duration_ms: 42,
            error: Some("boom".to_string()),
            individual_results: vec![IndividualTestResult {
                name: "works".to_string(),
                group: "suite".to_string(),
                passed: true,
                skipped: false,
            }],
        };

        let output_dir = artifact_dir_for_path(&source_path);
        fs::create_dir_all(&output_dir).expect("create output dir");
        write_result_json_at_dir(&source_path, &result, &output_dir).expect("write json");

        let json_path = output_dir.join("result.json");
        let json = fs::read_to_string(&json_path).expect("read json");
        assert!(json.contains("\"schema_version\": 1"));
        assert!(json.contains("\"failed\": 1"));
        assert!(json.contains("\"works\""));
    }
}

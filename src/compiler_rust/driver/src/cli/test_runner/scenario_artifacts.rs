//! Scenario-scoped artifact naming and layout.
//!
//! This module defines a stable, additive layout for future per-scenario
//! captures without changing the existing per-test artifact files.

use std::fs;
use std::path::{Path, PathBuf};

use super::super::types::IndividualTestResult;

const ARTIFACT_ROOT: &str = "target/test-artifacts";
const SCENARIO_ROOT: &str = "scenarios";
const MANIFEST_FILE: &str = "manifest.txt";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ScenarioArtifactKind {
    Summary,
    RunLog,
    ResultJson,
    StdoutLog,
    StderrLog,
    CombinedLog,
    ScreenshotPng,
    TuiAnsi,
    TuiText,
}

impl ScenarioArtifactKind {
    pub(super) fn file_name(self) -> &'static str {
        match self {
            Self::Summary => "summary.txt",
            Self::RunLog => "run.log",
            Self::ResultJson => "result.json",
            Self::StdoutLog => "stdout.log",
            Self::StderrLog => "stderr.log",
            Self::CombinedLog => "combined.log",
            Self::ScreenshotPng => "screenshot.png",
            Self::TuiAnsi => "transcript.ansi",
            Self::TuiText => "transcript.txt",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ScenarioArtifactFile {
    pub kind: ScenarioArtifactKind,
    pub path: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ScenarioArtifactEntry {
    pub index: usize,
    pub group: String,
    pub name: String,
    pub display_name: String,
    pub slug: String,
    pub directory: PathBuf,
    pub artifacts: Vec<ScenarioArtifactFile>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct ScenarioArtifactPlan {
    pub spec_path: PathBuf,
    pub spec_root: PathBuf,
    pub scenario_root: PathBuf,
    pub entries: Vec<ScenarioArtifactEntry>,
}

pub(super) fn write_scenario_manifest(
    source_path: &Path,
    results: &[IndividualTestResult],
) -> Result<Option<PathBuf>, String> {
    if results.is_empty() {
        return Ok(None);
    }

    let plan = build_scenario_artifact_plan(source_path, results);
    fs::create_dir_all(&plan.scenario_root).map_err(|e| {
        format!(
            "failed to create scenario artifact root {}: {}",
            plan.scenario_root.display(),
            e
        )
    })?;

    for entry in &plan.entries {
        fs::create_dir_all(&entry.directory).map_err(|e| {
            format!(
                "failed to create scenario artifact dir {}: {}",
                entry.directory.display(),
                e
            )
        })?;
    }

    let manifest_path = plan.scenario_root.join(MANIFEST_FILE);
    fs::write(&manifest_path, build_manifest_text(&plan)).map_err(|e| {
        format!(
            "failed to write scenario manifest {}: {}",
            manifest_path.display(),
            e
        )
    })?;

    Ok(Some(manifest_path))
}

pub(super) fn build_scenario_artifact_plan(
    source_path: &Path,
    results: &[IndividualTestResult],
) -> ScenarioArtifactPlan {
    let spec_root = artifact_root_for_path(source_path);
    let scenario_root = spec_root.join(SCENARIO_ROOT);
    let mut entries = Vec::with_capacity(results.len());

    for (index, result) in results.iter().enumerate() {
        let slug = scenario_slug(index, result);
        let directory = scenario_root.join(format!("{:03}-{}", index + 1, slug));
        let artifacts = planned_artifacts(&directory);
        entries.push(ScenarioArtifactEntry {
            index: index + 1,
            group: result.group.clone(),
            name: result.name.clone(),
            display_name: scenario_display_name(result),
            slug,
            directory,
            artifacts,
        });
    }

    ScenarioArtifactPlan {
        spec_path: source_path.to_path_buf(),
        spec_root,
        scenario_root,
        entries,
    }
}

fn build_manifest_text(plan: &ScenarioArtifactPlan) -> String {
    let mut lines = vec![
        format!("spec: {}", plan.spec_path.display()),
        format!("spec_root: {}", plan.spec_root.display()),
        format!("scenario_root: {}", plan.scenario_root.display()),
        format!("scenario_count: {}", plan.entries.len()),
        String::new(),
    ];

    for entry in &plan.entries {
        lines.push(format!("[{}] {}", entry.index, entry.display_name));
        if !entry.group.is_empty() {
            lines.push(format!("group: {}", entry.group));
        }
        lines.push(format!("name: {}", entry.name));
        lines.push(format!("slug: {}", entry.slug));
        lines.push(format!("directory: {}", entry.directory.display()));
        lines.push("planned_artifacts:".to_string());
        for artifact in &entry.artifacts {
            lines.push(format!("- {} => {}", artifact.kind.file_name(), artifact.path.display()));
        }
        lines.push(String::new());
    }

    lines.join("\n")
}

fn planned_artifacts(directory: &Path) -> Vec<ScenarioArtifactFile> {
    [
        ScenarioArtifactKind::Summary,
        ScenarioArtifactKind::RunLog,
        ScenarioArtifactKind::ResultJson,
        ScenarioArtifactKind::StdoutLog,
        ScenarioArtifactKind::StderrLog,
        ScenarioArtifactKind::CombinedLog,
        ScenarioArtifactKind::ScreenshotPng,
        ScenarioArtifactKind::TuiAnsi,
        ScenarioArtifactKind::TuiText,
    ]
    .iter()
    .copied()
    .map(|kind| ScenarioArtifactFile {
        kind,
        path: directory.join(kind.file_name()),
    })
    .collect()
}

fn scenario_display_name(result: &IndividualTestResult) -> String {
    if result.group.is_empty() {
        result.name.clone()
    } else {
        format!("{} > {}", result.group, result.name)
    }
}

fn scenario_slug(index: usize, result: &IndividualTestResult) -> String {
    let combined = if result.group.is_empty() {
        result.name.clone()
    } else {
        format!("{} {}", result.group, result.name)
    };

    let mut slug = slugify(&combined);
    if slug.is_empty() {
        slug = format!("scenario-{}", index + 1);
    }
    slug
}

fn slugify(value: &str) -> String {
    let mut slug = String::with_capacity(value.len());
    let mut last_was_dash = false;

    for ch in value.chars() {
        if ch.is_ascii_alphanumeric() {
            slug.push(ch.to_ascii_lowercase());
            last_was_dash = false;
        } else if !last_was_dash {
            slug.push('-');
            last_was_dash = true;
        }
    }

    slug.trim_matches('-').to_string()
}

fn artifact_root_for_path(source_path: &Path) -> PathBuf {
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
        let stem = source_path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("spec");
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

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_result(group: &str, name: &str) -> IndividualTestResult {
        IndividualTestResult {
            group: group.to_string(),
            name: name.to_string(),
            passed: true,
            skipped: false,
        }
    }

    #[test]
    fn plan_uses_spec_relative_root_and_scenario_dirs() {
        let plan = build_scenario_artifact_plan(
            Path::new("test/app/web_dashboard/tmux_rest_api_spec.spl"),
            &[sample_result("rendering", "shows dashboard")],
        );

        assert_eq!(
            plan.spec_root.to_string_lossy().replace('\\', "/"),
            "target/test-artifacts/app/web_dashboard/tmux_rest_api"
        );
        assert_eq!(
            plan.scenario_root.to_string_lossy().replace('\\', "/"),
            "target/test-artifacts/app/web_dashboard/tmux_rest_api/scenarios"
        );
        assert_eq!(plan.entries.len(), 1);
        assert_eq!(plan.entries[0].index, 1);
        assert_eq!(plan.entries[0].slug, "rendering-shows-dashboard");
        assert_eq!(
            plan.entries[0].directory.to_string_lossy().replace('\\', "/"),
            "target/test-artifacts/app/web_dashboard/tmux_rest_api/scenarios/001-rendering-shows-dashboard"
        );
    }

    #[test]
    fn planned_artifacts_include_future_capture_slots() {
        let artifacts = planned_artifacts(Path::new("target/test-artifacts/demo/scenarios/001-demo"));
        let filenames: Vec<String> = artifacts
            .iter()
            .map(|item| item.path.file_name().unwrap().to_string_lossy().to_string())
            .collect();

        assert!(filenames.contains(&"summary.txt".to_string()));
        assert!(filenames.contains(&"run.log".to_string()));
        assert!(filenames.contains(&"result.json".to_string()));
        assert!(filenames.contains(&"stdout.log".to_string()));
        assert!(filenames.contains(&"stderr.log".to_string()));
        assert!(filenames.contains(&"combined.log".to_string()));
        assert!(filenames.contains(&"screenshot.png".to_string()));
        assert!(filenames.contains(&"transcript.ansi".to_string()));
        assert!(filenames.contains(&"transcript.txt".to_string()));
    }

    #[test]
    fn manifest_text_lists_scenarios_and_artifacts() {
        let plan = build_scenario_artifact_plan(
            Path::new("test/unit/example_spec.spl"),
            &[
                sample_result("outer", "first scenario"),
                sample_result("", "second scenario"),
            ],
        );

        let manifest = build_manifest_text(&plan);
        assert!(manifest.contains("scenario_count: 2"));
        assert!(manifest.contains("[1] outer > first scenario"));
        assert!(manifest.contains("[2] second scenario"));
        assert!(manifest.contains("summary.txt =>"));
        assert!(manifest.contains("transcript.txt =>"));
    }

    #[test]
    fn slugify_collapses_non_alphanumeric_runs() {
        assert_eq!(slugify("hello, world! / 42"), "hello-world-42");
        assert_eq!(slugify("***"), "");
    }

    #[test]
    fn write_manifest_skips_empty_scenarios() {
        let written = write_scenario_manifest(Path::new("test/demo_spec.spl"), &[]).unwrap();
        assert!(written.is_none());
    }
}

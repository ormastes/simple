//! Build logging and replay functionality (#912).
//!
//! Records compilation sessions for debugging and auditing.

use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;
use uuid::Uuid;

/// Build log capturing compilation session details.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildLog {
    /// Unique session identifier
    pub session_id: String,

    /// Session start timestamp (ISO 8601)
    pub timestamp: String,

    /// Compiler version
    pub compiler_version: String,

    /// Command that was executed
    pub command: String,

    /// Environment variables and working directory
    pub environment: BuildEnvironment,

    /// Input files and dependencies
    pub inputs: BuildInputs,

    /// Compilation phases with timing
    pub phases: Vec<BuildPhase>,

    /// Output artifacts
    pub output: Option<BuildOutput>,

    /// Overall build result
    pub result: BuildResult,

    /// Errors and warnings captured during build
    pub diagnostics: Vec<BuildDiagnostic>,
}

/// Build environment information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildEnvironment {
    /// Working directory
    pub working_dir: String,

    /// Relevant environment variables
    pub env_vars: HashMap<String, String>,
}

/// Build input information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildInputs {
    /// Source files compiled
    pub source_files: Vec<String>,

    /// Dependencies and their versions
    pub dependencies: HashMap<String, String>,
}

/// A compilation phase with timing information.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildPhase {
    /// Phase name (parse, typecheck, codegen, etc.)
    pub name: String,

    /// Duration in milliseconds
    pub duration_ms: u64,

    /// Phase result
    pub result: PhaseResult,

    /// Optional error message
    pub error: Option<String>,
}

/// Phase execution result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum PhaseResult {
    Success,
    Failed,
    Skipped,
}

/// Build output artifacts.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildOutput {
    /// Output binary path
    pub binary: String,

    /// Output file size in bytes
    pub size_bytes: u64,

    /// SHA-256 hash of output
    pub hash: String,
}

/// Overall build result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum BuildResult {
    Success,
    Failed,
    Cancelled,
}

/// Diagnostic message (error or warning).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildDiagnostic {
    /// Diagnostic level
    pub level: DiagnosticLevel,

    /// Error/warning message
    pub message: String,

    /// Source file (if applicable)
    pub file: Option<String>,

    /// Line number (if applicable)
    pub line: Option<usize>,

    /// Column number (if applicable)
    pub column: Option<usize>,
}

/// Diagnostic severity level.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum DiagnosticLevel {
    Error,
    Warning,
    Info,
}

/// Build logger for recording compilation sessions.
pub struct BuildLogger {
    session_id: Uuid,
    start_time: Instant,
    start_timestamp: DateTime<Utc>,
    compiler_version: String,
    command: String,
    environment: BuildEnvironment,
    inputs: BuildInputs,
    phases: Vec<BuildPhase>,
    current_phase: Option<(String, Instant)>,
    diagnostics: Vec<BuildDiagnostic>,
}

impl BuildLogger {
    /// Create a new build logger.
    pub fn new(compiler_version: String, command: String) -> Self {
        let working_dir = std::env::current_dir()
            .ok()
            .and_then(|p| p.to_str().map(|s| s.to_string()))
            .unwrap_or_else(|| ".".to_string());

        // Capture relevant environment variables
        let mut env_vars = HashMap::new();
        for (key, value) in std::env::vars() {
            if key.starts_with("SIMPLE_") || key == "RUST_LOG" || key == "PATH" {
                env_vars.insert(key, value);
            }
        }

        Self {
            session_id: Uuid::new_v4(),
            start_time: Instant::now(),
            start_timestamp: Utc::now(),
            compiler_version,
            command,
            environment: BuildEnvironment {
                working_dir,
                env_vars,
            },
            inputs: BuildInputs {
                source_files: Vec::new(),
                dependencies: HashMap::new(),
            },
            phases: Vec::new(),
            current_phase: None,
            diagnostics: Vec::new(),
        }
    }

    /// Add a source file to the inputs.
    pub fn add_source_file(&mut self, path: &str) {
        self.inputs.source_files.push(path.to_string());
    }

    /// Add a dependency.
    pub fn add_dependency(&mut self, name: String, version: String) {
        self.inputs.dependencies.insert(name, version);
    }

    /// Start timing a compilation phase.
    pub fn start_phase(&mut self, name: &str) {
        self.end_current_phase();
        self.current_phase = Some((name.to_string(), Instant::now()));
    }

    /// End the current phase successfully.
    pub fn end_phase_success(&mut self) {
        self.end_phase_with_result(PhaseResult::Success, None);
    }

    /// End the current phase with a failure.
    pub fn end_phase_failed(&mut self, error: String) {
        self.end_phase_with_result(PhaseResult::Failed, Some(error));
    }

    /// End the current phase with a specific result.
    fn end_phase_with_result(&mut self, result: PhaseResult, error: Option<String>) {
        if let Some((name, start)) = self.current_phase.take() {
            let duration_ms = start.elapsed().as_millis() as u64;
            self.phases.push(BuildPhase {
                name,
                duration_ms,
                result,
                error,
            });
        }
    }

    /// End the current phase (if any).
    fn end_current_phase(&mut self) {
        self.end_phase_with_result(PhaseResult::Success, None);
    }

    /// Add a diagnostic message.
    pub fn add_diagnostic(&mut self, level: DiagnosticLevel, message: String) {
        self.diagnostics.push(BuildDiagnostic {
            level,
            message,
            file: None,
            line: None,
            column: None,
        });
    }

    /// Add a diagnostic with location information.
    pub fn add_diagnostic_with_location(
        &mut self,
        level: DiagnosticLevel,
        message: String,
        file: String,
        line: usize,
        column: usize,
    ) {
        self.diagnostics.push(BuildDiagnostic {
            level,
            message,
            file: Some(file),
            line: Some(line),
            column: Some(column),
        });
    }

    /// Finalize the log and return a BuildLog.
    pub fn finalize(mut self, result: BuildResult, output: Option<BuildOutput>) -> BuildLog {
        self.end_current_phase();

        BuildLog {
            session_id: self.session_id.to_string(),
            timestamp: self.start_timestamp.to_rfc3339(),
            compiler_version: self.compiler_version,
            command: self.command,
            environment: self.environment,
            inputs: self.inputs,
            phases: self.phases,
            output,
            result,
            diagnostics: self.diagnostics,
        }
    }
}

impl BuildLog {
    /// Load a build log from a JSON file.
    pub fn load(path: &Path) -> Result<Self, String> {
        let content =
            fs::read_to_string(path).map_err(|e| format!("Failed to read log file: {}", e))?;

        serde_json::from_str(&content).map_err(|e| format!("Failed to parse log file: {}", e))
    }

    /// Save the build log to a JSON file.
    pub fn save(&self, path: &Path) -> Result<(), String> {
        let json = serde_json::to_string_pretty(self)
            .map_err(|e| format!("Failed to serialize log: {}", e))?;

        fs::write(path, json).map_err(|e| format!("Failed to write log file: {}", e))
    }

    /// Get the total build duration in milliseconds.
    pub fn total_duration_ms(&self) -> u64 {
        self.phases.iter().map(|p| p.duration_ms).sum()
    }

    /// Check if the build was successful.
    pub fn is_success(&self) -> bool {
        self.result == BuildResult::Success
    }

    /// Count errors in diagnostics.
    pub fn error_count(&self) -> usize {
        self.diagnostics
            .iter()
            .filter(|d| d.level == DiagnosticLevel::Error)
            .count()
    }

    /// Count warnings in diagnostics.
    pub fn warning_count(&self) -> usize {
        self.diagnostics
            .iter()
            .filter(|d| d.level == DiagnosticLevel::Warning)
            .count()
    }

    /// Compare two build logs and return differences.
    pub fn compare(&self, other: &BuildLog) -> BuildComparison {
        let phase_diff = self.compare_phases(&other.phases);
        let duration_diff = self.total_duration_ms() as i64 - other.total_duration_ms() as i64;

        BuildComparison {
            session1: self.session_id.clone(),
            session2: other.session_id.clone(),
            phase_differences: phase_diff,
            duration_difference_ms: duration_diff,
            result_changed: self.result != other.result,
        }
    }

    /// Compare compilation phases.
    fn compare_phases(&self, other_phases: &[BuildPhase]) -> Vec<PhaseDifference> {
        let mut differences = Vec::new();

        for (i, phase) in self.phases.iter().enumerate() {
            if let Some(other_phase) = other_phases.get(i) {
                if phase.name == other_phase.name {
                    let duration_diff = phase.duration_ms as i64 - other_phase.duration_ms as i64;
                    if duration_diff.abs() > 5 {
                        // Only report differences > 5ms
                        differences.push(PhaseDifference {
                            phase_name: phase.name.clone(),
                            duration_diff_ms: duration_diff,
                            result_changed: phase.result != other_phase.result,
                        });
                    }
                }
            }
        }

        differences
    }
}

/// Comparison result between two build logs.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildComparison {
    pub session1: String,
    pub session2: String,
    pub phase_differences: Vec<PhaseDifference>,
    pub duration_difference_ms: i64,
    pub result_changed: bool,
}

/// Difference in a compilation phase.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PhaseDifference {
    pub phase_name: String,
    pub duration_diff_ms: i64,
    pub result_changed: bool,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_logger_new() {
        let logger = BuildLogger::new("0.1.0".to_string(), "simple compile test.spl".to_string());
        assert_eq!(logger.compiler_version, "0.1.0");
        assert_eq!(logger.command, "simple compile test.spl");
        assert_eq!(logger.phases.len(), 0);
    }

    #[test]
    fn test_add_source_file() {
        let mut logger = BuildLogger::new("0.1.0".to_string(), "simple compile".to_string());
        logger.add_source_file("test.spl");
        logger.add_source_file("lib.spl");
        assert_eq!(logger.inputs.source_files, vec!["test.spl", "lib.spl"]);
    }

    #[test]
    fn test_add_dependency() {
        let mut logger = BuildLogger::new("0.1.0".to_string(), "simple compile".to_string());
        logger.add_dependency("http".to_string(), "1.0.0".to_string());
        assert_eq!(
            logger.inputs.dependencies.get("http"),
            Some(&"1.0.0".to_string())
        );
    }

    #[test]
    fn test_phase_tracking() {
        let mut logger = BuildLogger::new("0.1.0".to_string(), "simple compile".to_string());

        logger.start_phase("parse");
        std::thread::sleep(std::time::Duration::from_millis(10));
        logger.end_phase_success();

        logger.start_phase("typecheck");
        std::thread::sleep(std::time::Duration::from_millis(10));
        logger.end_phase_success();

        assert_eq!(logger.phases.len(), 2);
        assert_eq!(logger.phases[0].name, "parse");
        assert_eq!(logger.phases[1].name, "typecheck");
        assert!(logger.phases[0].duration_ms >= 10);
        assert!(logger.phases[1].duration_ms >= 10);
    }

    #[test]
    fn test_phase_failure() {
        let mut logger = BuildLogger::new("0.1.0".to_string(), "simple compile".to_string());

        logger.start_phase("parse");
        logger.end_phase_failed("Syntax error".to_string());

        assert_eq!(logger.phases.len(), 1);
        assert_eq!(logger.phases[0].result, PhaseResult::Failed);
        assert_eq!(logger.phases[0].error, Some("Syntax error".to_string()));
    }

    #[test]
    fn test_diagnostics() {
        let mut logger = BuildLogger::new("0.1.0".to_string(), "simple compile".to_string());

        logger.add_diagnostic(DiagnosticLevel::Error, "Test error".to_string());
        logger.add_diagnostic(DiagnosticLevel::Warning, "Test warning".to_string());

        assert_eq!(logger.diagnostics.len(), 2);
        assert_eq!(logger.diagnostics[0].level, DiagnosticLevel::Error);
        assert_eq!(logger.diagnostics[1].level, DiagnosticLevel::Warning);
    }

    #[test]
    fn test_finalize() {
        let mut logger =
            BuildLogger::new("0.1.0".to_string(), "simple compile test.spl".to_string());
        logger.add_source_file("test.spl");
        logger.start_phase("parse");
        logger.end_phase_success();

        let log = logger.finalize(BuildResult::Success, None);

        assert_eq!(log.result, BuildResult::Success);
        assert_eq!(log.inputs.source_files.len(), 1);
        assert_eq!(log.phases.len(), 1);
    }

    #[test]
    fn test_total_duration() {
        let mut logger = BuildLogger::new("0.1.0".to_string(), "simple compile".to_string());

        logger.start_phase("parse");
        std::thread::sleep(std::time::Duration::from_millis(10));
        logger.end_phase_success();

        logger.start_phase("typecheck");
        std::thread::sleep(std::time::Duration::from_millis(10));
        logger.end_phase_success();

        let log = logger.finalize(BuildResult::Success, None);
        assert!(log.total_duration_ms() >= 20);
    }

    #[test]
    fn test_error_warning_count() {
        let mut logger = BuildLogger::new("0.1.0".to_string(), "simple compile".to_string());

        logger.add_diagnostic(DiagnosticLevel::Error, "Error 1".to_string());
        logger.add_diagnostic(DiagnosticLevel::Error, "Error 2".to_string());
        logger.add_diagnostic(DiagnosticLevel::Warning, "Warning 1".to_string());

        let log = logger.finalize(BuildResult::Failed, None);

        assert_eq!(log.error_count(), 2);
        assert_eq!(log.warning_count(), 1);
    }
}

//! Lean 4 invocation and proof checking.
//!
//! This module handles:
//! - Writing generated Lean files to disk
//! - Invoking Lean to check proofs
//! - Parsing Lean output for errors
//! - Tracking proof status

use std::fs;
use std::io;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use crate::CompileError;

/// Result of running Lean on a file
#[derive(Debug, Clone)]
pub struct LeanCheckResult {
    /// File that was checked
    pub file: PathBuf,
    /// Whether the check succeeded
    pub success: bool,
    /// Lean stdout
    pub stdout: String,
    /// Lean stderr
    pub stderr: String,
    /// Number of goals solved
    pub goals_solved: usize,
    /// Number of goals remaining (sorry)
    pub goals_remaining: usize,
    /// Exit code
    pub exit_code: Option<i32>,
}

impl LeanCheckResult {
    /// Check if this result has unproven theorems
    pub fn has_unproven(&self) -> bool {
        self.goals_remaining > 0
    }

    /// Check if this result is fully proven
    pub fn is_fully_proven(&self) -> bool {
        self.success && self.goals_remaining == 0
    }
}

/// Lean runner for proof checking
pub struct LeanRunner {
    /// Path to Lean executable
    lean_path: PathBuf,
    /// Output directory for Lean files
    output_dir: PathBuf,
    /// Whether to generate stubs
    generate_stubs: bool,
    /// Verbose mode
    verbose: bool,
}

impl LeanRunner {
    /// Create a new Lean runner
    pub fn new(lean_path: impl Into<PathBuf>, output_dir: impl Into<PathBuf>) -> Self {
        Self {
            lean_path: lean_path.into(),
            output_dir: output_dir.into(),
            generate_stubs: true,
            verbose: false,
        }
    }

    /// Set whether to generate stubs
    pub fn with_stubs(mut self, generate: bool) -> Self {
        self.generate_stubs = generate;
        self
    }

    /// Set verbose mode
    pub fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Ensure the output directory exists
    pub fn ensure_output_dir(&self) -> io::Result<()> {
        fs::create_dir_all(&self.output_dir)
    }

    /// Write a Lean file to the output directory
    pub fn write_lean_file(&self, name: &str, content: &str) -> io::Result<PathBuf> {
        self.ensure_output_dir()?;

        let file_path = self.output_dir.join(format!("{}.lean", name));
        fs::write(&file_path, content)?;

        if self.verbose {
            eprintln!("[lean] Wrote {}", file_path.display());
        }

        Ok(file_path)
    }

    /// Check if Lean is available
    pub fn is_lean_available(&self) -> bool {
        Command::new(&self.lean_path)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }

    /// Get Lean version
    pub fn lean_version(&self) -> Option<String> {
        Command::new(&self.lean_path)
            .arg("--version")
            .output()
            .ok()
            .and_then(|o| {
                if o.status.success() {
                    String::from_utf8(o.stdout).ok()
                } else {
                    None
                }
            })
            .map(|s| s.trim().to_string())
    }

    /// Run Lean on a file to check proofs
    pub fn check_file(&self, file: &Path) -> Result<LeanCheckResult, CompileError> {
        if self.verbose {
            eprintln!("[lean] Checking {}", file.display());
        }

        let output = Command::new(&self.lean_path)
            .arg(file)
            .output()
            .map_err(|e| CompileError::Semantic(format!("Failed to run Lean: {}", e)))?;

        Ok(self.parse_output(file, output))
    }

    /// Run Lean on generated content
    pub fn check_content(
        &self,
        name: &str,
        content: &str,
    ) -> Result<LeanCheckResult, CompileError> {
        let file_path = self
            .write_lean_file(name, content)
            .map_err(|e| CompileError::Semantic(format!("Failed to write Lean file: {}", e)))?;

        self.check_file(&file_path)
    }

    /// Parse Lean output
    fn parse_output(&self, file: &Path, output: Output) -> LeanCheckResult {
        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();

        // Count sorry occurrences as remaining goals
        let goals_remaining = stdout.matches("sorry").count() + stderr.matches("sorry").count();

        // Try to extract goal count from Lean output
        let goals_solved = self.count_solved_goals(&stdout, &stderr);

        LeanCheckResult {
            file: file.to_path_buf(),
            success: output.status.success(),
            stdout,
            stderr,
            goals_solved,
            goals_remaining,
            exit_code: output.status.code(),
        }
    }

    /// Count solved goals from Lean output
    fn count_solved_goals(&self, stdout: &str, stderr: &str) -> usize {
        // Look for "goals accomplished" or similar patterns
        let combined = format!("{}\n{}", stdout, stderr);

        // Simple heuristic: count "no goals" or "goals accomplished"
        let accomplished = combined.matches("goals accomplished").count();
        let no_goals = combined.matches("no goals").count();

        accomplished + no_goals
    }

    /// Check multiple files
    pub fn check_files(&self, files: &[PathBuf]) -> Vec<LeanCheckResult> {
        files
            .iter()
            .filter_map(|f| self.check_file(f).ok())
            .collect()
    }

    /// Get the output directory
    pub fn output_dir(&self) -> &Path {
        &self.output_dir
    }
}

/// Summary of verification results
#[derive(Debug, Default)]
pub struct VerificationSummary {
    /// Total files checked
    pub files_checked: usize,
    /// Files that passed
    pub files_passed: usize,
    /// Files that failed
    pub files_failed: usize,
    /// Total theorems
    pub total_theorems: usize,
    /// Proven theorems
    pub proven_theorems: usize,
    /// Unproven theorems (sorry)
    pub unproven_theorems: usize,
    /// Errors encountered
    pub errors: Vec<String>,
}

impl VerificationSummary {
    /// Create a summary from check results
    pub fn from_results(results: &[LeanCheckResult]) -> Self {
        let mut summary = VerificationSummary::default();

        for result in results {
            summary.files_checked += 1;
            if result.success {
                summary.files_passed += 1;
            } else {
                summary.files_failed += 1;
                if !result.stderr.is_empty() {
                    summary.errors.push(result.stderr.clone());
                }
            }
            summary.proven_theorems += result.goals_solved;
            summary.unproven_theorems += result.goals_remaining;
        }

        summary.total_theorems = summary.proven_theorems + summary.unproven_theorems;
        summary
    }

    /// Check if verification was successful
    pub fn is_success(&self) -> bool {
        self.files_failed == 0
    }

    /// Check if all theorems are proven
    pub fn is_fully_proven(&self) -> bool {
        self.is_success() && self.unproven_theorems == 0
    }

    /// Format as a human-readable string
    pub fn format(&self) -> String {
        let mut out = String::new();

        out.push_str(&format!("Verification Summary:\n"));
        out.push_str(&format!(
            "  Files: {}/{} passed\n",
            self.files_passed, self.files_checked
        ));

        if self.total_theorems > 0 {
            out.push_str(&format!(
                "  Theorems: {}/{} proven\n",
                self.proven_theorems, self.total_theorems
            ));
        }

        if self.unproven_theorems > 0 {
            out.push_str(&format!("  Unproven (sorry): {}\n", self.unproven_theorems));
        }

        if !self.errors.is_empty() {
            out.push_str(&format!("  Errors: {}\n", self.errors.len()));
        }

        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lean_runner_creation() {
        let runner = LeanRunner::new("lean", "build/lean")
            .with_stubs(true)
            .with_verbose(false);

        assert_eq!(runner.lean_path, PathBuf::from("lean"));
        assert_eq!(runner.output_dir, PathBuf::from("build/lean"));
        assert!(runner.generate_stubs);
        assert!(!runner.verbose);
    }

    #[test]
    fn test_check_result_status() {
        let result = LeanCheckResult {
            file: PathBuf::from("test.lean"),
            success: true,
            stdout: String::new(),
            stderr: String::new(),
            goals_solved: 5,
            goals_remaining: 0,
            exit_code: Some(0),
        };

        assert!(result.is_fully_proven());
        assert!(!result.has_unproven());

        let result_with_sorry = LeanCheckResult {
            goals_remaining: 2,
            ..result.clone()
        };

        assert!(!result_with_sorry.is_fully_proven());
        assert!(result_with_sorry.has_unproven());
    }

    #[test]
    fn test_verification_summary() {
        let results = vec![
            LeanCheckResult {
                file: PathBuf::from("a.lean"),
                success: true,
                stdout: String::new(),
                stderr: String::new(),
                goals_solved: 3,
                goals_remaining: 1,
                exit_code: Some(0),
            },
            LeanCheckResult {
                file: PathBuf::from("b.lean"),
                success: true,
                stdout: String::new(),
                stderr: String::new(),
                goals_solved: 2,
                goals_remaining: 0,
                exit_code: Some(0),
            },
        ];

        let summary = VerificationSummary::from_results(&results);

        assert_eq!(summary.files_checked, 2);
        assert_eq!(summary.files_passed, 2);
        assert_eq!(summary.proven_theorems, 5);
        assert_eq!(summary.unproven_theorems, 1);
        assert!(summary.is_success());
        assert!(!summary.is_fully_proven());
    }
}

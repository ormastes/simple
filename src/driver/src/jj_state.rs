use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use std::process::Command;

/// Build mode (Debug or Release)
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum BuildMode {
    Debug,
    Release,
}

impl std::fmt::Display for BuildMode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BuildMode::Debug => write!(f, "Debug"),
            BuildMode::Release => write!(f, "Release"),
        }
    }
}

/// Test level
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
pub enum TestLevel {
    Unit,
    Integration,
    System,
    Environment,
    All,
}

impl std::fmt::Display for TestLevel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TestLevel::Unit => write!(f, "Unit"),
            TestLevel::Integration => write!(f, "Integration"),
            TestLevel::System => write!(f, "System"),
            TestLevel::Environment => write!(f, "Environment"),
            TestLevel::All => write!(f, "All"),
        }
    }
}

/// Metadata for a successful build
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildMetadata {
    pub timestamp: DateTime<Utc>,
    pub duration_ms: u64,
    pub artifacts: Vec<PathBuf>,
    pub target: String,
    pub mode: BuildMode,
}

impl BuildMetadata {
    /// Convert metadata to a commit message
    pub fn to_commit_message(&self) -> String {
        let duration_secs = self.duration_ms as f64 / 1000.0;

        let mut message = format!(
            "🏗️  Build Success\n\n\
             Duration: {:.1}s\n\
             Mode: {}\n\
             Target: {}\n",
            duration_secs, self.mode, self.target
        );

        if !self.artifacts.is_empty() {
            message.push_str("Artifacts:\n");
            for artifact in &self.artifacts {
                message.push_str(&format!("  - {}\n", artifact.display()));
            }
        }

        message.push_str(&format!("\nTimestamp: {}\n", self.timestamp.to_rfc3339()));

        message
    }
}

/// Metadata for a successful test run
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestMetadata {
    pub timestamp: DateTime<Utc>,
    pub duration_ms: u64,
    pub total_tests: usize,
    pub passed: usize,
    pub failed: usize,
    pub ignored: usize,
    pub test_level: TestLevel,
}

impl TestMetadata {
    /// Convert metadata to a commit message
    pub fn to_commit_message(&self) -> String {
        let duration_secs = self.duration_ms as f64 / 1000.0;

        format!(
            "✅ Tests Passed: All\n\n\
             Level: {}\n\
             Total: {} tests\n\
             Passed: {}\n\
             Failed: {}\n\
             Ignored: {}\n\
             Duration: {:.1}s\n\n\
             Timestamp: {}\n",
            self.test_level,
            self.total_tests,
            self.passed,
            self.failed,
            self.ignored,
            duration_secs,
            self.timestamp.to_rfc3339()
        )
    }
}

/// JJ state manager for build snapshots
pub struct JjStateManager {
    enabled: bool,
    repo_path: PathBuf,
}

impl JjStateManager {
    /// Create a new state manager using current directory
    pub fn new() -> Result<Self, Box<dyn std::error::Error>> {
        let repo_path = std::env::current_dir()?;
        Self::new_with_path(repo_path)
    }

    /// Create a new state manager with specified path
    pub fn new_with_path(repo_path: PathBuf) -> Result<Self, Box<dyn std::error::Error>> {
        let enabled = repo_path.join(".jj").exists();
        Ok(Self { enabled, repo_path })
    }

    /// Check if JJ is enabled for this repository
    pub fn is_enabled(&self) -> bool {
        self.enabled
    }

    /// Snapshot a successful build
    pub fn snapshot_build_success(
        &self,
        metadata: &BuildMetadata,
    ) -> Result<(), Box<dyn std::error::Error>> {
        if !self.enabled {
            // Gracefully do nothing if JJ is not enabled
            return Ok(());
        }

        let message = metadata.to_commit_message();
        self.create_snapshot(&message)?;

        Ok(())
    }

    /// Snapshot a successful test run
    pub fn snapshot_test_success(
        &self,
        metadata: &TestMetadata,
    ) -> Result<(), Box<dyn std::error::Error>> {
        if !self.enabled {
            // Gracefully do nothing if JJ is not enabled
            return Ok(());
        }

        let message = metadata.to_commit_message();
        self.create_snapshot(&message)?;

        Ok(())
    }

    /// Get the last working state (commit ID)
    pub fn get_last_working_state(&self) -> Result<Option<String>, Box<dyn std::error::Error>> {
        if !self.enabled {
            return Ok(None);
        }

        // Get the most recent success snapshot
        let output = Command::new("jj")
            .args(&[
                "log",
                "--limit",
                "10",
                "-r",
                r#"description("Build Success") | description("Tests Passed")"#,
            ])
            .current_dir(&self.repo_path)
            .output()?;

        if !output.status.success() {
            return Ok(None);
        }

        let log = String::from_utf8_lossy(&output.stdout);
        if log.trim().is_empty() {
            return Ok(None);
        }

        // Parse commit ID from log output
        // Format: "@  commit_id email timestamp description..."
        // or:     "○  commit_id email timestamp description..."
        for line in log.lines() {
            if line.starts_with('@') || line.starts_with('○') || line.starts_with('◆') {
                let parts: Vec<&str> = line.split_whitespace().collect();
                if parts.len() >= 2 {
                    return Ok(Some(parts[1].to_string()));
                }
            }
        }

        Ok(None)
    }

    /// Create a JJ snapshot with the given message
    fn create_snapshot(&self, message: &str) -> Result<(), Box<dyn std::error::Error>> {
        let output = Command::new("jj")
            .args(&["describe", "-m", message])
            .current_dir(&self.repo_path)
            .output()?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("Failed to create snapshot: {}", stderr).into());
        }

        // Create a new working copy for the next change
        let output = Command::new("jj")
            .args(&["new"])
            .current_dir(&self.repo_path)
            .output()?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("Failed to create new working copy: {}", stderr).into());
        }

        Ok(())
    }
}

impl Default for JjStateManager {
    fn default() -> Self {
        Self::new().unwrap_or_else(|_| Self {
            enabled: false,
            repo_path: PathBuf::new(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn build_mode_display() {
        assert_eq!(BuildMode::Debug.to_string(), "Debug");
        assert_eq!(BuildMode::Release.to_string(), "Release");
    }

    #[test]
    fn test_level_display() {
        assert_eq!(TestLevel::Unit.to_string(), "Unit");
        assert_eq!(TestLevel::Integration.to_string(), "Integration");
        assert_eq!(TestLevel::System.to_string(), "System");
        assert_eq!(TestLevel::Environment.to_string(), "Environment");
        assert_eq!(TestLevel::All.to_string(), "All");
    }
}

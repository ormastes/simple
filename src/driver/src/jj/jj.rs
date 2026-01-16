use super::event::BuildState;
use super::store::StateStore;
use std::io;
use std::path::{Path, PathBuf};
use std::process::Command;

/// Interface to Jujutsu version control system
#[derive(Debug)]
pub struct JJConnector {
    repo_root: PathBuf,
    state_store: StateStore,
}

impl JJConnector {
    /// Create a new JJ connector for the given repository
    pub fn new(repo_root: impl Into<PathBuf>) -> Self {
        let repo_root = repo_root.into();
        let state_store = StateStore::new(StateStore::default_path(&repo_root));
        Self { repo_root, state_store }
    }

    /// Initialize the connector (create state store)
    pub fn init(&self) -> io::Result<()> {
        self.state_store.init()
    }

    /// Get current commit ID
    pub fn current_commit_id(&self) -> io::Result<String> {
        let output = Command::new("jj")
            .arg("log")
            .arg("-r")
            .arg("@")
            .arg("--no-graph")
            .arg("-T")
            .arg("commit_id")
            .current_dir(&self.repo_root)
            .output()?;

        if !output.status.success() {
            return Err(io::Error::new(
                io::ErrorKind::Other,
                String::from_utf8_lossy(&output.stderr).to_string(),
            ));
        }

        let commit_id = String::from_utf8_lossy(&output.stdout).trim().to_string();
        Ok(commit_id)
    }

    /// Create a change description with build state
    pub fn describe_with_state(&self, state: &BuildState) -> io::Result<()> {
        let description = self.format_description(state);

        Command::new("jj")
            .arg("describe")
            .arg("-m")
            .arg(description)
            .current_dir(&self.repo_root)
            .output()?;

        Ok(())
    }

    /// Store build state
    pub fn store_state(&self, state: BuildState) -> io::Result<()> {
        self.state_store.store(state)
    }

    /// Load states for current commit
    pub fn load_current_states(&self) -> io::Result<Vec<BuildState>> {
        let commit_id = self.current_commit_id()?;
        self.state_store.load_for_commit(&commit_id)
    }

    /// Check if current commit has successful build
    pub fn has_successful_build(&self) -> io::Result<bool> {
        let states = self.load_current_states()?;
        Ok(states.iter().any(|s| s.compilation_success))
    }

    /// Check if current commit has all tests passing
    pub fn has_all_tests_passing(&self) -> io::Result<bool> {
        let states = self.load_current_states()?;
        Ok(states
            .iter()
            .any(|s| s.compilation_success && s.tests_passed.is_some() && s.tests_failed == Some(0)))
    }

    /// Format description from build state
    fn format_description(&self, state: &BuildState) -> String {
        let mut parts = Vec::new();

        if state.compilation_success {
            parts.push("✓ Compilation succeeded".to_string());
        } else {
            parts.push("✗ Compilation failed".to_string());
        }

        if let (Some(passed), Some(failed), Some(total)) = (state.tests_passed, state.tests_failed, state.total_tests) {
            if failed == 0 {
                parts.push(format!("✓ All {} tests passed", total));
            } else {
                parts.push(format!("✗ {}/{} tests failed", failed, total));
                parts.push(format!("  {} tests passed", passed));
            }
        }

        parts.join("\n")
    }

    /// Get repository root
    pub fn repo_root(&self) -> &Path {
        &self.repo_root
    }

    /// Get state store
    pub fn state_store(&self) -> &StateStore {
        &self.state_store
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_format_description_success() {
        let temp = TempDir::new().unwrap();
        let connector = JJConnector::new(temp.path());

        let state = BuildState::new().mark_compilation_success().set_test_results(10, 0, 10);

        let desc = connector.format_description(&state);
        assert!(desc.contains("✓ Compilation succeeded"));
        assert!(desc.contains("✓ All 10 tests passed"));
    }

    #[test]
    fn test_format_description_failure() {
        let temp = TempDir::new().unwrap();
        let connector = JJConnector::new(temp.path());

        let state = BuildState::new().set_test_results(8, 2, 10);

        let desc = connector.format_description(&state);
        assert!(desc.contains("✗ Compilation failed"));
        assert!(desc.contains("✗ 2/10 tests failed"));
    }

    #[test]
    fn test_init_and_store() {
        let temp = TempDir::new().unwrap();
        let connector = JJConnector::new(temp.path());

        connector.init().unwrap();

        let state = BuildState::new()
            .with_commit("test123".to_string())
            .mark_compilation_success();

        connector.store_state(state).unwrap();

        let states = connector.state_store.load_all().unwrap();
        assert_eq!(states.len(), 1);
    }
}

use super::event::BuildState;
use serde::{Deserialize, Serialize};
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};

/// Persistent storage for build states
#[derive(Debug)]
pub struct StateStore {
    store_path: PathBuf,
}

#[derive(Debug, Serialize, Deserialize)]
struct StateRecord {
    states: Vec<BuildState>,
}

impl StateStore {
    /// Create a new state store at the given path
    pub fn new(store_path: impl Into<PathBuf>) -> Self {
        Self {
            store_path: store_path.into(),
        }
    }

    /// Get default store path in project root
    pub fn default_path(project_root: &Path) -> PathBuf {
        project_root.join(".simple").join("build_states.json")
    }

    /// Initialize store directory
    pub fn init(&self) -> io::Result<()> {
        if let Some(parent) = self.store_path.parent() {
            fs::create_dir_all(parent)?;
        }
        if !self.store_path.exists() {
            self.save_record(&StateRecord { states: Vec::new() })?;
        }
        Ok(())
    }

    /// Store a build state
    pub fn store(&self, state: BuildState) -> io::Result<()> {
        let mut record = self.load_record()?;
        record.states.push(state);
        self.save_record(&record)
    }

    /// Load all stored states
    pub fn load_all(&self) -> io::Result<Vec<BuildState>> {
        let record = self.load_record()?;
        Ok(record.states)
    }

    /// Load states for a specific commit
    pub fn load_for_commit(&self, commit_id: &str) -> io::Result<Vec<BuildState>> {
        let record = self.load_record()?;
        Ok(record
            .states
            .into_iter()
            .filter(|s| s.commit_id.as_deref() == Some(commit_id))
            .collect())
    }

    /// Get the latest state
    pub fn latest(&self) -> io::Result<Option<BuildState>> {
        let record = self.load_record()?;
        Ok(record.states.last().cloned())
    }

    /// Clear all stored states
    pub fn clear(&self) -> io::Result<()> {
        self.save_record(&StateRecord { states: Vec::new() })
    }

    fn load_record(&self) -> io::Result<StateRecord> {
        if !self.store_path.exists() {
            return Ok(StateRecord { states: Vec::new() });
        }
        let content = fs::read_to_string(&self.store_path)?;
        serde_json::from_str(&content).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
    }

    fn save_record(&self, record: &StateRecord) -> io::Result<()> {
        let content = serde_json::to_string_pretty(record)
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
        let mut file = fs::File::create(&self.store_path)?;
        file.write_all(content.as_bytes())?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::SystemTime;
    use tempfile::TempDir;

    #[test]
    fn test_store_and_load() {
        let temp = TempDir::new().unwrap();
        let store_path = temp.path().join("states.json");
        let store = StateStore::new(&store_path);

        store.init().unwrap();

        let state = BuildState {
            timestamp: SystemTime::now(),
            commit_id: Some("abc123".to_string()),
            compilation_success: true,
            tests_passed: Some(10),
            tests_failed: Some(0),
            total_tests: Some(10),
            events: Vec::new(),
        };

        store.store(state.clone()).unwrap();

        let loaded = store.load_all().unwrap();
        assert_eq!(loaded.len(), 1);
        assert_eq!(loaded[0].commit_id, Some("abc123".to_string()));
        assert!(loaded[0].compilation_success);
    }

    #[test]
    fn test_load_for_commit() {
        let temp = TempDir::new().unwrap();
        let store_path = temp.path().join("states.json");
        let store = StateStore::new(&store_path);

        store.init().unwrap();

        let state1 = BuildState::new()
            .with_commit("commit1".to_string())
            .mark_compilation_success();
        let state2 = BuildState::new().with_commit("commit2".to_string());

        store.store(state1).unwrap();
        store.store(state2).unwrap();

        let commit1_states = store.load_for_commit("commit1").unwrap();
        assert_eq!(commit1_states.len(), 1);
        assert!(commit1_states[0].compilation_success);
    }

    #[test]
    fn test_latest() {
        let temp = TempDir::new().unwrap();
        let store_path = temp.path().join("states.json");
        let store = StateStore::new(&store_path);

        store.init().unwrap();

        assert!(store.latest().unwrap().is_none());

        store
            .store(BuildState::new().with_commit("first".to_string()))
            .unwrap();
        store
            .store(BuildState::new().with_commit("second".to_string()))
            .unwrap();

        let latest = store.latest().unwrap().unwrap();
        assert_eq!(latest.commit_id, Some("second".to_string()));
    }

    #[test]
    fn test_clear() {
        let temp = TempDir::new().unwrap();
        let store_path = temp.path().join("states.json");
        let store = StateStore::new(&store_path);

        store.init().unwrap();
        store.store(BuildState::new()).unwrap();
        assert_eq!(store.load_all().unwrap().len(), 1);

        store.clear().unwrap();
        assert_eq!(store.load_all().unwrap().len(), 0);
    }
}

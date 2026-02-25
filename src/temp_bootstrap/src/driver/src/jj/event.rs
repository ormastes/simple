use serde::{Deserialize, Serialize};
use std::time::SystemTime;

/// Events captured during compilation and testing
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum BuildEvent {
    CompilationStarted {
        timestamp: SystemTime,
        files: Vec<String>,
    },
    CompilationSucceeded {
        timestamp: SystemTime,
        duration_ms: u64,
    },
    CompilationFailed {
        timestamp: SystemTime,
        duration_ms: u64,
        error: String,
    },
    TestStarted {
        timestamp: SystemTime,
        test_name: String,
    },
    TestPassed {
        timestamp: SystemTime,
        test_name: String,
        duration_ms: u64,
    },
    TestFailed {
        timestamp: SystemTime,
        test_name: String,
        duration_ms: u64,
        error: String,
    },
    AllTestsPassed {
        timestamp: SystemTime,
        total_tests: usize,
        total_duration_ms: u64,
    },
}

/// State snapshot at a specific point in time
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildState {
    pub timestamp: SystemTime,
    pub commit_id: Option<String>,
    pub compilation_success: bool,
    pub tests_passed: Option<usize>,
    pub tests_failed: Option<usize>,
    pub total_tests: Option<usize>,
    pub events: Vec<BuildEvent>,
}

impl BuildState {
    pub fn new() -> Self {
        Self {
            timestamp: SystemTime::now(),
            commit_id: None,
            compilation_success: false,
            tests_passed: None,
            tests_failed: None,
            total_tests: None,
            events: Vec::new(),
        }
    }

    pub fn with_commit(mut self, commit_id: String) -> Self {
        self.commit_id = Some(commit_id);
        self
    }

    pub fn mark_compilation_success(mut self) -> Self {
        self.compilation_success = true;
        self
    }

    pub fn set_test_results(mut self, passed: usize, failed: usize, total: usize) -> Self {
        self.tests_passed = Some(passed);
        self.tests_failed = Some(failed);
        self.total_tests = Some(total);
        self
    }

    pub fn add_event(mut self, event: BuildEvent) -> Self {
        self.events.push(event);
        self
    }
}

impl Default for BuildState {
    fn default() -> Self {
        Self::new()
    }
}

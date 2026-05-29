//! Data structures for the test database.

use crate::string_interner::StringInterner;
use crate::unified_db::Record;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Debug logging level for test database
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DebugLevel {
    None,
    Basic,
    Detailed,
    Trace,
}

impl DebugLevel {
    pub fn from_env() -> Self {
        match std::env::var("SIMPLE_TEST_DEBUG").as_deref() {
            Ok("trace") | Ok("TRACE") => DebugLevel::Trace,
            Ok("detailed") | Ok("DETAILED") => DebugLevel::Detailed,
            Ok("basic") | Ok("BASIC") => DebugLevel::Basic,
            _ => DebugLevel::None,
        }
    }

    pub fn is_enabled(level: DebugLevel) -> bool {
        Self::from_env() >= level
    }
}

macro_rules! debug_log {
    ($level:expr, $phase:expr, $($arg:tt)*) => {
        if $crate::test_db::types::DebugLevel::is_enabled($level) {
            eprintln!("[DEBUG:{}] {}", $phase, format!($($arg)*));
        }
    };
}
pub(crate) use debug_log;

// ============================================================================
// V3 Tree Structures
// ============================================================================

/// File record in the tree hierarchy.
#[derive(Debug, Clone)]
pub struct FileRecord {
    pub file_id: u32,
    pub path_str: u32, // interned string ID
}

/// Suite record in the tree hierarchy.
#[derive(Debug, Clone)]
pub struct SuiteRecord {
    pub suite_id: u32,
    pub file_id: u32,
    pub name_str: u32, // interned string ID
}

/// Status change type for tracking transitions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, Default)]
pub enum ChangeType {
    #[default]
    NoChange,
    PassToFail,
    FailToPass,
    NewTest,
    SkipToPass,
    SkipToFail,
    PassToSkip,
    FailToSkip,
}

impl std::fmt::Display for ChangeType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ChangeType::NoChange => write!(f, "no_change"),
            ChangeType::PassToFail => write!(f, "pass_to_fail"),
            ChangeType::FailToPass => write!(f, "fail_to_pass"),
            ChangeType::NewTest => write!(f, "new_test"),
            ChangeType::SkipToPass => write!(f, "skip_to_pass"),
            ChangeType::SkipToFail => write!(f, "skip_to_fail"),
            ChangeType::PassToSkip => write!(f, "pass_to_skip"),
            ChangeType::FailToSkip => write!(f, "fail_to_skip"),
        }
    }
}

impl ChangeType {
    pub fn parse_str(s: &str) -> Self {
        match s {
            "no_change" => ChangeType::NoChange,
            "pass_to_fail" => ChangeType::PassToFail,
            "fail_to_pass" => ChangeType::FailToPass,
            "new_test" => ChangeType::NewTest,
            "skip_to_pass" => ChangeType::SkipToPass,
            "skip_to_fail" => ChangeType::SkipToFail,
            "pass_to_skip" => ChangeType::PassToSkip,
            "fail_to_skip" => ChangeType::FailToSkip,
            _ => ChangeType::NoChange,
        }
    }
}

/// Timing summary for a test (volatile, stored in runs file).
#[derive(Debug, Clone)]
pub struct TimingSummary {
    pub test_id: u32,
    pub last_ms: f64,
    pub p50: f64,
    pub p90: f64,
    pub p95: f64,
    pub baseline_median: f64,
}

/// Single timing run (volatile).
#[derive(Debug, Clone)]
pub struct TimingRunEntry {
    pub test_id: u32,
    pub timestamp: String,
    pub duration_ms: f64,
    pub outlier: bool,
}

/// A change event recording a status transition.
#[derive(Debug, Clone)]
pub struct ChangeEvent {
    pub test_id: u32,
    pub change_type: ChangeType,
    pub run_id: String,
}

// ============================================================================
// Core Types (preserved from V2 for API compat)
// ============================================================================

/// Test database — V3 with tree structure and interning.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestDb {
    pub version: String,
    pub last_updated: String,
    pub records: HashMap<String, TestRecord>,
    pub config: TestDbConfig,

    // V3 fields (not serialized via serde — handled manually)
    #[serde(skip)]
    pub interner: StringInterner,
    #[serde(skip)]
    pub files: Vec<FileRecord>,
    #[serde(skip)]
    pub suites: Vec<SuiteRecord>,
    #[serde(skip)]
    pub timing_summaries: HashMap<u32, TimingSummary>,
    #[serde(skip)]
    pub timing_runs: HashMap<u32, Vec<TimingRunEntry>>,
    #[serde(skip)]
    pub changes: Vec<ChangeEvent>,
    #[serde(skip)]
    pub dirty: bool,
}

/// Test execution record
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestRecord {
    // Identification
    pub test_id: String,
    pub test_name: String,
    pub test_file: String,
    pub category: String,

    // Execution status
    pub status: TestStatus,
    pub last_run: String,

    // Failure information
    pub failure: Option<TestFailure>,

    // Execution history
    pub execution_history: ExecutionHistory,

    // Timing statistics
    pub timing: TimingData,

    // Timing configuration
    pub timing_config: Option<TimingConfig>,

    // Links
    pub related_bugs: Vec<String>,
    pub related_features: Vec<String>,

    // Metadata
    pub tags: Vec<String>,
    pub description: String,

    // Record validity
    pub valid: bool,

    // Qualified ignore fields
    #[serde(skip_serializing_if = "Option::is_none")]
    pub qualified_by: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub qualified_at: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub qualified_reason: Option<String>,

    // V3 fields
    #[serde(skip)]
    pub suite_id: Option<u32>,
    #[serde(skip)]
    pub name_str_id: Option<u32>,
    #[serde(skip)]
    pub category_str_id: Option<u32>,
    #[serde(skip)]
    pub status_str_id: Option<u32>,
    #[serde(skip)]
    pub last_change: ChangeType,
    #[serde(skip)]
    pub flaky_count: u32,
}

/// Implement Record trait for unified database access
impl Record for TestRecord {
    fn id(&self) -> String {
        self.test_id.clone()
    }

    fn table_name() -> &'static str {
        "tests"
    }

    fn field_names() -> &'static [&'static str] {
        &[
            "test_id",
            "test_name",
            "test_file",
            "category",
            "status",
            "last_run",
            "failure",
            "execution_history",
            "timing",
            "timing_config",
            "related_bugs",
            "related_features",
            "tags",
            "description",
            "valid",
            "qualified_by",
            "qualified_at",
            "qualified_reason",
        ]
    }

    fn from_sdn_row(row: &[String]) -> Result<Self, String> {
        let get_field = |idx: usize| row.get(idx).cloned().unwrap_or_default();

        let status = match get_field(4).as_str() {
            "passed" => TestStatus::Passed,
            "failed" => TestStatus::Failed,
            "skipped" => TestStatus::Skipped,
            "ignored" => TestStatus::Ignored,
            "qualifiedignore" | "qualified_ignore" => TestStatus::QualifiedIgnore,
            _ => TestStatus::Skipped,
        };

        let failure: Option<TestFailure> = {
            let json = get_field(6);
            if json.is_empty() {
                None
            } else {
                serde_json::from_str(&json).ok()
            }
        };

        let execution_history: ExecutionHistory =
            serde_json::from_str(&get_field(7)).unwrap_or_else(|_| ExecutionHistory::default());

        let timing: TimingData = serde_json::from_str(&get_field(8)).unwrap_or_else(|_| TimingData::default());

        let timing_config: Option<TimingConfig> = {
            let json = get_field(9);
            if json.is_empty() {
                None
            } else {
                serde_json::from_str(&json).ok()
            }
        };

        let qualified_by = {
            let s = get_field(15);
            if s.is_empty() {
                None
            } else {
                Some(s)
            }
        };
        let qualified_at = {
            let s = get_field(16);
            if s.is_empty() {
                None
            } else {
                Some(s)
            }
        };
        let qualified_reason = {
            let s = get_field(17);
            if s.is_empty() {
                None
            } else {
                Some(s)
            }
        };

        Ok(TestRecord {
            test_id: get_field(0),
            test_name: get_field(1),
            test_file: get_field(2),
            category: get_field(3),
            status,
            last_run: get_field(5),
            failure,
            execution_history,
            timing,
            timing_config,
            related_bugs: get_field(10)
                .split(',')
                .filter(|s| !s.is_empty())
                .map(|s| s.to_string())
                .collect(),
            related_features: get_field(11)
                .split(',')
                .filter(|s| !s.is_empty())
                .map(|s| s.to_string())
                .collect(),
            tags: get_field(12)
                .split(',')
                .filter(|s| !s.is_empty())
                .map(|s| s.to_string())
                .collect(),
            description: get_field(13),
            valid: get_field(14) == "true",
            qualified_by,
            qualified_at,
            qualified_reason,
            suite_id: None,
            name_str_id: None,
            category_str_id: None,
            status_str_id: None,
            last_change: ChangeType::NoChange,
            flaky_count: 0,
        })
    }

    fn to_sdn_row(&self) -> Vec<String> {
        let status_str = match self.status {
            TestStatus::Passed => "passed",
            TestStatus::Failed => "failed",
            TestStatus::Skipped => "skipped",
            TestStatus::Ignored => "ignored",
            TestStatus::QualifiedIgnore => "qualifiedignore",
        };

        let failure_json = self
            .failure
            .as_ref()
            .map(|f| serde_json::to_string(f).unwrap_or_default())
            .unwrap_or_default();
        let history_json = serde_json::to_string(&self.execution_history).unwrap_or_default();
        let timing_json = serde_json::to_string(&self.timing).unwrap_or_default();
        let timing_config_json = self
            .timing_config
            .as_ref()
            .map(|c| serde_json::to_string(c).unwrap_or_default())
            .unwrap_or_default();

        vec![
            self.test_id.clone(),
            self.test_name.clone(),
            self.test_file.clone(),
            self.category.clone(),
            status_str.to_string(),
            self.last_run.clone(),
            failure_json,
            history_json,
            timing_json,
            timing_config_json,
            self.related_bugs.join(","),
            self.related_features.join(","),
            self.tags.join(","),
            self.description.clone(),
            self.valid.to_string(),
            self.qualified_by.clone().unwrap_or_default(),
            self.qualified_at.clone().unwrap_or_default(),
            self.qualified_reason.clone().unwrap_or_default(),
        ]
    }
}

/// Test execution status
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum TestStatus {
    Passed,
    Failed,
    Skipped,
    Ignored,
    QualifiedIgnore,
}

/// Test failure information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestFailure {
    pub error_message: String,
    pub assertion_failed: Option<String>,
    pub location: Option<String>,
    pub stack_trace: Option<String>,
}

/// Execution history tracking
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionHistory {
    pub total_runs: usize,
    pub passed: usize,
    pub failed: usize,
    pub last_10_runs: Vec<String>,
    pub flaky: bool,
    pub failure_rate_pct: f64,
}

/// Timing data
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimingData {
    pub baseline_median: f64,
    pub baseline_mean: f64,
    pub baseline_std_dev: f64,
    pub baseline_cv_pct: f64,
    pub last_run_time: f64,
    pub history: TimingHistory,
    pub p50: f64,
    pub p90: f64,
    pub p95: f64,
    pub p99: f64,
    pub min_time: f64,
    pub max_time: f64,
    pub iqr: f64,
    pub baseline_last_updated: String,
    pub baseline_run_count: usize,
    pub baseline_update_reason: String,
}

/// Timing history
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimingHistory {
    pub window_size: usize,
    pub runs: Vec<TimingRun>,
}

/// Single timing run
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimingRun {
    pub timestamp: String,
    pub duration_ms: f64,
    pub outlier: bool,
}

/// Timing configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimingConfig {
    pub update_threshold_pct: f64,
    pub alert_threshold_pct: f64,
    pub std_dev_threshold: f64,
    pub min_sample_size: usize,
    pub max_sample_size: usize,
    pub use_median: bool,
    pub outlier_method: String,
}

/// Test database configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestDbConfig {
    pub default_timing_config: TimingConfig,
    pub update_rules: UpdateRules,
}

/// Update rules
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UpdateRules {
    pub update_on_all_tests_run: bool,
    pub track_top_variance_pct: f64,
    pub rewrite_top_variance: bool,
}

// ============================================================================
// Default Implementations
// ============================================================================

impl Default for TestDb {
    fn default() -> Self {
        Self::new()
    }
}

impl TestDb {
    pub fn new() -> Self {
        TestDb {
            version: "3.0".to_string(),
            last_updated: chrono::Utc::now().to_rfc3339(),
            records: HashMap::new(),
            config: TestDbConfig {
                default_timing_config: TimingConfig {
                    update_threshold_pct: 5.0,
                    alert_threshold_pct: 10.0,
                    std_dev_threshold: 4.0,
                    min_sample_size: 10,
                    max_sample_size: 10,
                    use_median: true,
                    outlier_method: "MAD".to_string(),
                },
                update_rules: UpdateRules {
                    update_on_all_tests_run: true,
                    track_top_variance_pct: 5.0,
                    rewrite_top_variance: false,
                },
            },
            interner: StringInterner::new(),
            files: Vec::new(),
            suites: Vec::new(),
            timing_summaries: HashMap::new(),
            timing_runs: HashMap::new(),
            changes: Vec::new(),
            dirty: false,
        }
    }

    pub fn valid_records(&self) -> Vec<&TestRecord> {
        self.records.values().filter(|r| r.valid).collect()
    }

    /// Get or create a suite for a file+suite combo, returning suite_id.
    pub fn get_or_create_suite(&mut self, file_path: &str, suite_name: &str) -> u32 {
        let path_str_id = self.interner.intern(file_path);
        let name_str_id = self.interner.intern(suite_name);

        // Find existing file
        let file_id = if let Some(f) = self.files.iter().find(|f| f.path_str == path_str_id) {
            f.file_id
        } else {
            let id = self.files.len() as u32;
            self.files.push(FileRecord {
                file_id: id,
                path_str: path_str_id,
            });
            id
        };

        // Find existing suite
        if let Some(s) = self
            .suites
            .iter()
            .find(|s| s.file_id == file_id && s.name_str == name_str_id)
        {
            s.suite_id
        } else {
            let id = self.suites.len() as u32;
            self.suites.push(SuiteRecord {
                suite_id: id,
                file_id,
                name_str: name_str_id,
            });
            id
        }
    }

    /// Build the interner and tree from existing records (for migration or after V2 load).
    pub fn rebuild_tree(&mut self) {
        self.interner = StringInterner::new();
        self.files = Vec::new();
        self.suites = Vec::new();

        // Pre-intern common status strings
        self.interner.intern("passed");
        self.interner.intern("failed");
        self.interner.intern("skipped");
        self.interner.intern("ignored");
        self.interner.intern("qualifiedignore");

        // Collect data from records first to avoid borrow conflict
        let record_data: Vec<(String, String, String, String, String, TestStatus)> = self
            .records
            .values()
            .map(|r| {
                let parts: Vec<&str> = r.test_id.splitn(3, "::").collect();
                let suite_name = if parts.len() >= 2 {
                    parts[1].to_string()
                } else {
                    "default".to_string()
                };
                (
                    r.test_id.clone(),
                    r.test_file.clone(),
                    suite_name,
                    r.test_name.clone(),
                    r.category.clone(),
                    r.status,
                )
            })
            .collect();

        for (test_id, file_path, suite_name, test_name, category, status) in record_data {
            let suite_id = self.get_or_create_suite(&file_path, &suite_name);
            let name_str_id = self.interner.intern(&test_name);
            let category_str_id = self.interner.intern(&category);
            let status_str_id = self.interner.intern(match status {
                TestStatus::Passed => "passed",
                TestStatus::Failed => "failed",
                TestStatus::Skipped => "skipped",
                TestStatus::Ignored => "ignored",
                TestStatus::QualifiedIgnore => "qualifiedignore",
            });

            if let Some(record) = self.records.get_mut(&test_id) {
                record.suite_id = Some(suite_id);
                record.name_str_id = Some(name_str_id);
                record.category_str_id = Some(category_str_id);
                record.status_str_id = Some(status_str_id);
            }
        }
    }

    /// Build timing summaries from records (for migration).
    pub fn rebuild_timing_from_records(&mut self) {
        self.timing_summaries.clear();
        self.timing_runs.clear();

        for record in self.records.values() {
            // Get test's numeric ID from suite_id
            if let Some(name_id) = record.name_str_id {
                let summary = TimingSummary {
                    test_id: name_id,
                    last_ms: record.timing.last_run_time,
                    p50: record.timing.p50,
                    p90: record.timing.p90,
                    p95: record.timing.p95,
                    baseline_median: record.timing.baseline_median,
                };
                self.timing_summaries.insert(name_id, summary);

                // Extract last 10 timing runs
                let runs: Vec<TimingRunEntry> = record
                    .timing
                    .history
                    .runs
                    .iter()
                    .take(10)
                    .map(|r| TimingRunEntry {
                        test_id: name_id,
                        timestamp: r.timestamp.clone(),
                        duration_ms: r.duration_ms,
                        outlier: r.outlier,
                    })
                    .collect();
                if !runs.is_empty() {
                    self.timing_runs.insert(name_id, runs);
                }
            }
        }
    }
}

impl Default for ExecutionHistory {
    fn default() -> Self {
        ExecutionHistory {
            total_runs: 0,
            passed: 0,
            failed: 0,
            last_10_runs: Vec::new(),
            flaky: false,
            failure_rate_pct: 0.0,
        }
    }
}

impl Default for TimingData {
    fn default() -> Self {
        TimingData {
            baseline_median: 0.0,
            baseline_mean: 0.0,
            baseline_std_dev: 0.0,
            baseline_cv_pct: 0.0,
            last_run_time: 0.0,
            history: TimingHistory {
                window_size: 10,
                runs: Vec::new(),
            },
            p50: 0.0,
            p90: 0.0,
            p95: 0.0,
            p99: 0.0,
            min_time: 0.0,
            max_time: 0.0,
            iqr: 0.0,
            baseline_last_updated: chrono::Utc::now().to_rfc3339(),
            baseline_run_count: 0,
            baseline_update_reason: "initial".to_string(),
        }
    }
}

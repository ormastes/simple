//! Test execution database - tracks test results and timing.
//!
//! V3 format: Tree structure + string interning + split stable/volatile files.
//!
//! - `test_db.sdn` — stable data (strings, files, suites, tests) tracked in jj
//! - `test_db_runs.sdn` — volatile data (timing, runs, changes) jj-ignored
//!
//! Auto-generates: doc/test/test_result.md

use crate::db_lock::FileLock;
use crate::string_interner::StringInterner;
use crate::test_stats::{compute_statistics, detect_outliers, has_significant_change, OutlierMethod};
use crate::unified_db::Record;
use serde::{Deserialize, Serialize};
use simple_sdn::{parse_document, SdnValue};
use std::collections::HashMap;
use std::fs;
use std::path::Path;

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
        if DebugLevel::is_enabled($level) {
            eprintln!("[DEBUG:{}] {}", $phase, format!($($arg)*));
        }
    };
}

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
    pub fn from_str(s: &str) -> Self {
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
// Test Run Tracking
// ============================================================================

/// Status of a test run session
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum TestRunStatus {
    Running,
    Completed,
    Crashed,
    TimedOut,
    Interrupted,
}

impl std::fmt::Display for TestRunStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TestRunStatus::Running => write!(f, "running"),
            TestRunStatus::Completed => write!(f, "completed"),
            TestRunStatus::Crashed => write!(f, "crashed"),
            TestRunStatus::TimedOut => write!(f, "timed_out"),
            TestRunStatus::Interrupted => write!(f, "interrupted"),
        }
    }
}

impl TestRunStatus {
    pub fn from_str(s: &str) -> Self {
        match s {
            "running" => TestRunStatus::Running,
            "completed" => TestRunStatus::Completed,
            "crashed" => TestRunStatus::Crashed,
            "timed_out" => TestRunStatus::TimedOut,
            "interrupted" => TestRunStatus::Interrupted,
            _ => TestRunStatus::Running,
        }
    }
}

/// A test run record
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestRunRecord {
    pub run_id: String,
    pub start_time: String,
    pub end_time: String,
    pub pid: u32,
    pub hostname: String,
    pub status: TestRunStatus,
    pub test_count: usize,
    pub passed: usize,
    pub failed: usize,
    pub crashed: usize,
    pub timed_out: usize,
}

impl TestRunRecord {
    pub fn new_running() -> Self {
        let now = chrono::Utc::now();
        TestRunRecord {
            run_id: format!("run_{}", now.format("%Y%m%d_%H%M%S_%3f")),
            start_time: now.to_rfc3339(),
            end_time: String::new(),
            pid: std::process::id(),
            hostname: hostname::get()
                .map(|h| h.to_string_lossy().to_string())
                .unwrap_or_else(|_| "unknown".to_string()),
            status: TestRunStatus::Running,
            test_count: 0,
            passed: 0,
            failed: 0,
            crashed: 0,
            timed_out: 0,
        }
    }

    pub fn mark_completed(&mut self) {
        self.end_time = chrono::Utc::now().to_rfc3339();
        self.status = TestRunStatus::Completed;
    }

    pub fn mark_crashed(&mut self) {
        self.end_time = chrono::Utc::now().to_rfc3339();
        self.status = TestRunStatus::Crashed;
    }

    pub fn is_stale(&self, max_hours: i64) -> bool {
        if self.status != TestRunStatus::Running {
            return false;
        }
        if let Ok(start) = chrono::DateTime::parse_from_rfc3339(&self.start_time) {
            let elapsed = chrono::Utc::now().signed_duration_since(start);
            return elapsed.num_hours() >= max_hours;
        }
        false
    }

    pub fn is_process_alive(&self) -> bool {
        #[cfg(unix)]
        {
            unsafe { libc::kill(self.pid as i32, 0) == 0 }
        }
        #[cfg(not(unix))]
        {
            true
        }
    }

    pub fn validate_record(&self) -> crate::unified_db::IntegrityReport {
        use crate::unified_db::{IntegrityReport, IntegrityViolation, ViolationType};

        let mut report = IntegrityReport::new(&self.run_id);

        if self.status == TestRunStatus::Running && self.is_stale(2) {
            report.add_violation(
                IntegrityViolation::new(
                    ViolationType::StaleRunning,
                    "status",
                    format!("Run has been 'running' for >2 hours (started: {})", self.start_time),
                )
                .with_expected("Completed or Crashed")
                .with_actual("Running"),
            );
            report = report.mark_auto_fixable();
        }

        if self.status == TestRunStatus::Running && !self.is_process_alive() {
            report.add_violation(
                IntegrityViolation::new(
                    ViolationType::DeadProcess,
                    "pid",
                    format!("Process {} is not running but status is 'running'", self.pid),
                )
                .with_expected("Running process or Crashed status")
                .with_actual(format!("Dead process, status={:?}", self.status)),
            );
            report = report.mark_auto_fixable();
        }

        match chrono::DateTime::parse_from_rfc3339(&self.start_time) {
            Ok(start) => {
                if start > chrono::Utc::now() {
                    report.add_violation(
                        IntegrityViolation::new(
                            ViolationType::FutureTimestamp,
                            "start_time",
                            "Start time is in the future",
                        )
                        .with_expected("Past or present")
                        .with_actual(self.start_time.clone()),
                    );
                }

                if !self.end_time.is_empty() {
                    match chrono::DateTime::parse_from_rfc3339(&self.end_time) {
                        Ok(end) => {
                            if end <= start {
                                report.add_violation(
                                    IntegrityViolation::new(
                                        ViolationType::TimestampInconsistent,
                                        "end_time",
                                        "End time is before or equal to start time",
                                    )
                                    .with_expected(format!("After {}", self.start_time))
                                    .with_actual(self.end_time.clone()),
                                );
                            }
                        }
                        Err(e) => {
                            report.add_violation(
                                IntegrityViolation::new(
                                    ViolationType::InvalidValue,
                                    "end_time",
                                    format!("Invalid timestamp format: {}", e),
                                )
                                .with_actual(self.end_time.clone()),
                            );
                        }
                    }
                }
            }
            Err(e) => {
                report.add_violation(
                    IntegrityViolation::new(
                        ViolationType::InvalidValue,
                        "start_time",
                        format!("Invalid timestamp format: {}", e),
                    )
                    .with_actual(self.start_time.clone()),
                );
            }
        }

        let sum = self.passed + self.failed + self.crashed + self.timed_out;
        if sum > self.test_count {
            report.add_violation(
                IntegrityViolation::new(
                    ViolationType::CountInconsistent,
                    "test_count",
                    format!(
                        "Sum of results ({}) exceeds total test count ({})",
                        sum, self.test_count
                    ),
                )
                .with_expected(format!("≥ {}", sum))
                .with_actual(self.test_count.to_string()),
            );
        }

        match self.status {
            TestRunStatus::Completed
            | TestRunStatus::Crashed
            | TestRunStatus::TimedOut
            | TestRunStatus::Interrupted => {
                if self.end_time.is_empty() {
                    report.add_violation(
                        IntegrityViolation::new(
                            ViolationType::StatusInconsistent,
                            "end_time",
                            format!("Status is {:?} but end_time is empty", self.status),
                        )
                        .with_expected("Non-empty timestamp")
                        .with_actual("(empty)"),
                    );
                }
            }
            TestRunStatus::Running => {
                if !self.end_time.is_empty() {
                    report.add_violation(
                        IntegrityViolation::new(
                            ViolationType::StatusInconsistent,
                            "end_time",
                            "Status is Running but end_time is set",
                        )
                        .with_expected("(empty)")
                        .with_actual(self.end_time.clone()),
                    );
                }
            }
        }

        report
    }
}

impl Record for TestRunRecord {
    fn id(&self) -> String {
        self.run_id.clone()
    }

    fn table_name() -> &'static str {
        "test_runs"
    }

    fn field_names() -> &'static [&'static str] {
        &[
            "run_id",
            "start_time",
            "end_time",
            "pid",
            "hostname",
            "status",
            "test_count",
            "passed",
            "failed",
            "crashed",
            "timed_out",
        ]
    }

    fn from_sdn_row(row: &[String]) -> Result<Self, String> {
        Ok(TestRunRecord {
            run_id: row.get(0).cloned().unwrap_or_default(),
            start_time: row.get(1).cloned().unwrap_or_default(),
            end_time: row.get(2).cloned().unwrap_or_default(),
            pid: row.get(3).and_then(|s| s.parse().ok()).unwrap_or(0),
            hostname: row.get(4).cloned().unwrap_or_default(),
            status: TestRunStatus::from_str(row.get(5).map(|s| s.as_str()).unwrap_or("running")),
            test_count: row.get(6).and_then(|s| s.parse().ok()).unwrap_or(0),
            passed: row.get(7).and_then(|s| s.parse().ok()).unwrap_or(0),
            failed: row.get(8).and_then(|s| s.parse().ok()).unwrap_or(0),
            crashed: row.get(9).and_then(|s| s.parse().ok()).unwrap_or(0),
            timed_out: row.get(10).and_then(|s| s.parse().ok()).unwrap_or(0),
        })
    }

    fn to_sdn_row(&self) -> Vec<String> {
        vec![
            self.run_id.clone(),
            self.start_time.clone(),
            self.end_time.clone(),
            self.pid.to_string(),
            self.hostname.clone(),
            self.status.to_string(),
            self.test_count.to_string(),
            self.passed.to_string(),
            self.failed.to_string(),
            self.crashed.to_string(),
            self.timed_out.to_string(),
        ]
    }

    fn validate(&self) -> crate::unified_db::IntegrityReport {
        self.validate_record()
    }
}

// ============================================================================
// Test Run Management Functions
// ============================================================================

use crate::unified_db::Database;

pub fn load_test_runs(db_path: &Path) -> Result<Database<TestRunRecord>, String> {
    // V3: load from runs file if it exists, fall back to main db
    let runs_path = runs_file_path(db_path);
    if runs_path.exists() {
        return Database::<TestRunRecord>::load(&runs_path);
    }
    Database::<TestRunRecord>::load(db_path)
}

pub fn save_test_runs(db: &Database<TestRunRecord>) -> Result<(), String> {
    db.save().map_err(|e| e.to_string())
}

pub fn start_test_run(db_path: &Path) -> Result<TestRunRecord, String> {
    let runs_path = runs_file_path(db_path);
    let load_path = if runs_path.exists() { &runs_path } else { db_path };
    let mut db = Database::<TestRunRecord>::load(load_path)?;
    // Ensure we save to runs file going forward
    let run = TestRunRecord::new_running();
    db.insert(run.clone());
    // Save to runs file
    let mut runs_db = Database::<TestRunRecord>::new(&runs_path);
    for (id, rec) in &db.records {
        runs_db.records.insert(id.clone(), rec.clone());
    }
    runs_db.save().map_err(|e| e.to_string())?;
    Ok(run)
}

pub fn update_test_run(db_path: &Path, run: &TestRunRecord) -> Result<(), String> {
    let runs_path = runs_file_path(db_path);
    let load_path = if runs_path.exists() { &runs_path } else { db_path };
    let mut db = Database::<TestRunRecord>::load(load_path)?;
    db.insert(run.clone());
    // Always save to runs file
    let mut runs_db = Database::<TestRunRecord>::new(&runs_path);
    for (id, rec) in &db.records {
        runs_db.records.insert(id.clone(), rec.clone());
    }
    runs_db.save().map_err(|e| e.to_string())
}

pub fn complete_test_run(
    db_path: &Path,
    run_id: &str,
    test_count: usize,
    passed: usize,
    failed: usize,
    crashed: usize,
    timed_out: usize,
) -> Result<(), String> {
    let runs_path = runs_file_path(db_path);
    let load_path = if runs_path.exists() { &runs_path } else { db_path };
    let mut db = Database::<TestRunRecord>::load(load_path)?;
    if let Some(run) = db.get_mut(run_id) {
        run.mark_completed();
        run.test_count = test_count;
        run.passed = passed;
        run.failed = failed;
        run.crashed = crashed;
        run.timed_out = timed_out;
    }
    let mut runs_db = Database::<TestRunRecord>::new(&runs_path);
    for (id, rec) in &db.records {
        runs_db.records.insert(id.clone(), rec.clone());
    }
    runs_db.save().map_err(|e| e.to_string())
}

pub fn mark_run_crashed(db_path: &Path, run_id: &str) -> Result<(), String> {
    let runs_path = runs_file_path(db_path);
    let load_path = if runs_path.exists() { &runs_path } else { db_path };
    let mut db = Database::<TestRunRecord>::load(load_path)?;
    if let Some(run) = db.get_mut(run_id) {
        run.mark_crashed();
    }
    let mut runs_db = Database::<TestRunRecord>::new(&runs_path);
    for (id, rec) in &db.records {
        runs_db.records.insert(id.clone(), rec.clone());
    }
    runs_db.save().map_err(|e| e.to_string())
}

pub fn cleanup_stale_runs(db_path: &Path, max_hours: i64) -> Result<Vec<String>, String> {
    let runs_path = runs_file_path(db_path);
    let load_path = if runs_path.exists() { &runs_path } else { db_path };
    let mut db = Database::<TestRunRecord>::load(load_path)?;
    let mut cleaned = Vec::new();

    let stale_ids: Vec<String> = db
        .records
        .values()
        .filter(|r| r.status == TestRunStatus::Running)
        .filter(|r| r.is_stale(max_hours) || !r.is_process_alive())
        .map(|r| r.run_id.clone())
        .collect();

    for run_id in stale_ids {
        if let Some(run) = db.get_mut(&run_id) {
            run.mark_crashed();
            cleaned.push(run_id);
        }
    }

    if !cleaned.is_empty() {
        let mut runs_db = Database::<TestRunRecord>::new(&runs_path);
        for (id, rec) in &db.records {
            runs_db.records.insert(id.clone(), rec.clone());
        }
        runs_db.save().map_err(|e| e.to_string())?;
    }

    Ok(cleaned)
}

pub fn prune_old_runs(db_path: &Path, keep_count: usize) -> Result<usize, String> {
    let runs_path = runs_file_path(db_path);
    let load_path = if runs_path.exists() { &runs_path } else { db_path };
    let mut db = Database::<TestRunRecord>::load(load_path)?;

    let mut runs: Vec<_> = db.records.values().cloned().collect();
    runs.sort_by(|a, b| b.start_time.cmp(&a.start_time));

    let to_delete: Vec<String> = runs.iter().skip(keep_count).map(|r| r.run_id.clone()).collect();

    let deleted_count = to_delete.len();
    for run_id in to_delete {
        db.delete(&run_id);
    }

    if deleted_count > 0 {
        let mut runs_db = Database::<TestRunRecord>::new(&runs_path);
        for (id, rec) in &db.records {
            runs_db.records.insert(id.clone(), rec.clone());
        }
        runs_db.save().map_err(|e| e.to_string())?;
    }

    Ok(deleted_count)
}

pub fn list_runs(db_path: &Path, status_filter: Option<TestRunStatus>) -> Result<Vec<TestRunRecord>, String> {
    let runs_path = runs_file_path(db_path);
    let load_path = if runs_path.exists() { &runs_path } else { db_path };
    let db = Database::<TestRunRecord>::load(load_path)?;
    let mut runs: Vec<_> = db
        .records
        .values()
        .filter(|r| status_filter.is_none() || Some(r.status) == status_filter)
        .cloned()
        .collect();

    runs.sort_by(|a, b| b.start_time.cmp(&a.start_time));
    Ok(runs)
}

pub fn get_running_runs(db_path: &Path) -> Result<Vec<TestRunRecord>, String> {
    list_runs(db_path, Some(TestRunStatus::Running))
}

// ============================================================================
// Helper: runs file path
// ============================================================================

fn runs_file_path(db_path: &Path) -> std::path::PathBuf {
    let parent = db_path.parent().unwrap_or(Path::new("."));
    parent.join("test_db_runs.sdn")
}

// ============================================================================
// TestDb Implementation
// ============================================================================

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

// ============================================================================
// V3 Format Detection
// ============================================================================

/// Check if content is V3 format (has `strings` table).
fn is_v3_format(content: &str) -> bool {
    content.contains("strings |") || content.contains("strings|")
}

// ============================================================================
// Load
// ============================================================================

/// Load test database from SDN file.
pub fn load_test_db(path: &Path) -> Result<TestDb, String> {
    if !path.exists() {
        return Ok(TestDb::new());
    }

    let _lock = FileLock::acquire(path, 10).map_err(|e| format!("Failed to acquire lock: {:?}", e))?;

    let file_size = fs::metadata(path)
        .map_err(|e| format!("Failed to stat file: {}", e))?
        .len();
    const MAX_DB_SIZE: u64 = 500 * 1024 * 1024;
    if file_size > MAX_DB_SIZE {
        eprintln!(
            "[WARNING] Test database file is too large ({:.1} GB, limit is {:.0} MB). \
             The database will be reset. Old file preserved as .sdn.oversized",
            file_size as f64 / (1024.0 * 1024.0 * 1024.0),
            MAX_DB_SIZE as f64 / (1024.0 * 1024.0),
        );
        let backup_path = path.with_extension("sdn.oversized");
        if let Err(e) = fs::rename(path, &backup_path) {
            eprintln!("[WARNING] Failed to rename oversized file: {}", e);
        } else {
            eprintln!("[INFO] Oversized database moved to: {}", backup_path.display());
        }
        return Ok(TestDb::new());
    }

    let content = fs::read_to_string(path).map_err(|e| format!("Failed to read file: {}", e))?;

    if content.trim().is_empty() {
        return Ok(TestDb::new());
    }

    if is_v3_format(&content) {
        return load_test_db_v3(path, &content);
    }

    // V2 or older format — load then auto-migrate
    match parse_document(&content) {
        Ok(doc) => {
            let mut db = parse_test_db_sdn_v2(&doc)?;
            if db.records.is_empty() && content.lines().count() > 2 {
                debug_log!(
                    DebugLevel::Basic,
                    "TestDB",
                    "Warning: Database file has content but no records were parsed"
                );
            }
            // Auto-migrate to V3
            db.version = "3.0".to_string();
            db.rebuild_tree();
            db.rebuild_timing_from_records();
            // Save migrated format
            eprintln!("[INFO] Auto-migrating test_db.sdn from V2 to V3 format");
            let backup_path = path.with_extension("sdn.v2_backup");
            if let Err(e) = fs::copy(path, &backup_path) {
                debug_log!(
                    DebugLevel::Basic,
                    "TestDB",
                    "Warning: Failed to create V2 backup: {}",
                    e
                );
            }
            // Drop lock before saving (save acquires its own)
            drop(_lock);
            save_test_db(path, &db)?;
            Ok(db)
        }
        Err(sdn_err) => {
            // Fallback to JSON format
            serde_json::from_str(&content).map_err(|json_err| {
                format!(
                    "Failed to parse database - SDN error: {}, JSON error: {}",
                    sdn_err, json_err
                )
            })
        }
    }
}

/// Load V3 format test database.
fn load_test_db_v3(path: &Path, content: &str) -> Result<TestDb, String> {
    let doc = parse_document(content).map_err(|e| format!("Failed to parse V3 SDN: {}", e))?;
    let root = doc.root();

    let dict = match root {
        SdnValue::Dict(d) => d,
        _ => return Err("Expected dict at root of V3 test_db.sdn".to_string()),
    };

    let mut db = TestDb::new();

    // Load strings table
    if let Some(SdnValue::Table {
        fields: Some(_fields),
        rows,
        ..
    }) = dict.get("strings")
    {
        for row in rows {
            let id = match row.get(0) {
                Some(SdnValue::Int(n)) => *n as u32,
                Some(SdnValue::String(s)) => s.parse::<u32>().unwrap_or(0),
                _ => continue,
            };
            let value = match row.get(1) {
                Some(SdnValue::String(s)) => s.clone(),
                Some(SdnValue::Int(n)) => n.to_string(),
                _ => continue,
            };
            // Ensure sequential
            while db.interner.len() < id as usize {
                db.interner.intern("");
            }
            db.interner.intern(&value);
        }
    }

    // Load files table
    if let Some(SdnValue::Table {
        fields: Some(_), rows, ..
    }) = dict.get("files")
    {
        for row in rows {
            let file_id = sdn_row_u32(row, 0);
            let path_str = sdn_row_u32(row, 1);
            db.files.push(FileRecord { file_id, path_str });
        }
    }

    // Load suites table
    if let Some(SdnValue::Table {
        fields: Some(_), rows, ..
    }) = dict.get("suites")
    {
        for row in rows {
            let suite_id = sdn_row_u32(row, 0);
            let file_id = sdn_row_u32(row, 1);
            let name_str = sdn_row_u32(row, 2);
            db.suites.push(SuiteRecord {
                suite_id,
                file_id,
                name_str,
            });
        }
    }

    // Load tests table
    if let Some(SdnValue::Table {
        fields: Some(fields),
        rows,
        ..
    }) = dict.get("tests")
    {
        for row in rows {
            let get = |name: &str| -> String {
                fields
                    .iter()
                    .position(|f| f == name)
                    .and_then(|idx| row.get(idx))
                    .map(|v| match v {
                        SdnValue::String(s) => s.clone(),
                        SdnValue::Int(n) => n.to_string(),
                        SdnValue::Float(f) => f.to_string(),
                        SdnValue::Bool(b) => b.to_string(),
                        _ => String::new(),
                    })
                    .unwrap_or_default()
            };

            let test_id_idx = sdn_row_u32(row, 0);
            let suite_id = sdn_row_u32(row, 1);
            let name_str = sdn_row_u32(row, 2);
            let category_str = sdn_row_u32(row, 3);
            let status_str = sdn_row_u32(row, 4);

            // Resolve strings from interner
            let test_name = if (name_str as usize) < db.interner.len() {
                db.interner.get_or_empty(name_str).to_string()
            } else {
                format!("test_{}", test_id_idx)
            };

            let category = if (category_str as usize) < db.interner.len() {
                db.interner.get_or_empty(category_str).to_string()
            } else {
                "Unknown".to_string()
            };

            let status_s = if (status_str as usize) < db.interner.len() {
                db.interner.get_or_empty(status_str).to_string()
            } else {
                "passed".to_string()
            };

            let status = match status_s.as_str() {
                "passed" => TestStatus::Passed,
                "failed" => TestStatus::Failed,
                "skipped" => TestStatus::Skipped,
                "ignored" => TestStatus::Ignored,
                "qualifiedignore" | "qualified_ignore" => TestStatus::QualifiedIgnore,
                _ => TestStatus::Passed,
            };

            // Counters are loaded from volatile file; use defaults here,
            // then overwrite from counters table in load_volatile_data().
            let last_change_str = get("last_change");
            let last_change = if last_change_str.is_empty() {
                ChangeType::NoChange
            } else {
                ChangeType::from_str(&last_change_str)
            };

            let total_runs: usize = get("total_runs").parse().unwrap_or(0);
            let passed_count: usize = get("passed").parse().unwrap_or(0);
            let failed_count: usize = get("failed").parse().unwrap_or(0);
            let flaky_count: u32 = get("flaky_count").parse().unwrap_or(0);

            // Resolve file path from suite -> file
            let test_file = if let Some(suite) = db.suites.iter().find(|s| s.suite_id == suite_id) {
                if let Some(file) = db.files.iter().find(|f| f.file_id == suite.file_id) {
                    if (file.path_str as usize) < db.interner.len() {
                        db.interner.get_or_empty(file.path_str).to_string()
                    } else {
                        String::new()
                    }
                } else {
                    String::new()
                }
            } else {
                String::new()
            };

            // Reconstruct test_id from file::suite::name
            let suite_name = if let Some(suite) = db.suites.iter().find(|s| s.suite_id == suite_id) {
                if (suite.name_str as usize) < db.interner.len() {
                    db.interner.get_or_empty(suite.name_str).to_string()
                } else {
                    "default".to_string()
                }
            } else {
                "default".to_string()
            };
            let test_id = format!("{}::{}::{}", test_file, suite_name, test_name);

            let failure_rate_pct = if total_runs > 0 {
                (failed_count as f64 / total_runs as f64) * 100.0
            } else {
                0.0
            };

            let tags_str = get("tags_str");
            let tags: Vec<String> = if tags_str.is_empty() {
                Vec::new()
            } else {
                tags_str
                    .split(',')
                    .filter(|s| !s.is_empty())
                    .map(|s| s.to_string())
                    .collect()
            };

            let qualified_by = {
                let s = get("qualified_by");
                if s.is_empty() {
                    None
                } else {
                    Some(s)
                }
            };
            let qualified_at = {
                let s = get("qualified_at");
                if s.is_empty() {
                    None
                } else {
                    Some(s)
                }
            };
            let qualified_reason = {
                let s = get("qualified_reason");
                if s.is_empty() {
                    None
                } else {
                    Some(s)
                }
            };

            let record = TestRecord {
                test_id: test_id.clone(),
                test_name,
                test_file,
                category,
                status,
                last_run: String::new(), // Volatile — loaded from runs file
                failure: None,           // Volatile
                execution_history: ExecutionHistory {
                    total_runs,
                    passed: passed_count,
                    failed: failed_count,
                    last_10_runs: Vec::new(), // Rebuilt from timing_runs
                    flaky: flaky_count > 0,
                    failure_rate_pct,
                },
                timing: TimingData::default(), // Volatile — loaded from runs file
                timing_config: None,
                related_bugs: Vec::new(),
                related_features: Vec::new(),
                tags,
                description: get("description_str"),
                valid: get("valid") != "false",
                qualified_by,
                qualified_at,
                qualified_reason,
                suite_id: Some(suite_id),
                name_str_id: Some(name_str),
                category_str_id: Some(category_str),
                status_str_id: Some(status_str),
                last_change,
                flaky_count,
            };

            db.records.insert(test_id, record);
        }
    }

    // Load volatile data from runs file
    let runs_path = runs_file_path(path);
    if runs_path.exists() {
        load_volatile_data(&mut db, &runs_path)?;
    }

    Ok(db)
}

/// Load volatile timing/run data from test_db_runs.sdn.
fn load_volatile_data(db: &mut TestDb, runs_path: &Path) -> Result<(), String> {
    let content = fs::read_to_string(runs_path).map_err(|e| format!("Failed to read runs file: {}", e))?;
    if content.trim().is_empty() {
        return Ok(());
    }

    let doc = parse_document(&content).map_err(|e| format!("Failed to parse runs SDN: {}", e))?;
    let root = doc.root();
    let dict = match root {
        SdnValue::Dict(d) => d,
        _ => return Ok(()), // No dict root, skip
    };

    // Load counters (total_runs, passed, failed, flaky_count, last_change)
    if let Some(SdnValue::Table { rows, .. }) = dict.get("counters") {
        for row in rows {
            let test_id = sdn_row_u32(row, 0);
            let total_runs: usize = sdn_row_u32(row, 1) as usize;
            let passed: usize = sdn_row_u32(row, 2) as usize;
            let failed: usize = sdn_row_u32(row, 3) as usize;
            let flaky_count: u32 = sdn_row_u32(row, 4);
            let last_change_str = sdn_row_string(row, 5);
            let last_change = ChangeType::from_str(&last_change_str);

            // Find record by name_str_id matching test_id
            for record in db.records.values_mut() {
                if record.name_str_id == Some(test_id) {
                    record.execution_history.total_runs = total_runs;
                    record.execution_history.passed = passed;
                    record.execution_history.failed = failed;
                    record.execution_history.failure_rate_pct = if total_runs > 0 {
                        (failed as f64 / total_runs as f64) * 100.0
                    } else {
                        0.0
                    };
                    record.execution_history.flaky = flaky_count > 0;
                    record.flaky_count = flaky_count;
                    record.last_change = last_change;
                    break;
                }
            }
        }
    }

    // Load timing summaries
    if let Some(SdnValue::Table { rows, .. }) = dict.get("timing") {
        for row in rows {
            let test_id = sdn_row_u32(row, 0);
            let last_ms = sdn_row_f64(row, 1);
            let p50 = sdn_row_f64(row, 2);
            let p90 = sdn_row_f64(row, 3);
            let p95 = sdn_row_f64(row, 4);
            let baseline_median = sdn_row_f64(row, 5);
            db.timing_summaries.insert(
                test_id,
                TimingSummary {
                    test_id,
                    last_ms,
                    p50,
                    p90,
                    p95,
                    baseline_median,
                },
            );
        }
    }

    // Load timing runs
    if let Some(SdnValue::Table { rows, .. }) = dict.get("timing_runs") {
        for row in rows {
            let test_id = sdn_row_u32(row, 0);
            let timestamp = sdn_row_string(row, 1);
            let duration_ms = sdn_row_f64(row, 2);
            let outlier = sdn_row_bool(row, 3);
            let entry = TimingRunEntry {
                test_id,
                timestamp,
                duration_ms,
                outlier,
            };
            db.timing_runs.entry(test_id).or_insert_with(Vec::new).push(entry);
        }
    }

    // Load changes
    if let Some(SdnValue::Table { rows, .. }) = dict.get("changes") {
        for row in rows {
            let test_id = sdn_row_u32(row, 0);
            let change_type_str = sdn_row_string(row, 1);
            let run_id = sdn_row_string(row, 2);
            db.changes.push(ChangeEvent {
                test_id,
                change_type: ChangeType::from_str(&change_type_str),
                run_id,
            });
        }
    }

    // Populate timing data back into records
    for record in db.records.values_mut() {
        if let Some(name_id) = record.name_str_id {
            if let Some(summary) = db.timing_summaries.get(&name_id) {
                record.timing.last_run_time = summary.last_ms;
                record.timing.p50 = summary.p50;
                record.timing.p90 = summary.p90;
                record.timing.p95 = summary.p95;
                record.timing.baseline_median = summary.baseline_median;
            }
            if let Some(runs) = db.timing_runs.get(&name_id) {
                record.timing.history.runs = runs
                    .iter()
                    .map(|r| TimingRun {
                        timestamp: r.timestamp.clone(),
                        duration_ms: r.duration_ms,
                        outlier: r.outlier,
                    })
                    .collect();
            }
        }
    }

    Ok(())
}

// SDN row helpers
fn sdn_row_u32(row: &[SdnValue], idx: usize) -> u32 {
    match row.get(idx) {
        Some(SdnValue::Int(n)) => *n as u32,
        Some(SdnValue::String(s)) => s.parse().unwrap_or(0),
        _ => 0,
    }
}

fn sdn_row_f64(row: &[SdnValue], idx: usize) -> f64 {
    match row.get(idx) {
        Some(SdnValue::Float(f)) => *f,
        Some(SdnValue::Int(n)) => *n as f64,
        Some(SdnValue::String(s)) => s.parse().unwrap_or(0.0),
        _ => 0.0,
    }
}

fn sdn_row_string(row: &[SdnValue], idx: usize) -> String {
    match row.get(idx) {
        Some(SdnValue::String(s)) => s.clone(),
        Some(SdnValue::Int(n)) => n.to_string(),
        Some(SdnValue::Float(f)) => f.to_string(),
        _ => String::new(),
    }
}

fn sdn_row_bool(row: &[SdnValue], idx: usize) -> bool {
    match row.get(idx) {
        Some(SdnValue::Bool(b)) => *b,
        Some(SdnValue::String(s)) => s == "true",
        _ => false,
    }
}

/// Parse V2 SDN format (old format with JSON blobs).
fn parse_test_db_sdn_v2(doc: &simple_sdn::SdnDocument) -> Result<TestDb, String> {
    let root = doc.root();
    let tests_table = match root {
        SdnValue::Table { .. } => Some(root),
        SdnValue::Dict(dict) => dict.get("tests"),
        _ => None,
    };

    let mut db = TestDb::new();

    if let Some(SdnValue::Table {
        fields: Some(fields),
        rows,
        ..
    }) = tests_table
    {
        for row in rows {
            if row.len() < fields.len() {
                continue;
            }

            let get_field = |name: &str| -> String {
                fields
                    .iter()
                    .position(|f| f == name)
                    .and_then(|idx| row.get(idx))
                    .map(|v| match v {
                        SdnValue::String(s) => s.clone(),
                        SdnValue::Int(n) => n.to_string(),
                        SdnValue::Float(f) => f.to_string(),
                        SdnValue::Bool(b) => b.to_string(),
                        _ => String::new(),
                    })
                    .unwrap_or_default()
            };

            let test_id = get_field("test_id");
            if test_id.is_empty() {
                continue;
            }

            let status_str = get_field("status");
            let status = match status_str.as_str() {
                "passed" => TestStatus::Passed,
                "failed" => TestStatus::Failed,
                "skipped" => TestStatus::Skipped,
                "ignored" => TestStatus::Ignored,
                "qualifiedignore" | "qualified_ignore" => TestStatus::QualifiedIgnore,
                _ => TestStatus::Passed,
            };

            let failure: Option<TestFailure> = {
                let s = get_field("failure");
                if s.is_empty() {
                    None
                } else {
                    serde_json::from_str(&s).ok()
                }
            };

            let execution_history: ExecutionHistory = {
                let s = get_field("execution_history");
                if s.is_empty() {
                    ExecutionHistory::default()
                } else {
                    serde_json::from_str(&s).unwrap_or_default()
                }
            };

            let timing: TimingData = {
                let s = get_field("timing");
                if s.is_empty() {
                    TimingData::default()
                } else {
                    serde_json::from_str(&s).unwrap_or_default()
                }
            };

            let timing_config: Option<TimingConfig> = {
                let s = get_field("timing_config");
                if s.is_empty() {
                    None
                } else {
                    serde_json::from_str(&s).ok()
                }
            };

            let related_bugs: Vec<String> = get_field("related_bugs")
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            let related_features: Vec<String> = get_field("related_features")
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            let tags: Vec<String> = get_field("tags")
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();

            let qualified_by = {
                let s = get_field("qualified_by");
                if s.is_empty() {
                    None
                } else {
                    Some(s)
                }
            };
            let qualified_at = {
                let s = get_field("qualified_at");
                if s.is_empty() {
                    None
                } else {
                    Some(s)
                }
            };
            let qualified_reason = {
                let s = get_field("qualified_reason");
                if s.is_empty() {
                    None
                } else {
                    Some(s)
                }
            };

            let record = TestRecord {
                test_id: test_id.clone(),
                test_name: get_field("test_name"),
                test_file: get_field("test_file"),
                category: get_field("category"),
                status,
                last_run: get_field("last_run"),
                failure,
                execution_history,
                timing,
                timing_config,
                related_bugs,
                related_features,
                tags,
                description: get_field("description"),
                valid: get_field("valid") == "true",
                qualified_by,
                qualified_at,
                qualified_reason,
                suite_id: None,
                name_str_id: None,
                category_str_id: None,
                status_str_id: None,
                last_change: ChangeType::NoChange,
                flaky_count: 0,
            };

            db.records.insert(test_id, record);
        }
    }

    Ok(db)
}

// ============================================================================
// Save — V3 format
// ============================================================================

/// Save test database to SDN file (V3 format).
/// Only writes test_db.sdn if content has changed.
pub fn save_test_db(path: &Path, db: &TestDb) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }

    // Guard: refuse to save empty DB if existing file has records
    if db.records.is_empty() && path.exists() {
        if let Ok(meta) = fs::metadata(path) {
            if meta.len() > 500 {
                debug_log!(
                    DebugLevel::Basic,
                    "TestDB",
                    "Refusing to overwrite non-empty database ({} bytes) with empty database",
                    meta.len()
                );
                return Ok(());
            }
        }
    }

    let _lock = FileLock::acquire(path, 10).map_err(|e| format!("Failed to acquire lock: {:?}", e))?;

    // Build V3 content
    let content = build_v3_sdn(db);

    // Compare with existing to avoid unnecessary writes
    if path.exists() {
        if let Ok(existing) = fs::read_to_string(path) {
            if existing == content {
                debug_log!(
                    DebugLevel::Detailed,
                    "TestDB",
                    "No changes to test_db.sdn, skipping write"
                );
                // Still save volatile data
                save_volatile_data(path, db)?;
                return Ok(());
            }
        }
    }

    // No .sdn.prev backup — jj handles history/rollback

    // Atomic write
    let temp_path = path.with_extension("sdn.tmp");
    fs::write(&temp_path, &content).map_err(|e| e.to_string())?;
    fs::rename(&temp_path, path).map_err(|e| e.to_string())?;

    // Save volatile data
    save_volatile_data(path, db)?;

    Ok(())
}

/// Build V3 SDN content string.
fn build_v3_sdn(db: &TestDb) -> String {
    let mut out = String::new();

    // Strings table
    out.push_str("strings |id, value|\n");
    for (id, value) in db.interner.to_sdn_rows() {
        let value = value;
        if value.contains(',') || value.contains('"') || value.contains('\n') {
            out.push_str(&format!("    {}, \"{}\"\n", id, value.replace('"', "\\\"")));
        } else {
            out.push_str(&format!("    {}, {}\n", id, value));
        }
    }
    out.push('\n');

    // Files table
    out.push_str("files |file_id, path_str|\n");
    for f in &db.files {
        out.push_str(&format!("    {}, {}\n", f.file_id, f.path_str));
    }
    out.push('\n');

    // Suites table
    out.push_str("suites |suite_id, file_id, name_str|\n");
    for s in &db.suites {
        out.push_str(&format!("    {}, {}, {}\n", s.suite_id, s.file_id, s.name_str));
    }
    out.push('\n');

    // Tests table — stable fields only (counters/timing in volatile runs file)
    // Sorted by test_id for deterministic output
    out.push_str("tests |test_id, suite_id, name_str, category_str, status_str, tags_str, description_str, valid, qualified_by, qualified_at, qualified_reason|\n");
    let mut sorted_records: Vec<_> = db.records.values().collect();
    sorted_records.sort_by(|a, b| a.test_id.cmp(&b.test_id));

    for (idx, record) in sorted_records.iter().enumerate() {
        let suite_id = record.suite_id.unwrap_or(0);
        let name_str = record.name_str_id.unwrap_or(0);
        let category_str = record.category_str_id.unwrap_or(0);
        let status_str = record.status_str_id.unwrap_or(0);
        let tags_str = record.tags.join(",");
        let desc = &record.description;

        out.push_str(&format!(
            "    {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}\n",
            idx,
            suite_id,
            name_str,
            category_str,
            status_str,
            if tags_str.is_empty() {
                String::new()
            } else {
                format!("\"{}\"", tags_str)
            },
            if desc.is_empty() {
                String::new()
            } else {
                format!("\"{}\"", desc.replace('"', "\\\""))
            },
            record.valid,
            record.qualified_by.as_deref().unwrap_or(""),
            record.qualified_at.as_deref().unwrap_or(""),
            record
                .qualified_reason
                .as_deref()
                .map(|s| format!("\"{}\"", s.replace('"', "\\\"")))
                .unwrap_or_default(),
        ));
    }

    out
}

/// Save volatile data (timing, runs, changes) to test_db_runs.sdn.
fn save_volatile_data(db_path: &Path, db: &TestDb) -> Result<(), String> {
    let runs_path = runs_file_path(db_path);

    if let Some(parent) = runs_path.parent() {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }

    let mut out = String::new();

    // Counters (volatile — per-test run counts, changes every run)
    out.push_str("counters |test_id, total_runs, passed, failed, flaky_count, last_change|\n");
    let mut counter_ids: Vec<_> = db
        .records
        .values()
        .filter_map(|r| r.name_str_id.map(|id| (id, r)))
        .collect();
    counter_ids.sort_by_key(|(id, _)| *id);
    for (id, record) in &counter_ids {
        out.push_str(&format!(
            "    {}, {}, {}, {}, {}, {}\n",
            id,
            record.execution_history.total_runs,
            record.execution_history.passed,
            record.execution_history.failed,
            record.flaky_count,
            record.last_change,
        ));
    }
    out.push('\n');

    // Timing summaries
    out.push_str("timing |test_id, last_ms, p50, p90, p95, baseline_median|\n");
    let mut timing_ids: Vec<_> = db.timing_summaries.keys().collect();
    timing_ids.sort();
    for &id in &timing_ids {
        if let Some(t) = db.timing_summaries.get(id) {
            out.push_str(&format!(
                "    {}, {}, {}, {}, {}, {}\n",
                t.test_id, t.last_ms, t.p50, t.p90, t.p95, t.baseline_median
            ));
        }
    }
    out.push('\n');

    // Timing runs
    out.push_str("timing_runs |test_id, timestamp, duration_ms, outlier|\n");
    let mut run_ids: Vec<_> = db.timing_runs.keys().collect();
    run_ids.sort();
    for &id in &run_ids {
        if let Some(runs) = db.timing_runs.get(id) {
            for r in runs {
                out.push_str(&format!(
                    "    {}, \"{}\", {}, {}\n",
                    r.test_id, r.timestamp, r.duration_ms, r.outlier
                ));
            }
        }
    }
    out.push('\n');

    // Changes
    out.push_str("changes |test_id, change_type, run_id|\n");
    for c in &db.changes {
        out.push_str(&format!("    {}, {}, {}\n", c.test_id, c.change_type, c.run_id));
    }
    out.push('\n');

    // Test runs are managed separately via Database<TestRunRecord>
    // Don't overwrite them here — they're loaded/saved through the test run APIs

    let temp_path = runs_path.with_extension("sdn.tmp");
    fs::write(&temp_path, &out).map_err(|e| e.to_string())?;
    fs::rename(&temp_path, &runs_path).map_err(|e| e.to_string())?;

    Ok(())
}

// ============================================================================
// Update test result
// ============================================================================

/// Update test result in database
pub fn update_test_result(
    db: &mut TestDb,
    test_id: &str,
    test_name: &str,
    test_file: &str,
    category: &str,
    status: TestStatus,
    duration_ms: f64,
    failure: Option<TestFailure>,
    all_tests_run: bool,
) {
    let is_new = !db.records.contains_key(test_id);

    debug_log!(
        DebugLevel::Trace,
        "TestDB",
        "    Record: {} ({})",
        test_id,
        if is_new { "NEW" } else { "UPDATE" }
    );

    // Ensure tree structures exist
    let parts: Vec<&str> = test_id.splitn(3, "::").collect();
    let suite_name = if parts.len() >= 2 { parts[1] } else { "default" };
    let suite_id = db.get_or_create_suite(test_file, suite_name);
    let name_str_id = db.interner.intern(test_name);
    let category_str_id = db.interner.intern(category);
    let status_str_id = db.interner.intern(match status {
        TestStatus::Passed => "passed",
        TestStatus::Failed => "failed",
        TestStatus::Skipped => "skipped",
        TestStatus::Ignored => "ignored",
        TestStatus::QualifiedIgnore => "qualifiedignore",
    });

    let test = db.records.entry(test_id.to_string()).or_insert_with(|| TestRecord {
        test_id: test_id.to_string(),
        test_name: test_name.to_string(),
        test_file: test_file.to_string(),
        category: category.to_string(),
        status,
        last_run: chrono::Utc::now().to_rfc3339(),
        failure: None,
        execution_history: ExecutionHistory::default(),
        timing: TimingData::default(),
        timing_config: None,
        related_bugs: Vec::new(),
        related_features: Vec::new(),
        tags: Vec::new(),
        description: String::new(),
        valid: true,
        qualified_by: None,
        qualified_at: None,
        qualified_reason: None,
        suite_id: Some(suite_id),
        name_str_id: Some(name_str_id),
        category_str_id: Some(category_str_id),
        status_str_id: Some(status_str_id),
        last_change: ChangeType::NewTest,
        flaky_count: 0,
    });

    let old_status = test.status;

    // Detect status transition
    let change_type = if is_new {
        ChangeType::NewTest
    } else {
        match (old_status, status) {
            (TestStatus::Passed, TestStatus::Failed) => ChangeType::PassToFail,
            (TestStatus::Failed, TestStatus::Passed) => ChangeType::FailToPass,
            (TestStatus::Skipped, TestStatus::Passed) => ChangeType::SkipToPass,
            (TestStatus::Skipped, TestStatus::Failed) => ChangeType::SkipToFail,
            (TestStatus::Passed, TestStatus::Skipped) => ChangeType::PassToSkip,
            (TestStatus::Failed, TestStatus::Skipped) => ChangeType::FailToSkip,
            _ => ChangeType::NoChange,
        }
    };

    // Update V3 fields
    test.suite_id = Some(suite_id);
    test.name_str_id = Some(name_str_id);
    test.category_str_id = Some(category_str_id);
    test.status_str_id = Some(status_str_id);

    if change_type != ChangeType::NoChange {
        test.last_change = change_type;
        db.dirty = true;

        // Track flaky transitions
        if matches!(change_type, ChangeType::PassToFail | ChangeType::FailToPass) {
            test.flaky_count += 1;
        }
    }

    // Update execution status
    test.status = status;
    test.last_run = chrono::Utc::now().to_rfc3339();
    test.failure = failure;

    if old_status != status {
        debug_log!(
            DebugLevel::Trace,
            "TestDB",
            "      Status transition: {:?} -> {:?}",
            old_status,
            status
        );
        db.dirty = true;
    }

    // Update execution history
    test.execution_history.total_runs += 1;
    match status {
        TestStatus::Passed => test.execution_history.passed += 1,
        TestStatus::Failed => test.execution_history.failed += 1,
        _ => {}
    }

    let run_result = match status {
        TestStatus::Passed => "pass",
        TestStatus::Failed => "fail",
        TestStatus::Skipped => "skip",
        TestStatus::Ignored => "ignore",
        TestStatus::QualifiedIgnore => "qualified_ignore",
    };
    test.execution_history.last_10_runs.insert(0, run_result.to_string());
    if test.execution_history.last_10_runs.len() > 10 {
        test.execution_history.last_10_runs.truncate(10);
    }

    if test.execution_history.total_runs > 0 {
        test.execution_history.failure_rate_pct =
            (test.execution_history.failed as f64 / test.execution_history.total_runs as f64) * 100.0;
    }

    debug_log!(
        DebugLevel::Trace,
        "TestDB",
        "      Execution history: {} runs, {} passed, {} failed ({:.1}% failure rate)",
        test.execution_history.total_runs,
        test.execution_history.passed,
        test.execution_history.failed,
        test.execution_history.failure_rate_pct
    );

    let was_flaky = test.execution_history.flaky;
    test.execution_history.flaky = detect_flaky_test(&test.execution_history);

    if !was_flaky && test.execution_history.flaky {
        debug_log!(DebugLevel::Detailed, "TestDB", "      Flaky test detected: {}", test_id);
    }

    // Update timing
    let old_baseline = test.timing.baseline_median;
    update_test_timing(test, duration_ms, all_tests_run, &db.config);

    if test.timing.baseline_median != old_baseline && old_baseline > 0.0 {
        let change_pct = ((test.timing.baseline_median - old_baseline) / old_baseline) * 100.0;
        debug_log!(
            DebugLevel::Trace,
            "TestDB",
            "      Timing: {}ms (baseline: {}ms, {:+.1}%)",
            duration_ms,
            test.timing.baseline_median,
            change_pct
        );
    }

    test.valid = true;

    // Update volatile timing summary
    if let Some(name_id) = test.name_str_id {
        let summary = TimingSummary {
            test_id: name_id,
            last_ms: test.timing.last_run_time,
            p50: test.timing.p50,
            p90: test.timing.p90,
            p95: test.timing.p95,
            baseline_median: test.timing.baseline_median,
        };
        db.timing_summaries.insert(name_id, summary);

        // Update timing runs (cap at 10)
        let runs = db.timing_runs.entry(name_id).or_insert_with(Vec::new);
        runs.insert(
            0,
            TimingRunEntry {
                test_id: name_id,
                timestamp: chrono::Utc::now().to_rfc3339(),
                duration_ms,
                outlier: false,
            },
        );
        if runs.len() > 10 {
            runs.truncate(10);
        }

        // Record change event if status changed
        if change_type != ChangeType::NoChange {
            db.changes.push(ChangeEvent {
                test_id: name_id,
                change_type,
                run_id: String::new(), // Will be filled in by caller if needed
            });
        }
    }
}

/// Detect if test is flaky
fn detect_flaky_test(history: &ExecutionHistory) -> bool {
    if history.last_10_runs.len() < 5 {
        return false;
    }

    let has_pass = history.last_10_runs.iter().any(|s| s == "pass");
    let has_fail = history.last_10_runs.iter().any(|s| s == "fail");

    has_pass && has_fail && history.failure_rate_pct > 5.0 && history.failure_rate_pct < 95.0
}

/// Update timing data for a test
fn update_test_timing(test: &mut TestRecord, duration_ms: f64, all_tests_run: bool, config: &TestDbConfig) {
    let timing_config = test.timing_config.as_ref().unwrap_or(&config.default_timing_config);

    test.timing.history.runs.insert(
        0,
        TimingRun {
            timestamp: chrono::Utc::now().to_rfc3339(),
            duration_ms,
            outlier: false,
        },
    );

    let max_size = timing_config.max_sample_size;
    if test.timing.history.runs.len() > max_size {
        test.timing.history.runs.truncate(max_size);
    }

    test.timing.last_run_time = duration_ms;

    if test.timing.history.runs.len() < timing_config.min_sample_size {
        return;
    }

    let samples: Vec<f64> = test.timing.history.runs.iter().map(|r| r.duration_ms).collect();

    let outlier_method = match timing_config.outlier_method.as_str() {
        "IQR" => OutlierMethod::IQR,
        "ZScore" => OutlierMethod::ZScore,
        _ => OutlierMethod::MAD,
    };

    let outlier_result = detect_outliers(&samples, outlier_method);

    for (i, run) in test.timing.history.runs.iter_mut().enumerate() {
        run.outlier = outlier_result.outlier_indices.contains(&i);
    }

    let stats = if !outlier_result.inliers.is_empty() {
        compute_statistics(&outlier_result.inliers)
    } else {
        compute_statistics(&samples)
    };

    test.timing.p50 = stats.p50;
    test.timing.p90 = stats.p90;
    test.timing.p95 = stats.p95;
    test.timing.p99 = stats.p99;
    test.timing.min_time = stats.min;
    test.timing.max_time = stats.max;
    test.timing.iqr = stats.iqr;

    if !all_tests_run && config.update_rules.update_on_all_tests_run {
        return;
    }

    let value_to_use = if timing_config.use_median {
        stats.median
    } else {
        stats.mean
    };

    let avg_change = has_significant_change(
        value_to_use,
        test.timing.baseline_median,
        timing_config.update_threshold_pct,
    );
    let std_dev_change = has_significant_change(stats.std_dev, test.timing.baseline_std_dev, 10.0);

    if avg_change || std_dev_change {
        let avg_change_pct = if test.timing.baseline_median != 0.0 {
            ((value_to_use - test.timing.baseline_median).abs() / test.timing.baseline_median) * 100.0
        } else {
            0.0
        };

        let std_dev_change_pct = if test.timing.baseline_std_dev != 0.0 {
            ((stats.std_dev - test.timing.baseline_std_dev).abs() / test.timing.baseline_std_dev) * 100.0
        } else {
            0.0
        };

        test.timing.baseline_median = stats.median;
        test.timing.baseline_mean = stats.mean;
        test.timing.baseline_std_dev = stats.std_dev;
        test.timing.baseline_cv_pct = stats.cv_pct;
        test.timing.baseline_last_updated = chrono::Utc::now().to_rfc3339();
        test.timing.baseline_run_count = test.timing.history.runs.len();
        test.timing.baseline_update_reason = format!(
            "avg_change={:.1}%, std_dev_change={:.1}%",
            avg_change_pct, std_dev_change_pct
        );
    }
}

// ============================================================================
// Report generation
// ============================================================================

/// Generate test result documentation
pub fn generate_test_result_docs(db: &TestDb, output_dir: &Path) -> Result<(), String> {
    let mut md = String::new();

    md.push_str("# Test Results\n\n");
    md.push_str(&format!(
        "**Generated:** {}\n",
        chrono::Local::now().format("%Y-%m-%d %H:%M:%S")
    ));

    let mut passed = 0;
    let mut failed = 0;
    let mut skipped = 0;
    let mut ignored = 0;
    let mut qualified_ignored = 0;

    for test in db.valid_records() {
        match test.status {
            TestStatus::Passed => passed += 1,
            TestStatus::Failed => failed += 1,
            TestStatus::Skipped => skipped += 1,
            TestStatus::Ignored => ignored += 1,
            TestStatus::QualifiedIgnore => qualified_ignored += 1,
        }
    }

    let total = passed + failed + skipped + ignored + qualified_ignored;
    md.push_str(&format!("**Total Tests:** {}\n", total));

    let status_emoji = if failed > 0 {
        "⚠️"
    } else if total == 0 {
        "❔"
    } else {
        "✅"
    };
    md.push_str(&format!("**Status:** {} ", status_emoji));
    if failed > 0 {
        md.push_str(&format!("{} FAILED\n\n", failed));
    } else {
        md.push_str("ALL PASSED\n\n");
    }

    md.push_str("## Summary\n\n");
    md.push_str("| Status | Count | Percentage |\n");
    md.push_str("|--------|-------|-----------|\n");

    let pct = |count: usize| {
        if total == 0 {
            0.0
        } else {
            (count as f64 / total as f64) * 100.0
        }
    };

    md.push_str(&format!("| ✅ Passed | {} | {:.1}% |\n", passed, pct(passed)));
    md.push_str(&format!("| ❌ Failed | {} | {:.1}% |\n", failed, pct(failed)));
    md.push_str(&format!("| ⏭️ Skipped | {} | {:.1}% |\n", skipped, pct(skipped)));
    md.push_str(&format!("| 🔕 Ignored | {} | {:.1}% |\n", ignored, pct(ignored)));
    md.push_str(&format!(
        "| 🔐 Qualified Ignore | {} | {:.1}% |\n\n",
        qualified_ignored,
        pct(qualified_ignored)
    ));

    // Recent Status Changes section (V3 feature)
    if !db.changes.is_empty() {
        md.push_str("---\n\n");
        md.push_str("## 🔄 Recent Status Changes\n\n");
        md.push_str("| Test | Change | Run |\n");
        md.push_str("|------|--------|-----|\n");

        for change in db.changes.iter().take(20) {
            let test_name = if (change.test_id as usize) < db.interner.len() {
                db.interner.get_or_empty(change.test_id).to_string()
            } else {
                format!("test_{}", change.test_id)
            };
            md.push_str(&format!(
                "| {} | {} | {} |\n",
                test_name, change.change_type, change.run_id
            ));
        }
        md.push_str("\n");
    }

    // Failed tests
    if failed > 0 {
        md.push_str("---\n\n");
        md.push_str(&format!("## ❌ Failed Tests ({})\n\n", failed));

        let failed_tests: Vec<&TestRecord> = db
            .valid_records()
            .into_iter()
            .filter(|t| t.status == TestStatus::Failed)
            .collect();

        for test in failed_tests {
            md.push_str(&format!("### 🔴 {}\n\n", test.test_name));
            md.push_str(&format!("**File:** `{}`\n", test.test_file));
            md.push_str(&format!("**Category:** {}\n", test.category));
            md.push_str(&format!("**Failed:** {}\n", test.last_run));
            md.push_str(&format!(
                "**Flaky:** {} ({:.1}% failure rate)\n\n",
                if test.execution_history.flaky { "Yes" } else { "No" },
                test.execution_history.failure_rate_pct
            ));

            if let Some(ref failure) = test.failure {
                md.push_str("**Error:**\n```\n");
                md.push_str(&failure.error_message);
                md.push_str("\n");
                if let Some(ref location) = failure.location {
                    md.push_str(&format!("Location: {}\n", location));
                }
                md.push_str("```\n\n");
            }

            if !test.related_bugs.is_empty() {
                md.push_str(&format!("**Linked Bugs:** [{}]\n\n", test.related_bugs.join(", ")));
            }

            if test.timing.baseline_median > 0.0 {
                let change_pct = if test.timing.baseline_median != 0.0 {
                    ((test.timing.last_run_time - test.timing.baseline_median) / test.timing.baseline_median) * 100.0
                } else {
                    0.0
                };
                let indicator = if change_pct > 10.0 {
                    "🔴"
                } else if change_pct > 5.0 {
                    "🟡"
                } else {
                    ""
                };
                md.push_str(&format!(
                    "**Timing:** {:.1}ms (baseline: {:.1}ms, {:+.1}% {})\n\n",
                    test.timing.last_run_time, test.timing.baseline_median, change_pct, indicator
                ));
            }

            md.push_str("---\n\n");
        }
    }

    // Timing Analysis
    md.push_str("---\n\n");
    md.push_str("## 📊 Timing Analysis\n\n");

    let mut regressions: Vec<(&TestRecord, f64)> = db
        .valid_records()
        .iter()
        .filter_map(|t| {
            if t.timing.baseline_median > 0.0 {
                let change_pct =
                    ((t.timing.last_run_time - t.timing.baseline_median) / t.timing.baseline_median) * 100.0;
                if change_pct > db.config.default_timing_config.alert_threshold_pct {
                    Some((*t, change_pct))
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    regressions.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());

    if !regressions.is_empty() {
        md.push_str(&format!("### Performance Regressions ({})\n\n", regressions.len()));
        md.push_str("Tests that are significantly slower than baseline:\n\n");
        md.push_str("| Test | Current | Baseline | Change | Status |\n");
        md.push_str("|------|---------|----------|--------|--------|\n");

        for (test, change_pct) in regressions.iter().take(10) {
            md.push_str(&format!(
                "| {} | {:.1}ms | {:.1}ms | {:+.1}% | 🔴 ALERT |\n",
                test.test_name, test.timing.last_run_time, test.timing.baseline_median, change_pct
            ));
        }
        md.push_str("\n");
    }

    let mut high_variance: Vec<(&TestRecord, f64)> = db
        .valid_records()
        .iter()
        .filter_map(|t| {
            if t.timing.baseline_cv_pct > 50.0 {
                Some((*t, t.timing.baseline_cv_pct))
            } else {
                None
            }
        })
        .collect();

    high_variance.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());

    if !high_variance.is_empty() {
        md.push_str(&format!("### High Variance Tests (CV% > 50%)\n\n"));
        md.push_str("Tests with unstable timing:\n\n");
        md.push_str("| Test | Mean | Std Dev | CV% | Recommendation |\n");
        md.push_str("|------|------|---------|-----|----------------|\n");

        for (test, cv_pct) in high_variance.iter().take(10) {
            let recommendation = if *cv_pct > 80.0 {
                "Investigate flakiness"
            } else {
                "May need longer warmup"
            };
            md.push_str(&format!(
                "| {} | {:.1}ms | {:.1}ms | {:.1}% | {} |\n",
                test.test_name, test.timing.baseline_mean, test.timing.baseline_std_dev, cv_pct, recommendation
            ));
        }
        md.push_str("\n");
    }

    let mut fastest: Vec<(&TestRecord, f64)> = db
        .valid_records()
        .iter()
        .filter_map(|t| {
            if t.timing.baseline_median > 0.0 {
                Some((*t, t.timing.baseline_median))
            } else {
                None
            }
        })
        .collect();

    fastest.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());

    if !fastest.is_empty() {
        md.push_str("### Fastest Tests (Top 10)\n\n");
        md.push_str("| Test | Time |\n");
        md.push_str("|------|------|\n");
        for (test, time) in fastest.iter().take(10) {
            md.push_str(&format!("| {} | {:.1}ms |\n", test.test_name, time));
        }
        md.push_str("\n");
    }

    let mut slowest: Vec<(&TestRecord, f64)> = db
        .valid_records()
        .iter()
        .filter_map(|t| {
            if t.timing.baseline_median > 0.0 {
                Some((*t, t.timing.baseline_median))
            } else {
                None
            }
        })
        .collect();

    slowest.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());

    if !slowest.is_empty() {
        md.push_str("### Slowest Tests (Top 10)\n\n");
        md.push_str("| Test | Time |\n");
        md.push_str("|------|------|\n");
        for (test, time) in slowest.iter().take(10) {
            md.push_str(&format!("| {} | {:.1}ms |\n", test.test_name, time));
        }
        md.push_str("\n");
    }

    // Action Items
    md.push_str("---\n\n");
    md.push_str("## 🎯 Action Items\n\n");

    if failed > 0 {
        md.push_str(&format!("### Priority 1: Fix Failing Tests ({})\n\n", failed));

        let failed_tests: Vec<&TestRecord> = db
            .valid_records()
            .into_iter()
            .filter(|t| t.status == TestStatus::Failed)
            .collect();

        for (i, test) in failed_tests.iter().take(5).enumerate() {
            md.push_str(&format!("{}. **{}** - ", i + 1, test.test_name));
            if let Some(ref failure) = test.failure {
                let short_msg = failure.error_message.lines().next().unwrap_or("Unknown error");
                md.push_str(short_msg);
            }
            md.push_str("\n");
            if !test.related_bugs.is_empty() {
                md.push_str(&format!("   - Related bugs: {}\n", test.related_bugs.join(", ")));
            }
        }
        md.push_str("\n");
    }

    if !regressions.is_empty() {
        md.push_str(&format!(
            "### Priority 2: Investigate Performance Regressions ({})\n\n",
            regressions.len()
        ));
        md.push_str("Tests showing significant slowdown compared to baseline:\n");
        for (test, change_pct) in regressions.iter().take(5) {
            md.push_str(&format!("- {} ({:+.1}%)\n", test.test_name, change_pct));
        }
        md.push_str("\n");
    }

    let flaky_tests: Vec<&TestRecord> = db
        .valid_records()
        .into_iter()
        .filter(|t| t.execution_history.flaky)
        .collect();

    if !flaky_tests.is_empty() {
        md.push_str(&format!(
            "### Priority 3: Stabilize Flaky Tests ({})\n\n",
            flaky_tests.len()
        ));
        md.push_str("Tests with intermittent failures:\n");
        for test in flaky_tests.iter().take(5) {
            md.push_str(&format!(
                "- {} ({:.1}% failure rate)\n",
                test.test_name, test.execution_history.failure_rate_pct
            ));
        }
        md.push_str("\n");
    }

    // Qualified Ignored
    let qualified_ignored_tests: Vec<&TestRecord> = db
        .valid_records()
        .into_iter()
        .filter(|t| t.status == TestStatus::QualifiedIgnore)
        .collect();

    if !qualified_ignored_tests.is_empty() {
        md.push_str("---\n\n");
        md.push_str(&format!(
            "## 🔐 Qualified Ignored Tests ({})\n\n",
            qualified_ignored_tests.len()
        ));
        md.push_str("Tests ignored with authorized qualification:\n\n");
        md.push_str("| Test | Qualified By | Reason | Date |\n");
        md.push_str("|------|-------------|--------|------|\n");

        for test in qualified_ignored_tests.iter().take(20) {
            let qualified_by = test.qualified_by.as_deref().unwrap_or("-");
            let reason = test.qualified_reason.as_deref().unwrap_or("-");
            let date = test
                .qualified_at
                .as_deref()
                .and_then(|s| s.split('T').next())
                .unwrap_or("-");
            md.push_str(&format!(
                "| {} | {} | {} | {} |\n",
                test.test_name, qualified_by, reason, date
            ));
        }
        md.push_str("\n");
    }

    let output_path = output_dir.join("test_result.md");
    fs::create_dir_all(output_dir).map_err(|e| e.to_string())?;
    fs::write(&output_path, md).map_err(|e| e.to_string())?;

    Ok(())
}

/// Check if a test record needs qualification
pub fn needs_qualification(record: &TestRecord) -> bool {
    record.status == TestStatus::Ignored && record.qualified_by.is_none()
}

/// Count the number of unqualified ignored tests
pub fn count_unqualified_ignores(db: &TestDb) -> usize {
    db.records.values().filter(|r| needs_qualification(r)).count()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_db() {
        let db = TestDb::new();
        assert_eq!(db.version, "3.0");
        assert_eq!(db.records.len(), 0);
    }

    #[test]
    fn test_update_test_result() {
        let mut db = TestDb::new();

        update_test_result(
            &mut db,
            "test_001",
            "test_example",
            "test.spl",
            "unit",
            TestStatus::Passed,
            45.5,
            None,
            true,
        );

        assert_eq!(db.records.len(), 1);
        let test = db.records.get("test_001").unwrap();
        assert_eq!(test.status, TestStatus::Passed);
        assert_eq!(test.execution_history.passed, 1);
    }

    #[test]
    fn test_detect_flaky_test() {
        let mut history = ExecutionHistory::default();
        history.last_10_runs = vec!["pass", "fail", "pass", "fail", "pass"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        history.total_runs = 5;
        history.failed = 2;
        history.failure_rate_pct = 40.0;

        assert!(detect_flaky_test(&history));
    }

    #[test]
    fn test_not_flaky_consistent_pass() {
        let mut history = ExecutionHistory::default();
        history.last_10_runs = vec!["pass", "pass", "pass", "pass", "pass"]
            .iter()
            .map(|s| s.to_string())
            .collect();
        history.total_runs = 5;
        history.failed = 0;
        history.failure_rate_pct = 0.0;

        assert!(!detect_flaky_test(&history));
    }

    #[test]
    fn test_change_detection() {
        let mut db = TestDb::new();

        // First run: passed
        update_test_result(
            &mut db,
            "test_001",
            "test_example",
            "test.spl",
            "unit",
            TestStatus::Passed,
            10.0,
            None,
            true,
        );
        assert_eq!(db.records.get("test_001").unwrap().last_change, ChangeType::NewTest);

        // Second run: still passed
        update_test_result(
            &mut db,
            "test_001",
            "test_example",
            "test.spl",
            "unit",
            TestStatus::Passed,
            10.0,
            None,
            true,
        );
        assert_eq!(db.records.get("test_001").unwrap().last_change, ChangeType::NewTest); // no change overwrites

        // Third run: failed
        update_test_result(
            &mut db,
            "test_001",
            "test_example",
            "test.spl",
            "unit",
            TestStatus::Failed,
            10.0,
            None,
            true,
        );
        assert_eq!(db.records.get("test_001").unwrap().last_change, ChangeType::PassToFail);

        // Fourth run: back to passed
        update_test_result(
            &mut db,
            "test_001",
            "test_example",
            "test.spl",
            "unit",
            TestStatus::Passed,
            10.0,
            None,
            true,
        );
        assert_eq!(db.records.get("test_001").unwrap().last_change, ChangeType::FailToPass);
        assert_eq!(db.records.get("test_001").unwrap().flaky_count, 2);
    }

    #[test]
    fn test_tree_structure() {
        let mut db = TestDb::new();

        update_test_result(
            &mut db,
            "test/foo.spl::suite1::test_a",
            "test_a",
            "test/foo.spl",
            "unit",
            TestStatus::Passed,
            10.0,
            None,
            true,
        );
        update_test_result(
            &mut db,
            "test/foo.spl::suite1::test_b",
            "test_b",
            "test/foo.spl",
            "unit",
            TestStatus::Passed,
            10.0,
            None,
            true,
        );
        update_test_result(
            &mut db,
            "test/bar.spl::suite2::test_c",
            "test_c",
            "test/bar.spl",
            "unit",
            TestStatus::Passed,
            10.0,
            None,
            true,
        );

        assert_eq!(db.files.len(), 2);
        assert_eq!(db.suites.len(), 2);
        assert_eq!(db.records.len(), 3);
    }

    #[test]
    fn test_validate_stale_run() {
        use crate::unified_db::ViolationType;

        let mut run = TestRunRecord::new_running();
        run.start_time = chrono::Utc::now()
            .checked_sub_signed(chrono::Duration::hours(3))
            .unwrap()
            .to_rfc3339();

        let report = run.validate_record();
        assert!(report.has_violations());
        assert_eq!(report.violations[0].violation_type, ViolationType::StaleRunning);
        assert!(report.auto_fixable);
    }

    #[test]
    fn test_validate_timestamp_inconsistent() {
        use crate::unified_db::ViolationType;

        let mut run = TestRunRecord::new_running();
        run.status = TestRunStatus::Completed;
        run.start_time = "2024-01-30T10:00:00Z".to_string();
        run.end_time = "2024-01-30T09:00:00Z".to_string();

        let report = run.validate_record();
        assert!(report.has_violations());
        assert_eq!(
            report.violations[0].violation_type,
            ViolationType::TimestampInconsistent
        );
    }

    #[test]
    fn test_validate_count_overflow() {
        use crate::unified_db::ViolationType;

        let mut run = TestRunRecord::new_running();
        run.test_count = 10;
        run.passed = 8;
        run.failed = 3;

        let report = run.validate_record();
        assert!(report.has_violations());
        assert_eq!(report.violations[0].violation_type, ViolationType::CountInconsistent);
    }

    #[test]
    fn test_validate_valid_run() {
        let run = TestRunRecord::new_running();
        let report = run.validate_record();
        assert!(!report.has_violations());
    }

    #[test]
    fn test_validate_status_inconsistent_missing_end_time() {
        use crate::unified_db::ViolationType;

        let mut run = TestRunRecord::new_running();
        run.status = TestRunStatus::Completed;
        run.end_time = "".to_string();

        let report = run.validate_record();
        assert!(report.has_violations());
        let has_status_violation = report
            .violations
            .iter()
            .any(|v| v.violation_type == ViolationType::StatusInconsistent);
        assert!(has_status_violation);
    }

    #[test]
    fn test_validate_status_inconsistent_running_with_end_time() {
        use crate::unified_db::ViolationType;

        let mut run = TestRunRecord::new_running();
        run.status = TestRunStatus::Running;
        run.end_time = chrono::Utc::now().to_rfc3339();

        let report = run.validate_record();
        assert!(report.has_violations());
        let has_status_violation = report
            .violations
            .iter()
            .any(|v| v.violation_type == ViolationType::StatusInconsistent);
        assert!(has_status_violation);
    }

    #[test]
    fn test_validate_future_timestamp() {
        use crate::unified_db::ViolationType;

        let mut run = TestRunRecord::new_running();
        run.start_time = chrono::Utc::now()
            .checked_add_signed(chrono::Duration::hours(1))
            .unwrap()
            .to_rfc3339();

        let report = run.validate_record();
        assert!(report.has_violations());
        assert_eq!(report.violations[0].violation_type, ViolationType::FutureTimestamp);
        assert_eq!(report.violations[0].severity(), crate::unified_db::Severity::Critical);
    }

    #[test]
    fn test_validate_invalid_timestamp_format() {
        use crate::unified_db::ViolationType;

        let mut run = TestRunRecord::new_running();
        run.status = TestRunStatus::Completed;
        run.start_time = "not-a-timestamp".to_string();
        run.end_time = chrono::Utc::now().to_rfc3339();

        let report = run.validate_record();
        assert!(report.has_violations());
        let has_invalid_value = report
            .violations
            .iter()
            .any(|v| v.violation_type == ViolationType::InvalidValue);
        assert!(has_invalid_value);
    }

    #[test]
    fn test_validate_multiple_violations() {
        use crate::unified_db::ViolationType;

        let mut run = TestRunRecord::new_running();
        run.start_time = chrono::Utc::now()
            .checked_sub_signed(chrono::Duration::hours(5))
            .unwrap()
            .to_rfc3339();
        run.test_count = 10;
        run.passed = 8;
        run.failed = 5;

        let report = run.validate_record();
        assert!(report.has_violations());
        assert!(report.violations.len() >= 2);

        let has_stale = report
            .violations
            .iter()
            .any(|v| v.violation_type == ViolationType::StaleRunning);
        let has_count = report
            .violations
            .iter()
            .any(|v| v.violation_type == ViolationType::CountInconsistent);
        assert!(has_stale);
        assert!(has_count);
    }

    #[test]
    fn test_validate_severity_levels() {
        use crate::unified_db::{Severity, ViolationType};

        let warning = ViolationType::StaleRunning;
        let error = ViolationType::DeadProcess;
        let critical = ViolationType::FutureTimestamp;

        let mut report = crate::unified_db::IntegrityReport::new("test");
        report.add_violation(crate::unified_db::IntegrityViolation::new(
            warning, "field1", "message1",
        ));
        assert_eq!(report.max_severity(), Severity::Warning);

        report.add_violation(crate::unified_db::IntegrityViolation::new(error, "field2", "message2"));
        assert_eq!(report.max_severity(), Severity::Error);

        report.add_violation(crate::unified_db::IntegrityViolation::new(
            critical, "field3", "message3",
        ));
        assert_eq!(report.max_severity(), Severity::Critical);
    }

    #[test]
    fn test_validate_auto_fixable_marking() {
        let mut run = TestRunRecord::new_running();
        run.start_time = chrono::Utc::now()
            .checked_sub_signed(chrono::Duration::hours(3))
            .unwrap()
            .to_rfc3339();

        let report = run.validate_record();
        assert!(report.auto_fixable);

        let mut run2 = TestRunRecord::new_running();
        run2.status = TestRunStatus::Completed;
        run2.start_time = "2026-01-30T10:00:00Z".to_string();
        run2.end_time = "2026-01-30T09:00:00Z".to_string();

        let report2 = run2.validate_record();
        assert!(!report2.auto_fixable);
    }

    #[test]
    fn test_validate_partial_counts_accepted() {
        let mut run = TestRunRecord::new_running();
        run.test_count = 20;
        run.passed = 10;
        run.failed = 3;
        run.crashed = 2;
        run.timed_out = 1;

        let report = run.validate_record();
        let has_count_error = report
            .violations
            .iter()
            .any(|v| v.violation_type == crate::unified_db::ViolationType::CountInconsistent);
        assert!(!has_count_error);
    }

    #[test]
    fn test_validate_exact_count_match() {
        let mut run = TestRunRecord::new_running();
        run.test_count = 15;
        run.passed = 10;
        run.failed = 3;
        run.crashed = 2;
        run.timed_out = 0;

        let report = run.validate_record();
        let has_count_error = report
            .violations
            .iter()
            .any(|v| v.violation_type == crate::unified_db::ViolationType::CountInconsistent);
        assert!(!has_count_error);
    }

    #[test]
    fn test_validate_report_formatting() {
        use crate::unified_db::{IntegrityViolation, ViolationType};

        let mut report = crate::unified_db::IntegrityReport::new("test_run_123");
        report.add_violation(
            IntegrityViolation::new(
                ViolationType::StaleRunning,
                "status",
                "Run has been 'running' for >2 hours",
            )
            .with_expected("Completed or Crashed")
            .with_actual("Running"),
        );

        let report_text = report.to_report();
        assert!(report_text.contains("test_run_123"));
        assert!(report_text.contains("status"));
        assert!(report_text.contains("Expected:"));
        assert!(report_text.contains("Actual:"));
    }

    #[test]
    fn test_string_interner_integration() {
        let mut db = TestDb::new();
        let id1 = db.interner.intern("passed");
        let id2 = db.interner.intern("failed");
        let id3 = db.interner.intern("passed"); // duplicate
        assert_eq!(id1, id3);
        assert_ne!(id1, id2);
    }

    #[test]
    fn test_v3_roundtrip() {
        let mut db = TestDb::new();

        update_test_result(
            &mut db,
            "test/foo.spl::suite1::test_a",
            "test_a",
            "test/foo.spl",
            "unit",
            TestStatus::Passed,
            10.0,
            None,
            true,
        );

        let content = build_v3_sdn(&db);
        assert!(content.contains("strings |id, value|"));
        assert!(content.contains("files |file_id, path_str|"));
        assert!(content.contains("suites |suite_id, file_id, name_str|"));
        assert!(content.contains("tests |test_id, suite_id"));
    }
}

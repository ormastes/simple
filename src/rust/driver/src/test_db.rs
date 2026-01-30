//! Test execution database - tracks test results and timing.
//!
//! Stores:
//! - Test execution status (pass/fail/skipped)
//! - Failure information (error messages, stack traces)
//! - Timing statistics with variance tracking
//! - Execution history
//! - Flaky test detection
//!
//! Auto-generates: doc/test/test_result.md

use crate::db_lock::FileLock;
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

/// Test database
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestDb {
    pub version: String,
    pub last_updated: String,
    pub records: HashMap<String, TestRecord>,
    pub config: TestDbConfig,
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

    // Qualified ignore fields (requires authentication to modify)
    /// Who qualified this ignore (email or "password:<hash-prefix>")
    #[serde(skip_serializing_if = "Option::is_none")]
    pub qualified_by: Option<String>,
    /// When the qualification was made (ISO timestamp)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub qualified_at: Option<String>,
    /// User-provided reason for the qualified ignore
    #[serde(skip_serializing_if = "Option::is_none")]
    pub qualified_reason: Option<String>,
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

        // Parse qualified ignore fields
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
    /// Ignored with qualified authorization - requires authentication to set/modify
    QualifiedIgnore,
}

/// Test failure information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestFailure {
    pub error_message: String,
    pub assertion_failed: Option<String>,
    pub location: Option<String>, // file:line
    pub stack_trace: Option<String>,
}

/// Execution history tracking
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExecutionHistory {
    pub total_runs: usize,
    pub passed: usize,
    pub failed: usize,
    pub last_10_runs: Vec<String>, // ["pass", "pass", "fail", ...]
    pub flaky: bool,
    pub failure_rate_pct: f64,
}

/// Timing data
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimingData {
    // Current baseline
    pub baseline_median: f64,
    pub baseline_mean: f64,
    pub baseline_std_dev: f64,
    pub baseline_cv_pct: f64,

    // Latest run
    pub last_run_time: f64,

    // Historical window
    pub history: TimingHistory,

    // Percentiles
    pub p50: f64,
    pub p90: f64,
    pub p95: f64,
    pub p99: f64,

    // Variance tracking
    pub min_time: f64,
    pub max_time: f64,
    pub iqr: f64,

    // Update metadata
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
    pub outlier_method: String, // "IQR", "MAD", "ZScore"
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

/// A test run record - tracks a single test execution session
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestRunRecord {
    /// Unique run identifier (timestamp-based)
    pub run_id: String,
    /// When the run started (ISO 8601)
    pub start_time: String,
    /// When the run ended (empty if still running)
    pub end_time: String,
    /// Process ID of the test runner
    pub pid: u32,
    /// Hostname where the test ran
    pub hostname: String,
    /// Current status
    pub status: TestRunStatus,
    /// Total number of tests in this run
    pub test_count: usize,
    /// Number of passed tests
    pub passed: usize,
    /// Number of failed tests
    pub failed: usize,
    /// Number of tests that crashed
    pub crashed: usize,
    /// Number of tests that timed out
    pub timed_out: usize,
}

impl TestRunRecord {
    /// Create a new running test run record
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

    /// Mark the run as completed
    pub fn mark_completed(&mut self) {
        self.end_time = chrono::Utc::now().to_rfc3339();
        self.status = TestRunStatus::Completed;
    }

    /// Mark the run as crashed
    pub fn mark_crashed(&mut self) {
        self.end_time = chrono::Utc::now().to_rfc3339();
        self.status = TestRunStatus::Crashed;
    }

    /// Check if this run is stale (running but started too long ago)
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

    /// Check if the process is still alive
    pub fn is_process_alive(&self) -> bool {
        #[cfg(unix)]
        {
            // Check if process exists by sending signal 0
            unsafe { libc::kill(self.pid as i32, 0) == 0 }
        }
        #[cfg(not(unix))]
        {
            // On non-unix, assume process is alive if we can't check
            true
        }
    }
}

/// Implement Record trait for TestRunRecord
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
}

// ============================================================================
// Test Run Management Functions
// ============================================================================

use crate::unified_db::Database;

/// Load test runs from the test database file
pub fn load_test_runs(db_path: &Path) -> Result<Database<TestRunRecord>, String> {
    Database::<TestRunRecord>::load(db_path)
}

/// Save test runs to the test database file (preserves other tables)
pub fn save_test_runs(db: &Database<TestRunRecord>) -> Result<(), String> {
    db.save().map_err(|e| e.to_string())
}

/// Start a new test run and save it to the database
pub fn start_test_run(db_path: &Path) -> Result<TestRunRecord, String> {
    let mut db = load_test_runs(db_path)?;
    let run = TestRunRecord::new_running();
    db.insert(run.clone());
    save_test_runs(&db)?;
    Ok(run)
}

/// Update an existing test run
pub fn update_test_run(db_path: &Path, run: &TestRunRecord) -> Result<(), String> {
    let mut db = load_test_runs(db_path)?;
    db.insert(run.clone());
    save_test_runs(&db)
}

/// Complete a test run with final counts
pub fn complete_test_run(
    db_path: &Path,
    run_id: &str,
    test_count: usize,
    passed: usize,
    failed: usize,
    crashed: usize,
    timed_out: usize,
) -> Result<(), String> {
    let mut db = load_test_runs(db_path)?;
    if let Some(run) = db.get_mut(run_id) {
        run.mark_completed();
        run.test_count = test_count;
        run.passed = passed;
        run.failed = failed;
        run.crashed = crashed;
        run.timed_out = timed_out;
    }
    save_test_runs(&db)
}

/// Mark a test run as crashed
pub fn mark_run_crashed(db_path: &Path, run_id: &str) -> Result<(), String> {
    let mut db = load_test_runs(db_path)?;
    if let Some(run) = db.get_mut(run_id) {
        run.mark_crashed();
    }
    save_test_runs(&db)
}

/// Cleanup stale test runs (mark as crashed if running too long or process dead)
pub fn cleanup_stale_runs(db_path: &Path, max_hours: i64) -> Result<Vec<String>, String> {
    let mut db = load_test_runs(db_path)?;
    let mut cleaned = Vec::new();

    // Collect IDs to update (can't mutate while iterating)
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
        save_test_runs(&db)?;
    }

    Ok(cleaned)
}

/// Delete old completed runs (keep only N most recent)
pub fn prune_old_runs(db_path: &Path, keep_count: usize) -> Result<usize, String> {
    let mut db = load_test_runs(db_path)?;

    // Sort by start_time descending
    let mut runs: Vec<_> = db.records.values().cloned().collect();
    runs.sort_by(|a, b| b.start_time.cmp(&a.start_time));

    // Keep only the most recent N
    let to_delete: Vec<String> = runs.iter().skip(keep_count).map(|r| r.run_id.clone()).collect();

    let deleted_count = to_delete.len();
    for run_id in to_delete {
        db.delete(&run_id);
    }

    if deleted_count > 0 {
        save_test_runs(&db)?;
    }

    Ok(deleted_count)
}

/// List all test runs, optionally filtered by status
pub fn list_runs(db_path: &Path, status_filter: Option<TestRunStatus>) -> Result<Vec<TestRunRecord>, String> {
    let db = load_test_runs(db_path)?;
    let mut runs: Vec<_> = db
        .records
        .values()
        .filter(|r| status_filter.is_none() || Some(r.status) == status_filter)
        .cloned()
        .collect();

    // Sort by start_time descending (most recent first)
    runs.sort_by(|a, b| b.start_time.cmp(&a.start_time));
    Ok(runs)
}

/// Get currently running test runs
pub fn get_running_runs(db_path: &Path) -> Result<Vec<TestRunRecord>, String> {
    list_runs(db_path, Some(TestRunStatus::Running))
}

impl TestDb {
    pub fn new() -> Self {
        TestDb {
            version: "1.0".to_string(),
            last_updated: chrono::Utc::now().to_rfc3339(),
            records: HashMap::new(),
            config: TestDbConfig {
                default_timing_config: TimingConfig {
                    update_threshold_pct: 5.0,
                    alert_threshold_pct: 10.0,
                    std_dev_threshold: 4.0,
                    min_sample_size: 10,
                    max_sample_size: 40,
                    use_median: true,
                    outlier_method: "MAD".to_string(),
                },
                update_rules: UpdateRules {
                    update_on_all_tests_run: true,
                    track_top_variance_pct: 5.0,
                    rewrite_top_variance: false,
                },
            },
        }
    }

    pub fn valid_records(&self) -> Vec<&TestRecord> {
        self.records.values().filter(|r| r.valid).collect()
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
                window_size: 40,
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

/// Load test database from SDN file
pub fn load_test_db(path: &Path) -> Result<TestDb, String> {
    if !path.exists() {
        return Ok(TestDb::new());
    }

    let _lock = FileLock::acquire(path, 10).map_err(|e| format!("Failed to acquire lock: {:?}", e))?;
    let content = fs::read_to_string(path).map_err(|e| format!("Failed to read file: {}", e))?;

    if content.trim().is_empty() {
        return Ok(TestDb::new());
    }

    // Try SDN format first, fall back to JSON for backward compatibility
    match parse_document(&content) {
        Ok(doc) => {
            let db = parse_test_db_sdn(&doc)?;
            // Validate that we actually loaded some records if file has content
            if db.records.is_empty() && content.lines().count() > 2 {
                debug_log!(
                    DebugLevel::Basic,
                    "TestDB",
                    "Warning: Database file has content but no records were parsed"
                );
            }
            Ok(db)
        }
        Err(sdn_err) => {
            // Fallback to JSON format for existing databases
            serde_json::from_str(&content).map_err(|json_err| {
                format!(
                    "Failed to parse database - SDN error: {}, JSON error: {}",
                    sdn_err, json_err
                )
            })
        }
    }
}

/// Parse test database from SDN document
fn parse_test_db_sdn(doc: &simple_sdn::SdnDocument) -> Result<TestDb, String> {
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
                continue; // Skip malformed rows
            }

            // Helper to get field value
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

            // Parse JSON-encoded complex fields
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

            // Parse qualified ignore fields
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
            };

            db.records.insert(test_id, record);
        }
    }

    Ok(db)
}

/// Save test database to SDN file (with file locking)
/// Uses simple_sdn library for proper serialization (matches Simple's sdn.serializer)
pub fn save_test_db(path: &Path, db: &TestDb) -> Result<(), String> {
    use simple_sdn::SdnValue;

    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }

    let _lock = FileLock::acquire(path, 10).map_err(|e| format!("Failed to acquire lock: {:?}", e))?;

    // Create backup before overwriting if file exists and has content
    if path.exists() {
        if let Ok(existing_content) = fs::read_to_string(path) {
            if !existing_content.trim().is_empty() {
                let backup_path = path.with_extension("sdn.prev");
                if let Err(e) = fs::write(&backup_path, &existing_content) {
                    debug_log!(DebugLevel::Basic, "TestDB", "Warning: Failed to create backup: {}", e);
                }
            }
        }
    }

    // Build table fields
    let fields = vec![
        "test_id".to_string(),
        "test_name".to_string(),
        "test_file".to_string(),
        "category".to_string(),
        "status".to_string(),
        "last_run".to_string(),
        "failure".to_string(),
        "execution_history".to_string(),
        "timing".to_string(),
        "timing_config".to_string(),
        "related_bugs".to_string(),
        "related_features".to_string(),
        "tags".to_string(),
        "description".to_string(),
        "valid".to_string(),
        "qualified_by".to_string(),
        "qualified_at".to_string(),
        "qualified_reason".to_string(),
    ];

    // Build table rows using Record trait (no duplication, proper serialization)
    let mut sorted_records: Vec<_> = db.records.values().collect();
    sorted_records.sort_by(|a, b| a.test_id.cmp(&b.test_id));

    let rows: Vec<Vec<SdnValue>> = sorted_records
        .iter()
        .map(|record| {
            // Use Record::to_sdn_row() for consistent serialization
            record.to_sdn_row().into_iter().map(SdnValue::String).collect()
        })
        .collect();

    // Create SDN table and serialize using library (proper quoting built-in)
    let table = SdnValue::Table {
        fields: Some(fields),
        types: None,
        rows,
    };

    // Build document with table as root under "tests" key
    let mut dict = indexmap::IndexMap::new();
    dict.insert("tests".to_string(), table);

    let mut doc = simple_sdn::SdnDocument::parse("tests |id|").map_err(|e| e.to_string())?;
    *doc.root_mut() = SdnValue::Dict(dict);

    let content = doc.to_sdn();

    // Atomic write: temp file then rename
    let temp_path = path.with_extension("sdn.tmp");
    fs::write(&temp_path, &content).map_err(|e| e.to_string())?;
    fs::rename(&temp_path, path).map_err(|e| e.to_string())?;

    Ok(())
}

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
    });

    let old_status = test.status;

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

    // Calculate failure rate
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

    // Detect flaky tests (intermittent failures)
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
}

/// Detect if test is flaky (intermittent failures)
fn detect_flaky_test(history: &ExecutionHistory) -> bool {
    if history.last_10_runs.len() < 5 {
        return false; // Not enough data
    }

    let has_pass = history.last_10_runs.iter().any(|s| s == "pass");
    let has_fail = history.last_10_runs.iter().any(|s| s == "fail");

    // Flaky if both passes and failures in recent history
    // and failure rate is between 5% and 95% (not consistently failing/passing)
    has_pass && has_fail && history.failure_rate_pct > 5.0 && history.failure_rate_pct < 95.0
}

/// Update timing data for a test
fn update_test_timing(test: &mut TestRecord, duration_ms: f64, all_tests_run: bool, config: &TestDbConfig) {
    // Get timing config (use test-specific or default)
    let timing_config = test.timing_config.as_ref().unwrap_or(&config.default_timing_config);

    // Add new run to history
    test.timing.history.runs.insert(
        0,
        TimingRun {
            timestamp: chrono::Utc::now().to_rfc3339(),
            duration_ms,
            outlier: false, // Will be determined later
        },
    );

    // Keep only last N runs
    let max_size = timing_config.max_sample_size;
    if test.timing.history.runs.len() > max_size {
        test.timing.history.runs.truncate(max_size);
    }

    test.timing.last_run_time = duration_ms;

    // Need enough samples for statistics
    if test.timing.history.runs.len() < timing_config.min_sample_size {
        return;
    }

    // Extract duration values
    let samples: Vec<f64> = test.timing.history.runs.iter().map(|r| r.duration_ms).collect();

    // Detect outliers
    let outlier_method = match timing_config.outlier_method.as_str() {
        "IQR" => OutlierMethod::IQR,
        "ZScore" => OutlierMethod::ZScore,
        _ => OutlierMethod::MAD, // Default to MAD
    };

    let outlier_result = detect_outliers(&samples, outlier_method);

    // Mark outliers in history
    for (i, run) in test.timing.history.runs.iter_mut().enumerate() {
        run.outlier = outlier_result.outlier_indices.contains(&i);
    }

    // Compute statistics on inliers
    let stats = if !outlier_result.inliers.is_empty() {
        compute_statistics(&outlier_result.inliers)
    } else {
        compute_statistics(&samples) // Fall back to all samples
    };

    // Update percentiles
    test.timing.p50 = stats.p50;
    test.timing.p90 = stats.p90;
    test.timing.p95 = stats.p95;
    test.timing.p99 = stats.p99;
    test.timing.min_time = stats.min;
    test.timing.max_time = stats.max;
    test.timing.iqr = stats.iqr;

    // Check if baseline should update
    if !all_tests_run && config.update_rules.update_on_all_tests_run {
        // Skip baseline update if not all tests run
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

    let std_dev_change = has_significant_change(
        stats.std_dev,
        test.timing.baseline_std_dev,
        10.0, // 10% threshold for std_dev changes
    );

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

/// Generate test result documentation
pub fn generate_test_result_docs(db: &TestDb, output_dir: &Path) -> Result<(), String> {
    let mut md = String::new();

    // Header
    md.push_str("# Test Results\n\n");
    md.push_str(&format!(
        "**Generated:** {}\n",
        chrono::Local::now().format("%Y-%m-%d %H:%M:%S")
    ));

    // Count tests by status
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

    // Summary table
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

    // Failed tests section
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
                md.push_str("**Error:**\n");
                md.push_str("```\n");
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

            // Timing info
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

    // Timing Analysis section
    md.push_str("---\n\n");
    md.push_str("## 📊 Timing Analysis\n\n");

    // Performance regressions
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

    // High variance tests
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

    // Fastest tests
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

    // Slowest tests
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

    // Action Items section
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

    // Flaky tests
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

    // Qualified Ignored tests section
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

    // Write to file
    let output_path = output_dir.join("test_result.md");
    fs::create_dir_all(output_dir).map_err(|e| e.to_string())?;
    fs::write(&output_path, md).map_err(|e| e.to_string())?;

    Ok(())
}

/// Check if a test record needs qualification (ignored but not yet qualified)
pub fn needs_qualification(record: &TestRecord) -> bool {
    record.status == TestStatus::Ignored && record.qualified_by.is_none()
}

/// Count the number of unqualified ignored tests in the database
pub fn count_unqualified_ignores(db: &TestDb) -> usize {
    db.records.values().filter(|r| needs_qualification(r)).count()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_db() {
        let db = TestDb::new();
        assert_eq!(db.version, "1.0");
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
}

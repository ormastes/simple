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
}

/// Test execution status
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum TestStatus {
    Passed,
    Failed,
    Skipped,
    Ignored,
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
    let content = fs::read_to_string(path).map_err(|e| e.to_string())?;

    // Try SDN format first, fall back to JSON for backward compatibility
    if let Ok(doc) = parse_document(&content) {
        parse_test_db_sdn(&doc)
    } else {
        // Fallback to JSON format for existing databases
        serde_json::from_str(&content).map_err(|e| e.to_string())
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

    if let Some(SdnValue::Table { fields: Some(fields), rows, .. }) = tests_table {
        for row in rows {
            if row.len() < fields.len() {
                continue; // Skip malformed rows
            }

            // Helper to get field value
            let get_field = |name: &str| -> String {
                fields.iter().position(|f| f == name)
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
            if test_id.is_empty() { continue; }

            let status_str = get_field("status");
            let status = match status_str.as_str() {
                "passed" => TestStatus::Passed,
                "failed" => TestStatus::Failed,
                "skipped" => TestStatus::Skipped,
                "ignored" => TestStatus::Ignored,
                _ => TestStatus::Passed,
            };

            // Parse JSON-encoded complex fields
            let failure: Option<TestFailure> = {
                let s = get_field("failure");
                if s.is_empty() { None } else { serde_json::from_str(&s).ok() }
            };

            let execution_history: ExecutionHistory = {
                let s = get_field("execution_history");
                if s.is_empty() { ExecutionHistory::default() } else { serde_json::from_str(&s).unwrap_or_default() }
            };

            let timing: TimingData = {
                let s = get_field("timing");
                if s.is_empty() { TimingData::default() } else { serde_json::from_str(&s).unwrap_or_default() }
            };

            let timing_config: Option<TimingConfig> = {
                let s = get_field("timing_config");
                if s.is_empty() { None } else { serde_json::from_str(&s).ok() }
            };

            let related_bugs: Vec<String> = get_field("related_bugs")
                .split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect();
            let related_features: Vec<String> = get_field("related_features")
                .split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect();
            let tags: Vec<String> = get_field("tags")
                .split(',').map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect();

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
            };

            db.records.insert(test_id, record);
        }
    }

    Ok(db)
}

/// Save test database to SDN file (with file locking)
pub fn save_test_db(path: &Path, db: &TestDb) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }

    let _lock = FileLock::acquire(path, 10).map_err(|e| format!("Failed to acquire lock: {:?}", e))?;

    let mut content = String::new();
    content.push_str("tests |test_id, test_name, test_file, category, status, last_run, failure, execution_history, timing, timing_config, related_bugs, related_features, tags, description, valid|\n");

    let mut sorted_records: Vec<_> = db.records.values().collect();
    sorted_records.sort_by(|a, b| a.test_id.cmp(&b.test_id));

    for record in sorted_records {
        let status_str = match record.status {
            TestStatus::Passed => "passed",
            TestStatus::Failed => "failed",
            TestStatus::Skipped => "skipped",
            TestStatus::Ignored => "ignored",
        };

        let failure_json = record.failure.as_ref()
            .map(|f| serde_json::to_string(f).unwrap_or_default())
            .unwrap_or_default();
        let history_json = serde_json::to_string(&record.execution_history).unwrap_or_default();
        let timing_json = serde_json::to_string(&record.timing).unwrap_or_default();
        let timing_config_json = record.timing_config.as_ref()
            .map(|c| serde_json::to_string(c).unwrap_or_default())
            .unwrap_or_default();

        let quote = |s: &str| {
            if s.is_empty() || s.contains(',') || s.contains('"') || s.contains('\n') {
                format!("\"{}\"", s.replace("\"", "\\\"").replace("\n", "\\n"))
            } else {
                s.to_string()
            }
        };

        let row = vec![
            quote(&record.test_id),
            quote(&record.test_name),
            quote(&record.test_file),
            quote(&record.category),
            quote(status_str),
            quote(&record.last_run),
            quote(&failure_json),
            quote(&history_json),
            quote(&timing_json),
            quote(&timing_config_json),
            quote(&record.related_bugs.join(",")),
            quote(&record.related_features.join(",")),
            quote(&record.tags.join(",")),
            quote(&record.description),
            record.valid.to_string(),
        ];

        content.push_str("    ");
        content.push_str(&row.join(", "));
        content.push('\n');
    }

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

    debug_log!(DebugLevel::Trace, "TestDB", "    Record: {} ({})",
        test_id, if is_new { "NEW" } else { "UPDATE" });

    let test = db.records.entry(test_id.to_string()).or_insert_with(|| {
        TestRecord {
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
        }
    });

    let old_status = test.status;

    // Update execution status
    test.status = status;
    test.last_run = chrono::Utc::now().to_rfc3339();
    test.failure = failure;

    if old_status != status {
        debug_log!(DebugLevel::Trace, "TestDB", "      Status transition: {:?} -> {:?}",
            old_status, status);
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

    debug_log!(DebugLevel::Trace, "TestDB", "      Execution history: {} runs, {} passed, {} failed ({:.1}% failure rate)",
        test.execution_history.total_runs,
        test.execution_history.passed,
        test.execution_history.failed,
        test.execution_history.failure_rate_pct);

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
        debug_log!(DebugLevel::Trace, "TestDB", "      Timing: {}ms (baseline: {}ms, {:+.1}%)",
            duration_ms, test.timing.baseline_median, change_pct);
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
fn update_test_timing(
    test: &mut TestRecord,
    duration_ms: f64,
    all_tests_run: bool,
    config: &TestDbConfig,
) {
    // Get timing config (use test-specific or default)
    let timing_config = test.timing_config.as_ref().unwrap_or(&config.default_timing_config);

    // Add new run to history
    test.timing.history.runs.insert(0, TimingRun {
        timestamp: chrono::Utc::now().to_rfc3339(),
        duration_ms,
        outlier: false, // Will be determined later
    });

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
    md.push_str(&format!("**Generated:** {}\n", chrono::Local::now().format("%Y-%m-%d %H:%M:%S")));

    // Count tests by status
    let mut passed = 0;
    let mut failed = 0;
    let mut skipped = 0;
    let mut ignored = 0;

    for test in db.valid_records() {
        match test.status {
            TestStatus::Passed => passed += 1,
            TestStatus::Failed => failed += 1,
            TestStatus::Skipped => skipped += 1,
            TestStatus::Ignored => ignored += 1,
        }
    }

    let total = passed + failed + skipped + ignored;
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
    md.push_str(&format!("| 🔕 Ignored | {} | {:.1}% |\n\n", ignored, pct(ignored)));

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
            md.push_str(&format!("**Flaky:** {} ({:.1}% failure rate)\n\n",
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
                    test.timing.last_run_time,
                    test.timing.baseline_median,
                    change_pct,
                    indicator
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
                let change_pct = ((t.timing.last_run_time - t.timing.baseline_median) / t.timing.baseline_median) * 100.0;
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
                test.test_name,
                test.timing.last_run_time,
                test.timing.baseline_median,
                change_pct
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
                test.test_name,
                test.timing.baseline_mean,
                test.timing.baseline_std_dev,
                cv_pct,
                recommendation
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
        md.push_str(&format!("### Priority 2: Investigate Performance Regressions ({})\n\n", regressions.len()));
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
        md.push_str(&format!("### Priority 3: Stabilize Flaky Tests ({})\n\n", flaky_tests.len()));
        md.push_str("Tests with intermittent failures:\n");
        for test in flaky_tests.iter().take(5) {
            md.push_str(&format!(
                "- {} ({:.1}% failure rate)\n",
                test.test_name,
                test.execution_history.failure_rate_pct
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

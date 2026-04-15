//! Test result update logic — update_test_result, flaky detection, timing updates.

use super::types::*;
use super::types::debug_log;
use crate::test_stats::{compute_statistics, detect_outliers, has_significant_change, OutlierMethod};

// ============================================================================
// Update test result
// ============================================================================

/// Update test result in database
#[allow(clippy::too_many_arguments)]
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
        let runs = db.timing_runs.entry(name_id).or_default();
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
pub(crate) fn detect_flaky_test(history: &ExecutionHistory) -> bool {
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

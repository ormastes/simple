//! Tests for the test database module.

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

    assert!(update::detect_flaky_test(&history));
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

    assert!(!update::detect_flaky_test(&history));
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

    let content = saver::build_v3_sdn(&db);
    assert!(content.contains("strings |id, value|"));
    assert!(content.contains("files |file_id, path_str|"));
    assert!(content.contains("suites |suite_id, file_id, name_str|"));
    assert!(content.contains("tests |test_id, suite_id"));
}

//! Test database update utilities.
//!
//! Handles updating the test database from test results.

use std::path::{Path, PathBuf};

use crate::test_db::{self, TestStatus, TestFailure};
use super::types::TestFileResult;

/// Update test database from test results
pub fn update_test_database(
    test_files: &[PathBuf],
    results: &[TestFileResult],
    all_tests_run: bool,
) -> Result<(), String> {
    let db_path = Path::new("doc/test/test_db.sdn");

    // Load or create test database
    let mut test_db = test_db::load_test_db(db_path).unwrap_or_else(|_| test_db::TestDb::new());

    // Update each test result
    for (test_path, result) in test_files.iter().zip(results.iter()) {
        let test_id = test_path
            .to_str()
            .unwrap_or("unknown")
            .to_string();

        let test_name = test_path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown")
            .to_string();

        let test_file = test_path
            .to_str()
            .unwrap_or("unknown")
            .to_string();

        let category = categorize_test(test_path);
        let (status, failure) = convert_result_to_db(result);
        let duration_ms = result.duration_ms as f64;

        test_db::update_test_result(
            &mut test_db,
            &test_id,
            &test_name,
            &test_file,
            &category,
            status,
            duration_ms,
            failure,
            all_tests_run,
        );
    }

    // Save updated database
    test_db::save_test_db(db_path, &test_db)?;

    // Generate test result documentation
    let doc_dir = Path::new("doc/test");
    test_db::generate_test_result_docs(&test_db, doc_dir)?;

    Ok(())
}

/// Categorize test based on path
fn categorize_test(path: &Path) -> String {
    let path_str = path.to_string_lossy().to_lowercase();
    if path_str.contains("unit") {
        "Unit".to_string()
    } else if path_str.contains("integration") {
        "Integration".to_string()
    } else if path_str.contains("system") {
        "System".to_string()
    } else {
        "Unknown".to_string()
    }
}

/// Convert TestFileResult to test_db types
fn convert_result_to_db(result: &TestFileResult) -> (TestStatus, Option<TestFailure>) {
    if result.error.is_some() {
        let failure = TestFailure {
            error_message: result.error.clone().unwrap_or_default(),
            assertion_failed: None,
            location: Some(result.path.to_string_lossy().to_string()),
            stack_trace: None,
        };
        (TestStatus::Failed, Some(failure))
    } else if result.failed > 0 {
        let failure = TestFailure {
            error_message: format!("{} tests failed", result.failed),
            assertion_failed: None,
            location: Some(result.path.to_string_lossy().to_string()),
            stack_trace: None,
        };
        (TestStatus::Failed, Some(failure))
    } else if result.passed > 0 {
        (TestStatus::Passed, None)
    } else {
        (TestStatus::Skipped, None)
    }
}

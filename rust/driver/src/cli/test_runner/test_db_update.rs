//! Test database update utilities.
//!
//! Handles updating the test database from test results.

use std::path::{Path, PathBuf};

use crate::test_db::{self, TestStatus, TestFailure};
use super::types::{TestFileResult, DebugLevel, debug_log};

/// Update test database from test results
pub fn update_test_database(
    test_files: &[PathBuf],
    results: &[TestFileResult],
    all_tests_run: bool,
) -> Result<(), String> {
    let db_path = Path::new("doc/test/test_db.sdn");

    debug_log!(
        DebugLevel::Basic,
        "TestDB",
        "Updating test database: {}",
        db_path.display()
    );
    debug_log!(
        DebugLevel::Detailed,
        "TestDB",
        "  Updating {} test records",
        test_files.len()
    );

    // Load existing database - NEVER silently create empty on error
    let mut test_db = match test_db::load_test_db(db_path) {
        Ok(db) => {
            debug_log!(
                DebugLevel::Detailed,
                "TestDB",
                "  Loaded existing database with {} records",
                db.records.len()
            );
            db
        }
        Err(e) => {
            // Only create new DB if file doesn't exist
            if !db_path.exists() {
                debug_log!(
                    DebugLevel::Basic,
                    "TestDB",
                    "  Creating new test database (file not found)"
                );
                test_db::TestDb::new()
            } else {
                // File exists but failed to parse - this is an error, don't lose data!
                eprintln!("[WARNING] Failed to load test database: {}", e);
                eprintln!("[WARNING] Existing records will be preserved. Fix the database format manually.");
                // Try to backup the corrupted file
                let backup_path = db_path.with_extension("sdn.backup");
                if let Err(backup_err) = std::fs::copy(db_path, &backup_path) {
                    eprintln!("[WARNING] Failed to create backup: {}", backup_err);
                } else {
                    eprintln!("[INFO] Backup created at: {}", backup_path.display());
                }
                return Err(format!("Database load failed: {}. Not overwriting existing data.", e));
            }
        }
    };

    // Update each test result - per individual test case when available
    for (test_path, result) in test_files.iter().zip(results.iter()) {
        let test_file = test_path.to_str().unwrap_or("unknown").to_string();
        let category = categorize_test(test_path);
        let duration_per_test = if !result.individual_results.is_empty() {
            result.duration_ms as f64 / result.individual_results.len() as f64
        } else {
            result.duration_ms as f64
        };

        if !result.individual_results.is_empty() {
            // Emit one row per individual test case
            for ind in &result.individual_results {
                let test_id = format!("{}::{}::{}", test_file, ind.group, ind.name);
                let test_name = ind.name.clone();

                let (status, failure) = if ind.skipped {
                    (TestStatus::Skipped, None)
                } else if ind.passed {
                    (TestStatus::Passed, None)
                } else {
                    let failure = TestFailure {
                        error_message: format!("Test '{}' failed", ind.name),
                        assertion_failed: None,
                        location: Some(test_file.clone()),
                        stack_trace: None,
                    };
                    (TestStatus::Failed, Some(failure))
                };

                debug_log!(DebugLevel::Trace, "TestDB", "  Test: {}", test_id);
                debug_log!(DebugLevel::Trace, "TestDB", "    Status: {:?}", status);

                test_db::update_test_result(
                    &mut test_db,
                    &test_id,
                    &test_name,
                    &test_file,
                    &category,
                    status,
                    duration_per_test,
                    failure,
                    all_tests_run,
                );
            }
        } else {
            // Fall back to per-file row (compile errors, etc.)
            let test_id = test_file.clone();
            let test_name = test_path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("unknown")
                .to_string();

            let (status, failure) = convert_result_to_db(result);
            let duration_ms = result.duration_ms as f64;

            debug_log!(DebugLevel::Trace, "TestDB", "  Test: {}", test_id);
            debug_log!(DebugLevel::Trace, "TestDB", "    Status: {:?}", status);
            debug_log!(DebugLevel::Trace, "TestDB", "    Duration: {}ms", duration_ms);
            debug_log!(DebugLevel::Trace, "TestDB", "    Category: {}", category);

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
    }

    debug_log!(
        DebugLevel::Detailed,
        "TestDB",
        "  Total records in database: {}",
        test_db.records.len()
    );

    // Save updated database
    test_db::save_test_db(db_path, &test_db)?;
    debug_log!(
        DebugLevel::Basic,
        "TestDB",
        "Saved test database to: {}",
        db_path.display()
    );

    // Generate test result documentation
    let doc_dir = Path::new("doc/test");
    test_db::generate_test_result_docs(&test_db, doc_dir)?;
    debug_log!(
        DebugLevel::Basic,
        "TestDB",
        "Generated test result documentation in: {}",
        doc_dir.display()
    );

    Ok(())
}

/// Update test database with Rust test results
pub fn update_rust_test_database(results: &[TestFileResult]) -> Result<(), String> {
    let db_path = Path::new("doc/test/test_db.sdn");

    debug_log!(
        DebugLevel::Basic,
        "RustTestDB",
        "Updating Rust test database: {}",
        db_path.display()
    );

    // Load existing database - NEVER silently create empty on error
    let mut test_db = match test_db::load_test_db(db_path) {
        Ok(db) => {
            debug_log!(
                DebugLevel::Detailed,
                "RustTestDB",
                "  Loaded existing database with {} records",
                db.records.len()
            );
            db
        }
        Err(e) => {
            if !db_path.exists() {
                debug_log!(
                    DebugLevel::Basic,
                    "RustTestDB",
                    "  Creating new test database (file not found)"
                );
                test_db::TestDb::new()
            } else {
                eprintln!("[WARNING] Failed to load test database: {}", e);
                eprintln!("[WARNING] Existing records will be preserved.");
                let backup_path = db_path.with_extension("sdn.backup");
                if let Err(backup_err) = std::fs::copy(db_path, &backup_path) {
                    eprintln!("[WARNING] Failed to create backup: {}", backup_err);
                } else {
                    eprintln!("[INFO] Backup created at: {}", backup_path.display());
                }
                return Err(format!("Database load failed: {}. Not overwriting existing data.", e));
            }
        }
    };

    // Update each Rust test result
    for result in results {
        let test_id = format!("rust::{}", result.path.to_str().unwrap_or("unknown"));

        let test_name = result
            .path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("rust_test")
            .to_string();

        let test_file = result.path.to_str().unwrap_or("unknown").to_string();

        let category = categorize_test(&result.path);
        let (status, failure) = convert_result_to_db(result);
        let duration_ms = result.duration_ms as f64;

        debug_log!(DebugLevel::Trace, "RustTestDB", "  Test: {}", test_id);
        debug_log!(DebugLevel::Trace, "RustTestDB", "    Status: {:?}", status);
        debug_log!(DebugLevel::Trace, "RustTestDB", "    Category: {}", category);

        test_db::update_test_result(
            &mut test_db,
            &test_id,
            &test_name,
            &test_file,
            &category,
            status,
            duration_ms,
            failure,
            false, // Don't mark other tests as stale
        );
    }

    debug_log!(
        DebugLevel::Basic,
        "RustTestDB",
        "Updated {} Rust test records",
        results.len()
    );

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

    // Rust test categories
    if path_str.ends_with(".rs") || path_str.contains("src/rust") || path_str.starts_with("rust::") {
        if path_str.contains("tests/") || path_str.contains("integration") {
            return "RustIntegration".to_string();
        }
        if path_str.contains("doctests") || path_str.contains("line ") || path_str.contains("rustdoc") {
            return "RustDoc".to_string();
        }
        return "RustUnit".to_string();
    }

    // Simple test categories
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
    } else if result.ignored > 0 {
        // Tests were ignored (intentionally disabled with ignore_it)
        (TestStatus::Ignored, None)
    } else if result.passed > 0 {
        (TestStatus::Passed, None)
    } else if result.skipped > 0 {
        (TestStatus::Skipped, None)
    } else {
        (TestStatus::Skipped, None)
    }
}

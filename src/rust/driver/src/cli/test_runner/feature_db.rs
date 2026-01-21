//! Feature database update utilities.
//!
//! Handles updating the feature database from test results.

use std::path::PathBuf;

use super::types::TestFileResult;

/// Update feature database from test results
pub fn update_feature_database(test_files: &[PathBuf], results: &mut Vec<TestFileResult>, total_failed: &mut usize) {
    let feature_db_path = PathBuf::from("doc/features/feature_db.sdn");
    let sspec_files: Vec<PathBuf> = test_files
        .iter()
        .filter(|path| {
            path.file_name()
                .and_then(|n| n.to_str())
                .map(|n| n.ends_with("_spec.spl"))
                .unwrap_or(false)
        })
        .cloned()
        .collect();

    let failed_specs: Vec<PathBuf> = results
        .iter()
        .filter(|result| result.failed > 0 || result.error.is_some())
        .map(|result| result.path.clone())
        .collect();

    if let Err(e) = crate::feature_db::update_feature_db_from_sspec(&feature_db_path, &sspec_files, &failed_specs) {
        *total_failed += 1;
        results.push(TestFileResult {
            path: feature_db_path,
            passed: 0,
            failed: 1,
            duration_ms: 0,
            error: Some(format!("feature db update failed: {}", e)),
        });
    }
}

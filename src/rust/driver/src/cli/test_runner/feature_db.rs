//! Feature database update utilities.
//!
//! Handles updating the feature database from test results.

use std::path::PathBuf;

use super::types::{TestFileResult, DebugLevel, debug_log};

/// Update feature database from test results
pub fn update_feature_database(test_files: &[PathBuf], results: &mut Vec<TestFileResult>, total_failed: &mut usize) {
    debug_log!(DebugLevel::Basic, "FeatureDB", "Updating feature database");

    let feature_db_path = PathBuf::from("doc/feature/feature_db.sdn");
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

    debug_log!(DebugLevel::Detailed, "FeatureDB", "  Found {} SSpec files", sspec_files.len());

    let failed_specs: Vec<PathBuf> = results
        .iter()
        .filter(|result| result.failed > 0 || result.error.is_some())
        .map(|result| result.path.clone())
        .collect();

    debug_log!(DebugLevel::Detailed, "FeatureDB", "  {} failed specs to mark", failed_specs.len());

    if let Err(e) = crate::feature_db::update_feature_db_from_sspec(&feature_db_path, &sspec_files, &failed_specs) {
        debug_log!(DebugLevel::Basic, "FeatureDB", "  WARNING: Feature DB update failed (non-fatal): {}", e);
        // Don't treat feature database update failures as test failures
        // This allows tests to pass even if feature DB update has issues
    } else {
        debug_log!(DebugLevel::Basic, "FeatureDB", "  Successfully updated feature database");
    }
}

//! File walking utilities for migration operations.

use std::path::{Path, PathBuf};
use walkdir::WalkDir;

/// Collect .spl files from a path (file or directory)
pub fn collect_spl_files(path: &Path) -> Vec<PathBuf> {
    if path.is_file() {
        vec![path.to_path_buf()]
    } else {
        // Walk directory and find all .spl files
        WalkDir::new(path)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| e.path().extension().and_then(|s| s.to_str()) == Some("spl"))
            .map(|e| e.path().to_path_buf())
            .collect::<Vec<_>>()
    }
}

/// Collect *_spec.spl files from a path (file or directory)
pub fn collect_spec_files(path: &Path) -> Vec<PathBuf> {
    if path.is_file() {
        vec![path.to_path_buf()]
    } else {
        // Walk directory and find all *_spec.spl files
        WalkDir::new(path)
            .into_iter()
            .filter_map(|e| e.ok())
            .filter(|e| {
                e.path()
                    .file_name()
                    .and_then(|n| n.to_str())
                    .map(|n| n.ends_with("_spec.spl"))
                    .unwrap_or(false)
            })
            .map(|e| e.path().to_path_buf())
            .collect::<Vec<_>>()
    }
}

/// Print migration summary for dry-run mode
pub fn print_dry_run_summary(modified_count: usize, total_files: usize, error_count: usize) {
    println!();
    println!("DRY RUN complete!");
    println!("  Would modify: {}", modified_count);
    println!("  Unchanged: {}", total_files - modified_count - error_count);
    println!("  Errors: {}", error_count);
    if modified_count > 0 {
        println!();
        println!("Run without --dry-run to apply these changes");
    }
}

/// Print migration summary for actual run
pub fn print_migration_summary(modified_count: usize, total_files: usize, error_count: usize) {
    println!();
    println!("Migration complete!");
    println!("  Modified: {}", modified_count);
    println!("  Unchanged: {}", total_files - modified_count - error_count);
    println!("  Errors: {}", error_count);
}

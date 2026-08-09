//! Coverage tracking utilities.
//!
//! Handles coverage data saving and reporting.

use simple_compiler::{get_coverage_output_path, get_global_coverage, save_global_coverage, is_coverage_enabled};

/// Save coverage data and print statistics
pub fn save_coverage_data(quiet: bool) {
    if !is_coverage_enabled() {
        return;
    }

    if let Err(e) = save_global_coverage() {
        if !quiet {
            eprintln!("Warning: Failed to save coverage data: {}", e);
        }
        return;
    }

    if quiet {
        return;
    }

    if let Some(path) = get_coverage_output_path() {
        println!("Coverage data saved to: {}", path);
    }
}

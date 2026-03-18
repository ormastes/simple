//! Coverage tracking utilities.
//!
//! Handles coverage data saving, reporting, and threshold enforcement.

use simple_compiler::{get_coverage_output_path, save_global_coverage, is_coverage_enabled};

/// Save coverage data, print summary, and check threshold.
/// Returns false if threshold check fails.
pub fn save_coverage_data(quiet: bool) -> bool {
    if !is_coverage_enabled() {
        return true;
    }

    if let Err(e) = save_global_coverage() {
        if !quiet {
            eprintln!("Warning: Failed to save coverage data: {}", e);
        }
        return true;
    }

    // Get SDN data for summary
    let sdn = unsafe {
        let ptr = simple_runtime::rt_coverage_dump_sdn();
        if ptr.is_null() {
            String::new()
        } else {
            let s = std::ffi::CStr::from_ptr(ptr).to_string_lossy().to_string();
            simple_runtime::rt_coverage_free_sdn(ptr);
            s
        }
    };

    // Parse and print summary
    let (total, covered) = parse_decision_counts(&sdn);
    let pct = if total > 0 { (covered as f64 / total as f64) * 100.0 } else { 100.0 };

    if !quiet {
        println!();
        println!("=========================================");
        println!("Coverage Summary");
        println!("=========================================");
        println!("Decision coverage: {:.1}% ({}/{} decisions)", pct, covered, total);
        println!("=========================================");

        if let Some(path) = get_coverage_output_path() {
            println!("Coverage data saved to: {}", path);
        }
    }

    // Check threshold
    if let Ok(threshold_str) = std::env::var("SIMPLE_COVERAGE_THRESHOLD") {
        if let Ok(threshold) = threshold_str.parse::<f64>() {
            if threshold > 0.0 && pct < threshold {
                println!();
                println!("[Coverage] THRESHOLD FAILURE: {:.1}% < {}%", pct, threshold);
                return false;
            }
            if !quiet {
                println!("[Coverage] Threshold check passed: {:.1}% >= {}%", pct, threshold);
            }
        }
    }

    true
}

/// Parse total and covered decision counts from SDN text.
/// Only counts decisions from .spl files (filters out .sdt, .md, <source>, etc.).
fn parse_decision_counts(sdn: &str) -> (usize, usize) {
    let mut total = 0usize;
    let mut covered = 0usize;
    let mut in_decisions = false;

    for line in sdn.lines() {
        let trimmed = line.trim();

        // Track which section we're in
        if trimmed.starts_with("decisions ") || trimmed.starts_with("decisions|") {
            in_decisions = true;
            continue;
        }
        if trimmed.starts_with("conditions ") || trimmed.starts_with("conditions|")
            || trimmed.starts_with("summary:")
            || trimmed.starts_with("paths ")
        {
            in_decisions = false;
            continue;
        }

        if !in_decisions || trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }

        // Parse decision entry: "id, file, line, column, true_count, false_count"
        let parts: Vec<&str> = trimmed.splitn(6, ',').collect();
        if parts.len() >= 6 {
            let file = parts[1].trim();
            // Only count .spl files — skip .sdt, .md, <source>, <error>, etc.
            if !file.ends_with(".spl") {
                continue;
            }
            let true_count: usize = parts[4].trim().parse().unwrap_or(0);
            let false_count: usize = parts[5].trim().parse().unwrap_or(0);
            total += 1;
            if true_count > 0 && false_count > 0 {
                covered += 1;
            }
        }
    }

    (total, covered)
}

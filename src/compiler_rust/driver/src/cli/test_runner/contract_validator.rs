//! Coverage contract validation engine.
//!
//! Validates `# @covers`, `# @covers_fn`, and `# @not_covers` directives
//! against actual coverage data collected during test execution.

use simple_parser::ast::nodes::test_meta::CoverageContract;
use super::types::CoverageContractResult;

/// Parse decision counts for a specific target file from SDN coverage text.
///
/// Returns (total_decisions, covered_decisions) for decisions whose file
/// path matches `target_path` using suffix-based normalization.
fn parse_decision_counts_for_file(sdn: &str, target_path: &str) -> (usize, usize) {
    let mut total = 0usize;
    let mut covered = 0usize;
    let mut in_decisions = false;

    for line in sdn.lines() {
        let trimmed = line.trim();

        if trimmed.starts_with("decisions ") || trimmed.starts_with("decisions|") {
            in_decisions = true;
            continue;
        }
        if trimmed.starts_with("conditions ")
            || trimmed.starts_with("conditions|")
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
            if !file_matches(file, target_path) {
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

/// Check whether a specific function has covered decisions in the SDN data.
///
/// Strategy: Parse the target source file to find the function's line range,
/// then check if any decisions within that range were covered. Falls back to
/// checking if any decision line is within a heuristic range of a `fn <name>` definition.
fn check_function_covered(sdn: &str, target_path: &str, fn_name: &str) -> bool {
    let mut in_decisions = false;
    let mut decision_lines: Vec<(usize, bool)> = Vec::new(); // (line, was_covered)

    // Collect all decisions for the target file
    for line in sdn.lines() {
        let trimmed = line.trim();

        if trimmed.starts_with("decisions ") || trimmed.starts_with("decisions|") {
            in_decisions = true;
            continue;
        }
        if trimmed.starts_with("conditions ")
            || trimmed.starts_with("conditions|")
            || trimmed.starts_with("summary:")
            || trimmed.starts_with("paths ")
        {
            in_decisions = false;
            continue;
        }

        if !in_decisions || trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }

        let parts: Vec<&str> = trimmed.splitn(6, ',').collect();
        if parts.len() >= 6 {
            let file = parts[1].trim();
            if !file_matches(file, target_path) {
                continue;
            }
            let line_num: usize = parts[2].trim().parse().unwrap_or(0);
            let true_count: usize = parts[4].trim().parse().unwrap_or(0);
            let false_count: usize = parts[5].trim().parse().unwrap_or(0);
            let was_covered = true_count > 0 && false_count > 0;
            decision_lines.push((line_num, was_covered));
        }
    }

    if decision_lines.is_empty() {
        return false;
    }

    // Try to find function definition line range by reading the source file
    if let Some((_start, end)) = find_function_line_range(target_path, fn_name) {
        // Check if any covered decisions fall within the function's line range
        return decision_lines
            .iter()
            .any(|(line, covered)| *covered && *line >= _start && *line <= end);
    }

    // Fallback: check if function name appears in sdn paths section
    // or just check if ANY decision was covered (loose match)
    false
}

/// Find the line range (start, end) of a function definition in a source file.
/// Returns None if the file cannot be read or the function is not found.
fn find_function_line_range(file_path: &str, fn_name: &str) -> Option<(usize, usize)> {
    // Try multiple path resolutions
    let content = try_read_source_file(file_path)?;

    let fn_pattern = format!("fn {}(", fn_name);
    let fn_pattern2 = format!("fn {}:", fn_name); // Simple language uses `fn name:` syntax too
    let def_pattern = format!("def {}(", fn_name);

    let lines: Vec<&str> = content.lines().collect();
    let mut fn_start = None;

    for (i, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if trimmed.contains(&fn_pattern)
            || trimmed.contains(&fn_pattern2)
            || trimmed.contains(&def_pattern)
        {
            fn_start = Some(i + 1); // 1-based line numbers
            break;
        }
    }

    let start = fn_start?;

    // Find the end of the function by tracking indentation
    let start_indent = lines[start - 1].len() - lines[start - 1].trim_start().len();
    let mut end = start;

    for (i, line) in lines.iter().enumerate().skip(start) {
        let trimmed = line.trim();
        if trimmed.is_empty() {
            continue;
        }
        let indent = line.len() - trimmed.len();
        if indent <= start_indent && i > start - 1 {
            break;
        }
        end = i + 1; // 1-based
    }

    Some((start, end))
}

/// Try to read a source file, attempting multiple path resolutions.
fn try_read_source_file(file_path: &str) -> Option<String> {
    // Try direct path
    if let Ok(content) = std::fs::read_to_string(file_path) {
        return Some(content);
    }
    // Try relative to cwd
    let cwd = std::env::current_dir().ok()?;
    let full_path = cwd.join(file_path);
    std::fs::read_to_string(full_path).ok()
}

/// Check if a file path from SDN data matches the target path.
/// Uses suffix-based normalization to handle different path prefixes.
/// Also handles `src/lib/` vs `src/std/` aliasing (hardlinked directories).
/// If `target_path` ends with `/`, it is treated as a directory prefix —
/// any SDN file whose (normalized) path contains the directory prefix matches.
fn file_matches(sdn_file: &str, target_path: &str) -> bool {
    // Handle src/lib/ <-> src/std/ aliasing (hardlinked directories)
    let normalize = |p: &str| p.replace("src/lib/", "src/std/").replace("src\\lib\\", "src\\std\\");

    // Directory prefix match: target ends with '/'
    if target_path.ends_with('/') {
        let norm_sdn = normalize(sdn_file);
        let norm_target = normalize(target_path);
        // Check if the normalized SDN path contains the directory prefix
        return norm_sdn.contains(&norm_target) || sdn_file.contains(target_path);
    }

    if sdn_file == target_path {
        return true;
    }
    // Suffix match: "src/lib/common/array.spl" matches "/full/path/src/lib/common/array.spl"
    if sdn_file.ends_with(target_path) || target_path.ends_with(sdn_file) {
        return true;
    }
    let norm_sdn = normalize(sdn_file);
    let norm_target = normalize(target_path);
    if norm_sdn == norm_target {
        return true;
    }
    norm_sdn.ends_with(&norm_target) || norm_target.ends_with(&norm_sdn)
}

/// Validate a set of coverage contracts against SDN coverage data.
///
/// Returns a result for each contract indicating pass/fail with details.
pub fn validate_contracts(
    contracts: &[CoverageContract],
    sdn: &str,
) -> Vec<CoverageContractResult> {
    contracts.iter().map(|contract| validate_one(contract, sdn)).collect()
}

/// Validate a single coverage contract.
fn validate_one(contract: &CoverageContract, sdn: &str) -> CoverageContractResult {
    let (total, covered) = parse_decision_counts_for_file(sdn, &contract.target_path);
    let actual_pct = if total > 0 {
        (covered as f64 / total as f64) * 100.0
    } else {
        0.0
    };

    // Handle negative contracts (@not_covers)
    if contract.is_negative {
        let touched = total > 0 && covered > 0;
        return CoverageContractResult {
            target_path: contract.target_path.clone(),
            required_percent: None,
            actual_percent: actual_pct,
            function_results: vec![],
            is_negative: true,
            passed: !touched,
            failure_reason: if touched {
                Some(format!(
                    "expected NOT covered but got {:.1}% ({}/{})",
                    actual_pct, covered, total
                ))
            } else {
                None
            },
        };
    }

    // Handle function-level contracts (@covers_fn)
    if !contract.required_functions.is_empty() {
        let fn_results: Vec<(String, bool)> = contract
            .required_functions
            .iter()
            .map(|fn_name| {
                let covered = check_function_covered(sdn, &contract.target_path, fn_name);
                (fn_name.clone(), covered)
            })
            .collect();

        let all_covered = fn_results.iter().all(|(_, c)| *c);
        let failure_reason = if !all_covered {
            let uncovered: Vec<&str> = fn_results
                .iter()
                .filter(|(_, c)| !c)
                .map(|(name, _)| name.as_str())
                .collect();
            Some(format!("uncovered functions: {}", uncovered.join(", ")))
        } else {
            None
        };

        return CoverageContractResult {
            target_path: contract.target_path.clone(),
            required_percent: None,
            actual_percent: actual_pct,
            function_results: fn_results,
            is_negative: false,
            passed: all_covered,
            failure_reason,
        };
    }

    // Handle file-level contracts (@covers with optional threshold)
    match contract.threshold_percent {
        Some(threshold) => {
            let passed = actual_pct >= threshold;
            CoverageContractResult {
                target_path: contract.target_path.clone(),
                required_percent: Some(threshold),
                actual_percent: actual_pct,
                function_results: vec![],
                is_negative: false,
                passed,
                failure_reason: if !passed {
                    Some(format!(
                        "{:.1}% < {}% threshold ({}/{})",
                        actual_pct, threshold, covered, total
                    ))
                } else {
                    None
                },
            }
        }
        None => {
            // Touch only: any coverage > 0%
            let touched = total > 0 && covered > 0;
            CoverageContractResult {
                target_path: contract.target_path.clone(),
                required_percent: None,
                actual_percent: actual_pct,
                function_results: vec![],
                is_negative: false,
                passed: touched,
                failure_reason: if !touched {
                    Some(format!(
                        "expected file to be touched but got 0% coverage ({} decisions)",
                        total
                    ))
                } else {
                    None
                },
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_sdn() -> &'static str {
        r#"decisions |6|
1, src/lib/common/array.spl, 10, 5, 3, 2
2, src/lib/common/array.spl, 15, 5, 5, 0
3, src/lib/common/array.spl, 20, 5, 4, 3
4, src/lib/common/string.spl, 8, 5, 0, 0
5, src/lib/common/string.spl, 12, 5, 1, 1
6, src/lib/common/date.spl, 5, 5, 0, 0
conditions |0|
"#
    }

    #[test]
    fn test_parse_decision_counts_for_file() {
        let (total, covered) = parse_decision_counts_for_file(sample_sdn(), "src/lib/common/array.spl");
        assert_eq!(total, 3);
        assert_eq!(covered, 2); // entries 1 and 3 have both true_count>0 and false_count>0
    }

    #[test]
    fn test_file_matches() {
        assert!(file_matches("src/lib/common/array.spl", "src/lib/common/array.spl"));
        assert!(file_matches("/full/path/src/lib/common/array.spl", "src/lib/common/array.spl"));
        assert!(file_matches("src/lib/common/array.spl", "/full/path/src/lib/common/array.spl"));
        assert!(!file_matches("src/lib/common/string.spl", "src/lib/common/array.spl"));
        // src/lib/ <-> src/std/ normalization (hardlinked directories)
        assert!(file_matches("src/std/common/array.spl", "src/lib/common/array.spl"));
        assert!(file_matches("src/lib/common/array.spl", "src/std/common/array.spl"));
        assert!(!file_matches("src/std/common/array.spl", "src/lib/common/string.spl"));
    }

    #[test]
    fn test_file_matches_directory_prefix() {
        // Directory prefix: target ends with '/'
        assert!(file_matches("src/lib/common/json/parser.spl", "src/lib/common/json/"));
        assert!(file_matches("src/lib/common/json/lexer.spl", "src/lib/common/json/"));
        assert!(!file_matches("src/lib/common/yaml/parser.spl", "src/lib/common/json/"));
        // Directory prefix with src/lib/ <-> src/std/ normalization
        assert!(file_matches("src/std/common/json/parser.spl", "src/lib/common/json/"));
        assert!(file_matches("src/lib/common/json/parser.spl", "src/std/common/json/"));
    }

    #[test]
    fn test_covers_with_threshold_pass() {
        let contract = CoverageContract {
            target_path: "src/lib/common/array.spl".to_string(),
            threshold_percent: Some(60.0),
            required_functions: vec![],
            is_negative: false,
        };
        let results = validate_contracts(&[contract], sample_sdn());
        assert_eq!(results.len(), 1);
        assert!(results[0].passed);
        assert!(results[0].actual_percent > 60.0);
    }

    #[test]
    fn test_covers_with_threshold_fail() {
        let contract = CoverageContract {
            target_path: "src/lib/common/array.spl".to_string(),
            threshold_percent: Some(90.0),
            required_functions: vec![],
            is_negative: false,
        };
        let results = validate_contracts(&[contract], sample_sdn());
        assert_eq!(results.len(), 1);
        assert!(!results[0].passed);
        assert!(results[0].failure_reason.is_some());
    }

    #[test]
    fn test_covers_touch_only() {
        // string.spl has one covered decision
        let contract = CoverageContract {
            target_path: "src/lib/common/string.spl".to_string(),
            threshold_percent: None,
            required_functions: vec![],
            is_negative: false,
        };
        let results = validate_contracts(&[contract], sample_sdn());
        assert!(results[0].passed);
    }

    #[test]
    fn test_not_covers_pass() {
        // date.spl has 0 covered decisions (true_count=0, false_count=0)
        let contract = CoverageContract {
            target_path: "src/lib/common/date.spl".to_string(),
            threshold_percent: None,
            required_functions: vec![],
            is_negative: true,
        };
        let results = validate_contracts(&[contract], sample_sdn());
        assert!(results[0].passed);
    }

    #[test]
    fn test_not_covers_fail() {
        // array.spl IS covered, so @not_covers should fail
        let contract = CoverageContract {
            target_path: "src/lib/common/array.spl".to_string(),
            threshold_percent: None,
            required_functions: vec![],
            is_negative: true,
        };
        let results = validate_contracts(&[contract], sample_sdn());
        assert!(!results[0].passed);
        assert!(results[0].failure_reason.as_ref().unwrap().contains("NOT covered"));
    }
}

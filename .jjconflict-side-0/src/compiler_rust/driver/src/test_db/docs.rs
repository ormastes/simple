//! Documentation/report generation for test results.

use super::types::*;
use std::fs;
use std::path::Path;

// ============================================================================
// Report generation
// ============================================================================

/// Generate test result documentation
pub fn generate_test_result_docs(db: &TestDb, output_dir: &Path) -> Result<(), String> {
    let mut md = String::new();

    md.push_str("# Test Results\n\n");
    md.push_str(&format!(
        "**Generated:** {}\n",
        chrono::Local::now().format("%Y-%m-%d %H:%M:%S")
    ));

    let mut passed = 0;
    let mut failed = 0;
    let mut skipped = 0;
    let mut ignored = 0;
    let mut qualified_ignored = 0;

    for test in db.valid_records() {
        match test.status {
            TestStatus::Passed => passed += 1,
            TestStatus::Failed => failed += 1,
            TestStatus::Skipped => skipped += 1,
            TestStatus::Ignored => ignored += 1,
            TestStatus::QualifiedIgnore => qualified_ignored += 1,
        }
    }

    let total = passed + failed + skipped + ignored + qualified_ignored;
    md.push_str(&format!("**Total Tests:** {}\n", total));

    let status_emoji = if failed > 0 {
        "⚠️"
    } else if total == 0 {
        "❔"
    } else {
        "✅"
    };
    md.push_str(&format!("**Status:** {} ", status_emoji));
    if failed > 0 {
        md.push_str(&format!("{} FAILED\n\n", failed));
    } else {
        md.push_str("ALL PASSED\n\n");
    }

    md.push_str("## Summary\n\n");
    md.push_str("| Status | Count | Percentage |\n");
    md.push_str("|--------|-------|-----------|\n");

    let pct = |count: usize| {
        if total == 0 {
            0.0
        } else {
            (count as f64 / total as f64) * 100.0
        }
    };

    md.push_str(&format!("| ✅ Passed | {} | {:.1}% |\n", passed, pct(passed)));
    md.push_str(&format!("| ❌ Failed | {} | {:.1}% |\n", failed, pct(failed)));
    md.push_str(&format!("| ⏭️ Skipped | {} | {:.1}% |\n", skipped, pct(skipped)));
    md.push_str(&format!("| 🔕 Ignored | {} | {:.1}% |\n", ignored, pct(ignored)));
    md.push_str(&format!(
        "| 🔐 Qualified Ignore | {} | {:.1}% |\n\n",
        qualified_ignored,
        pct(qualified_ignored)
    ));

    // Recent Status Changes section (V3 feature)
    if !db.changes.is_empty() {
        md.push_str("---\n\n");
        md.push_str("## 🔄 Recent Status Changes\n\n");
        md.push_str("| Test | Change | Run |\n");
        md.push_str("|------|--------|-----|\n");

        for change in db.changes.iter().take(20) {
            let test_name = if (change.test_id as usize) < db.interner.len() {
                db.interner.get_or_empty(change.test_id).to_string()
            } else {
                format!("test_{}", change.test_id)
            };
            md.push_str(&format!(
                "| {} | {} | {} |\n",
                test_name, change.change_type, change.run_id
            ));
        }
        md.push('\n');
    }

    // Failed tests
    if failed > 0 {
        md.push_str("---\n\n");
        md.push_str(&format!("## ❌ Failed Tests ({})\n\n", failed));

        let failed_tests: Vec<&TestRecord> = db
            .valid_records()
            .into_iter()
            .filter(|t| t.status == TestStatus::Failed)
            .collect();

        for test in failed_tests {
            md.push_str(&format!("### 🔴 {}\n\n", test.test_name));
            md.push_str(&format!("**File:** `{}`\n", test.test_file));
            md.push_str(&format!("**Category:** {}\n", test.category));
            md.push_str(&format!("**Failed:** {}\n", test.last_run));
            md.push_str(&format!(
                "**Flaky:** {} ({:.1}% failure rate)\n\n",
                if test.execution_history.flaky { "Yes" } else { "No" },
                test.execution_history.failure_rate_pct
            ));

            if let Some(ref failure) = test.failure {
                md.push_str("**Error:**\n```\n");
                md.push_str(&failure.error_message);
                md.push('\n');
                if let Some(ref location) = failure.location {
                    md.push_str(&format!("Location: {}\n", location));
                }
                md.push_str("```\n\n");
            }

            if !test.related_bugs.is_empty() {
                md.push_str(&format!("**Linked Bugs:** [{}]\n\n", test.related_bugs.join(", ")));
            }

            if test.timing.baseline_median > 0.0 {
                let change_pct = if test.timing.baseline_median != 0.0 {
                    ((test.timing.last_run_time - test.timing.baseline_median) / test.timing.baseline_median) * 100.0
                } else {
                    0.0
                };
                let indicator = if change_pct > 10.0 {
                    "🔴"
                } else if change_pct > 5.0 {
                    "🟡"
                } else {
                    ""
                };
                md.push_str(&format!(
                    "**Timing:** {:.1}ms (baseline: {:.1}ms, {:+.1}% {})\n\n",
                    test.timing.last_run_time, test.timing.baseline_median, change_pct, indicator
                ));
            }

            md.push_str("---\n\n");
        }
    }

    // Timing Analysis
    md.push_str("---\n\n");
    md.push_str("## 📊 Timing Analysis\n\n");

    let mut regressions: Vec<(&TestRecord, f64)> = db
        .valid_records()
        .iter()
        .filter_map(|t| {
            if t.timing.baseline_median > 0.0 {
                let change_pct =
                    ((t.timing.last_run_time - t.timing.baseline_median) / t.timing.baseline_median) * 100.0;
                if change_pct > db.config.default_timing_config.alert_threshold_pct {
                    Some((*t, change_pct))
                } else {
                    None
                }
            } else {
                None
            }
        })
        .collect();

    regressions.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());

    if !regressions.is_empty() {
        md.push_str(&format!("### Performance Regressions ({})\n\n", regressions.len()));
        md.push_str("Tests that are significantly slower than baseline:\n\n");
        md.push_str("| Test | Current | Baseline | Change | Status |\n");
        md.push_str("|------|---------|----------|--------|--------|\n");

        for (test, change_pct) in regressions.iter().take(10) {
            md.push_str(&format!(
                "| {} | {:.1}ms | {:.1}ms | {:+.1}% | 🔴 ALERT |\n",
                test.test_name, test.timing.last_run_time, test.timing.baseline_median, change_pct
            ));
        }
        md.push('\n');
    }

    let mut high_variance: Vec<(&TestRecord, f64)> = db
        .valid_records()
        .iter()
        .filter_map(|t| {
            if t.timing.baseline_cv_pct > 50.0 {
                Some((*t, t.timing.baseline_cv_pct))
            } else {
                None
            }
        })
        .collect();

    high_variance.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());

    if !high_variance.is_empty() {
        md.push_str("### High Variance Tests (CV% > 50%)\n\n");
        md.push_str("Tests with unstable timing:\n\n");
        md.push_str("| Test | Mean | Std Dev | CV% | Recommendation |\n");
        md.push_str("|------|------|---------|-----|----------------|\n");

        for (test, cv_pct) in high_variance.iter().take(10) {
            let recommendation = if *cv_pct > 80.0 {
                "Investigate flakiness"
            } else {
                "May need longer warmup"
            };
            md.push_str(&format!(
                "| {} | {:.1}ms | {:.1}ms | {:.1}% | {} |\n",
                test.test_name, test.timing.baseline_mean, test.timing.baseline_std_dev, cv_pct, recommendation
            ));
        }
        md.push('\n');
    }

    let mut fastest: Vec<(&TestRecord, f64)> = db
        .valid_records()
        .iter()
        .filter_map(|t| {
            if t.timing.baseline_median > 0.0 {
                Some((*t, t.timing.baseline_median))
            } else {
                None
            }
        })
        .collect();

    fastest.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());

    if !fastest.is_empty() {
        md.push_str("### Fastest Tests (Top 10)\n\n");
        md.push_str("| Test | Time |\n");
        md.push_str("|------|------|\n");
        for (test, time) in fastest.iter().take(10) {
            md.push_str(&format!("| {} | {:.1}ms |\n", test.test_name, time));
        }
        md.push('\n');
    }

    let mut slowest: Vec<(&TestRecord, f64)> = db
        .valid_records()
        .iter()
        .filter_map(|t| {
            if t.timing.baseline_median > 0.0 {
                Some((*t, t.timing.baseline_median))
            } else {
                None
            }
        })
        .collect();

    slowest.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap());

    if !slowest.is_empty() {
        md.push_str("### Slowest Tests (Top 10)\n\n");
        md.push_str("| Test | Time |\n");
        md.push_str("|------|------|\n");
        for (test, time) in slowest.iter().take(10) {
            md.push_str(&format!("| {} | {:.1}ms |\n", test.test_name, time));
        }
        md.push('\n');
    }

    // Action Items
    md.push_str("---\n\n");
    md.push_str("## 🎯 Action Items\n\n");

    if failed > 0 {
        md.push_str(&format!("### Priority 1: Fix Failing Tests ({})\n\n", failed));

        let failed_tests: Vec<&TestRecord> = db
            .valid_records()
            .into_iter()
            .filter(|t| t.status == TestStatus::Failed)
            .collect();

        for (i, test) in failed_tests.iter().take(5).enumerate() {
            md.push_str(&format!("{}. **{}** - ", i + 1, test.test_name));
            if let Some(ref failure) = test.failure {
                let short_msg = failure.error_message.lines().next().unwrap_or("Unknown error");
                md.push_str(short_msg);
            }
            md.push('\n');
            if !test.related_bugs.is_empty() {
                md.push_str(&format!("   - Related bugs: {}\n", test.related_bugs.join(", ")));
            }
        }
        md.push('\n');
    }

    if !regressions.is_empty() {
        md.push_str(&format!(
            "### Priority 2: Investigate Performance Regressions ({})\n\n",
            regressions.len()
        ));
        md.push_str("Tests showing significant slowdown compared to baseline:\n");
        for (test, change_pct) in regressions.iter().take(5) {
            md.push_str(&format!("- {} ({:+.1}%)\n", test.test_name, change_pct));
        }
        md.push('\n');
    }

    let flaky_tests: Vec<&TestRecord> = db
        .valid_records()
        .into_iter()
        .filter(|t| t.execution_history.flaky)
        .collect();

    if !flaky_tests.is_empty() {
        md.push_str(&format!(
            "### Priority 3: Stabilize Flaky Tests ({})\n\n",
            flaky_tests.len()
        ));
        md.push_str("Tests with intermittent failures:\n");
        for test in flaky_tests.iter().take(5) {
            md.push_str(&format!(
                "- {} ({:.1}% failure rate)\n",
                test.test_name, test.execution_history.failure_rate_pct
            ));
        }
        md.push('\n');
    }

    // Qualified Ignored
    let qualified_ignored_tests: Vec<&TestRecord> = db
        .valid_records()
        .into_iter()
        .filter(|t| t.status == TestStatus::QualifiedIgnore)
        .collect();

    if !qualified_ignored_tests.is_empty() {
        md.push_str("---\n\n");
        md.push_str(&format!(
            "## 🔐 Qualified Ignored Tests ({})\n\n",
            qualified_ignored_tests.len()
        ));
        md.push_str("Tests ignored with authorized qualification:\n\n");
        md.push_str("| Test | Qualified By | Reason | Date |\n");
        md.push_str("|------|-------------|--------|------|\n");

        for test in qualified_ignored_tests.iter().take(20) {
            let qualified_by = test.qualified_by.as_deref().unwrap_or("-");
            let reason = test.qualified_reason.as_deref().unwrap_or("-");
            let date = test
                .qualified_at
                .as_deref()
                .and_then(|s| s.split('T').next())
                .unwrap_or("-");
            md.push_str(&format!(
                "| {} | {} | {} | {} |\n",
                test.test_name, qualified_by, reason, date
            ));
        }
        md.push('\n');
    }

    let output_path = output_dir.join("test_result.md");
    fs::create_dir_all(output_dir).map_err(|e| e.to_string())?;
    fs::write(&output_path, md).map_err(|e| e.to_string())?;

    Ok(())
}

/// Check if a test record needs qualification
pub fn needs_qualification(record: &TestRecord) -> bool {
    record.status == TestStatus::Ignored && record.qualified_by.is_none()
}

/// Count the number of unqualified ignored tests
pub fn count_unqualified_ignores(db: &TestDb) -> usize {
    db.records.values().filter(|r| needs_qualification(r)).count()
}

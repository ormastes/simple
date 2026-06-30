//! V3 format serialization and database saving.

use super::runs::runs_file_path;
use super::types::*;
use super::types::debug_log;
use crate::db_lock::FileLock;
use std::fs;
use std::path::Path;

// ============================================================================
// Save — V3 format
// ============================================================================

/// Save test database to SDN file (V3 format).
/// Only writes test_db.sdn if content has changed.
pub fn save_test_db(path: &Path, db: &TestDb) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }

    // Guard: refuse to save empty DB if existing file has records
    if db.records.is_empty() && path.exists() {
        if let Ok(meta) = fs::metadata(path) {
            if meta.len() > 500 {
                debug_log!(
                    DebugLevel::Basic,
                    "TestDB",
                    "Refusing to overwrite non-empty database ({} bytes) with empty database",
                    meta.len()
                );
                return Ok(());
            }
        }
    }

    let _lock = FileLock::acquire(path, 2).map_err(|e| format!("Failed to acquire lock: {:?}", e))?;

    // Build V3 content
    let content = build_v3_sdn(db);

    // Compare with existing to avoid unnecessary writes
    if path.exists() {
        if let Ok(existing) = fs::read_to_string(path) {
            if existing == content {
                debug_log!(
                    DebugLevel::Detailed,
                    "TestDB",
                    "No changes to test_db.sdn, skipping write"
                );
                // Still save volatile data
                save_volatile_data(path, db)?;
                return Ok(());
            }
        }
    }

    // No .sdn.prev backup — jj handles history/rollback

    // Atomic write
    let temp_path = path.with_extension("sdn.tmp");
    fs::write(&temp_path, &content).map_err(|e| e.to_string())?;
    fs::rename(&temp_path, path).map_err(|e| e.to_string())?;

    // Save volatile data
    save_volatile_data(path, db)?;

    Ok(())
}

/// Check if an SDN string value needs quoting in table rows.
///
/// Values containing SDN-significant characters must be quoted to avoid
/// confusing the parser.  For example, `14a73b269158` starts with digits
/// so the lexer splits it into a number + identifier; colons trigger dict
/// parsing; brackets/parens affect bracket depth tracking.
fn needs_quoting(value: &str) -> bool {
    if value.is_empty() {
        return false; // Empty values are represented by consecutive commas
    }
    // Always quote if value contains characters that are significant to the
    // SDN lexer or parser:
    value.contains(',')
        || value.contains('"')
        || value.contains('\n')
        || value.contains(':')
        || value.contains('[')
        || value.contains(']')
        || value.contains('(')
        || value.contains(')')
        || value.contains('{')
        || value.contains('}')
        || value.contains('|')
        || value.contains('=')
        || value.contains(' ')
        || value.contains('\t')
        // Values starting with a digit that also contain letters (hex hashes
        // like `14a73b269158`) get split by the lexer into number + ident.
        || (value.starts_with(|c: char| c.is_ascii_digit())
            && value.contains(|c: char| c.is_alphabetic()))
}

/// Build V3 SDN content string.
pub(crate) fn build_v3_sdn(db: &TestDb) -> String {
    let mut out = String::new();

    // Strings table
    out.push_str("strings |id, value|\n");
    for (id, value) in db.interner.to_sdn_rows() {
        if needs_quoting(value) {
            out.push_str(&format!("    {}, \"{}\"\n", id, value.replace('"', "\\\"")));
        } else {
            out.push_str(&format!("    {}, {}\n", id, value));
        }
    }
    out.push('\n');

    // Files table
    out.push_str("files |file_id, path_str|\n");
    for f in &db.files {
        out.push_str(&format!("    {}, {}\n", f.file_id, f.path_str));
    }
    out.push('\n');

    // Suites table
    out.push_str("suites |suite_id, file_id, name_str|\n");
    for s in &db.suites {
        out.push_str(&format!("    {}, {}, {}\n", s.suite_id, s.file_id, s.name_str));
    }
    out.push('\n');

    // Tests table — stable fields only (counters/timing in volatile runs file)
    // Sorted by test_id for deterministic output
    out.push_str("tests |test_id, suite_id, name_str, category_str, status_str, tags_str, description_str, valid, qualified_by, qualified_at, qualified_reason|\n");
    let mut sorted_records: Vec<_> = db.records.values().collect();
    sorted_records.sort_by(|a, b| a.test_id.cmp(&b.test_id));

    for (idx, record) in sorted_records.iter().enumerate() {
        let suite_id = record.suite_id.unwrap_or(0);
        let name_str = record.name_str_id.unwrap_or(0);
        let category_str = record.category_str_id.unwrap_or(0);
        let status_str = record.status_str_id.unwrap_or(0);
        let tags_str = record.tags.join(",");
        let desc = &record.description;

        out.push_str(&format!(
            "    {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}\n",
            idx,
            suite_id,
            name_str,
            category_str,
            status_str,
            if tags_str.is_empty() {
                String::new()
            } else {
                format!("\"{}\"", tags_str)
            },
            if desc.is_empty() {
                String::new()
            } else {
                format!("\"{}\"", desc.replace('"', "\\\""))
            },
            record.valid,
            record.qualified_by.as_deref().unwrap_or(""),
            record.qualified_at.as_deref().unwrap_or(""),
            record
                .qualified_reason
                .as_deref()
                .map(|s| format!("\"{}\"", s.replace('"', "\\\"")))
                .unwrap_or_default(),
        ));
    }

    out
}

/// Save volatile data (timing, runs, changes) to test_db_runs.sdn.
fn save_volatile_data(db_path: &Path, db: &TestDb) -> Result<(), String> {
    let runs_path = runs_file_path(db_path);

    if let Some(parent) = runs_path.parent() {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }

    let mut out = String::new();

    // Counters (volatile — per-test run counts, changes every run)
    out.push_str("counters |test_id, total_runs, passed, failed, flaky_count, last_change|\n");
    let mut counter_ids: Vec<_> = db
        .records
        .values()
        .filter_map(|r| r.name_str_id.map(|id| (id, r)))
        .collect();
    counter_ids.sort_by_key(|(id, _)| *id);
    for (id, record) in &counter_ids {
        out.push_str(&format!(
            "    {}, {}, {}, {}, {}, {}\n",
            id,
            record.execution_history.total_runs,
            record.execution_history.passed,
            record.execution_history.failed,
            record.flaky_count,
            record.last_change,
        ));
    }
    out.push('\n');

    // Timing summaries
    out.push_str("timing |test_id, last_ms, p50, p90, p95, baseline_median|\n");
    let mut timing_ids: Vec<_> = db.timing_summaries.keys().collect();
    timing_ids.sort();
    for &id in &timing_ids {
        if let Some(t) = db.timing_summaries.get(id) {
            out.push_str(&format!(
                "    {}, {}, {}, {}, {}, {}\n",
                t.test_id, t.last_ms, t.p50, t.p90, t.p95, t.baseline_median
            ));
        }
    }
    out.push('\n');

    // Timing runs
    out.push_str("timing_runs |test_id, timestamp, duration_ms, outlier|\n");
    let mut run_ids: Vec<_> = db.timing_runs.keys().collect();
    run_ids.sort();
    for &id in &run_ids {
        if let Some(runs) = db.timing_runs.get(id) {
            for r in runs {
                out.push_str(&format!(
                    "    {}, \"{}\", {}, {}\n",
                    r.test_id, r.timestamp, r.duration_ms, r.outlier
                ));
            }
        }
    }
    out.push('\n');

    // Changes
    out.push_str("changes |test_id, change_type, run_id|\n");
    for c in &db.changes {
        out.push_str(&format!("    {}, {}, {}\n", c.test_id, c.change_type, c.run_id));
    }
    out.push('\n');

    // Test runs are managed separately via Database<TestRunRecord>
    // Don't overwrite them here — they're loaded/saved through the test run APIs

    let temp_path = runs_path.with_extension("sdn.tmp");
    fs::write(&temp_path, &out).map_err(|e| e.to_string())?;
    fs::rename(&temp_path, &runs_path).map_err(|e| e.to_string())?;

    Ok(())
}

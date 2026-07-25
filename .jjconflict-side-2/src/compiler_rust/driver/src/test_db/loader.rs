//! V3 format parsing, SDN deserialization, and database loading.

use super::runs::runs_file_path;
use super::saver::save_test_db;
use super::types::*;
use super::types::debug_log;
use crate::db_lock::FileLock;
use simple_sdn::{parse_document, SdnValue};
use std::fs;
use std::path::Path;

// ============================================================================
// V3 Format Detection
// ============================================================================

/// Check if content is V3 format (has `strings` table).
fn is_v3_format(content: &str) -> bool {
    content.contains("strings |") || content.contains("strings|")
}

// ============================================================================
// Load
// ============================================================================

/// Load test database from SDN file.
pub fn load_test_db(path: &Path) -> Result<TestDb, String> {
    if !path.exists() {
        return Ok(TestDb::new());
    }

    let _lock = FileLock::acquire(path, 2).map_err(|e| format!("Failed to acquire lock: {:?}", e))?;

    let file_size = fs::metadata(path)
        .map_err(|e| format!("Failed to stat file: {}", e))?
        .len();
    const MAX_DB_SIZE: u64 = 500 * 1024 * 1024;
    if file_size > MAX_DB_SIZE {
        eprintln!(
            "[WARNING] Test database file is too large ({:.1} GB, limit is {:.0} MB). \
             The database will be reset. Old file preserved as .sdn.oversized",
            file_size as f64 / (1024.0 * 1024.0 * 1024.0),
            MAX_DB_SIZE as f64 / (1024.0 * 1024.0),
        );
        let backup_path = path.with_extension("sdn.oversized");
        if let Err(e) = fs::rename(path, &backup_path) {
            eprintln!("[WARNING] Failed to rename oversized file: {}", e);
        } else {
            eprintln!("[INFO] Oversized database moved to: {}", backup_path.display());
        }
        return Ok(TestDb::new());
    }

    let content = fs::read_to_string(path).map_err(|e| format!("Failed to read file: {}", e))?;

    if content.trim().is_empty() {
        return Ok(TestDb::new());
    }

    if is_v3_format(&content) {
        return load_test_db_v3(path, &content);
    }

    // V2 or older format — load then auto-migrate
    match parse_document(&content) {
        Ok(doc) => {
            let mut db = parse_test_db_sdn_v2(&doc)?;
            if db.records.is_empty() && content.lines().count() > 2 {
                debug_log!(
                    DebugLevel::Basic,
                    "TestDB",
                    "Warning: Database file has content but no records were parsed"
                );
            }
            // Auto-migrate to V3
            db.version = "3.0".to_string();
            db.rebuild_tree();
            db.rebuild_timing_from_records();
            // Save migrated format
            eprintln!("[INFO] Auto-migrating test_db.sdn from V2 to V3 format");
            let backup_path = path.with_extension("sdn.v2_backup");
            if let Err(e) = fs::copy(path, &backup_path) {
                debug_log!(
                    DebugLevel::Basic,
                    "TestDB",
                    "Warning: Failed to create V2 backup: {}",
                    e
                );
            }
            // Drop lock before saving (save acquires its own)
            drop(_lock);
            save_test_db(path, &db)?;
            Ok(db)
        }
        Err(sdn_err) => {
            // Fallback to JSON format
            serde_json::from_str(&content).map_err(|json_err| {
                format!(
                    "Failed to parse database - SDN error: {}, JSON error: {}",
                    sdn_err, json_err
                )
            })
        }
    }
}

/// Load V3 format test database.
fn load_test_db_v3(path: &Path, content: &str) -> Result<TestDb, String> {
    let doc = parse_document(content).map_err(|e| format!("Failed to parse V3 SDN: {}", e))?;
    let root = doc.root();

    let dict = match root {
        SdnValue::Dict(d) => d,
        _ => return Err("Expected dict at root of V3 test_db.sdn".to_string()),
    };

    let mut db = TestDb::new();

    // Load strings table
    if let Some(SdnValue::Table {
        fields: Some(_fields),
        rows,
        ..
    }) = dict.get("strings")
    {
        for row in rows {
            let id = match row.first() {
                Some(SdnValue::Int(n)) => *n as u32,
                Some(SdnValue::String(s)) => s.parse::<u32>().unwrap_or(0),
                _ => continue,
            };
            let value = match row.get(1) {
                Some(SdnValue::String(s)) => s.clone(),
                Some(SdnValue::Int(n)) => n.to_string(),
                _ => continue,
            };
            // Ensure sequential
            while db.interner.len() < id as usize {
                db.interner.intern("");
            }
            db.interner.intern(&value);
        }
    }

    // Load files table
    if let Some(SdnValue::Table {
        fields: Some(_), rows, ..
    }) = dict.get("files")
    {
        for row in rows {
            let file_id = sdn_row_u32(row, 0);
            let path_str = sdn_row_u32(row, 1);
            db.files.push(FileRecord { file_id, path_str });
        }
    }

    // Load suites table
    if let Some(SdnValue::Table {
        fields: Some(_), rows, ..
    }) = dict.get("suites")
    {
        for row in rows {
            let suite_id = sdn_row_u32(row, 0);
            let file_id = sdn_row_u32(row, 1);
            let name_str = sdn_row_u32(row, 2);
            db.suites.push(SuiteRecord {
                suite_id,
                file_id,
                name_str,
            });
        }
    }

    // Load tests table
    if let Some(SdnValue::Table {
        fields: Some(fields),
        rows,
        ..
    }) = dict.get("tests")
    {
        for row in rows {
            let get = |name: &str| -> String {
                fields
                    .iter()
                    .position(|f| f == name)
                    .and_then(|idx| row.get(idx))
                    .map(|v| match v {
                        SdnValue::String(s) => s.clone(),
                        SdnValue::Int(n) => n.to_string(),
                        SdnValue::Float(f) => f.to_string(),
                        SdnValue::Bool(b) => b.to_string(),
                        _ => String::new(),
                    })
                    .unwrap_or_default()
            };

            let test_id_idx = sdn_row_u32(row, 0);
            let suite_id = sdn_row_u32(row, 1);
            let name_str = sdn_row_u32(row, 2);
            let category_str = sdn_row_u32(row, 3);
            let status_str = sdn_row_u32(row, 4);

            // Resolve strings from interner
            let test_name = if (name_str as usize) < db.interner.len() {
                db.interner.get_or_empty(name_str).to_string()
            } else {
                format!("test_{}", test_id_idx)
            };

            let category = if (category_str as usize) < db.interner.len() {
                db.interner.get_or_empty(category_str).to_string()
            } else {
                "Unknown".to_string()
            };

            let status_s = if (status_str as usize) < db.interner.len() {
                db.interner.get_or_empty(status_str).to_string()
            } else {
                "passed".to_string()
            };

            let status = match status_s.as_str() {
                "passed" => TestStatus::Passed,
                "failed" => TestStatus::Failed,
                "skipped" => TestStatus::Skipped,
                "ignored" => TestStatus::Ignored,
                "qualifiedignore" | "qualified_ignore" => TestStatus::QualifiedIgnore,
                _ => TestStatus::Passed,
            };

            // Counters are loaded from volatile file; use defaults here,
            // then overwrite from counters table in load_volatile_data().
            let last_change_str = get("last_change");
            let last_change = if last_change_str.is_empty() {
                ChangeType::NoChange
            } else {
                ChangeType::parse_str(&last_change_str)
            };

            let total_runs: usize = get("total_runs").parse().unwrap_or(0);
            let passed_count: usize = get("passed").parse().unwrap_or(0);
            let failed_count: usize = get("failed").parse().unwrap_or(0);
            let flaky_count: u32 = get("flaky_count").parse().unwrap_or(0);

            // Resolve file path from suite -> file
            let test_file = if let Some(suite) = db.suites.iter().find(|s| s.suite_id == suite_id) {
                if let Some(file) = db.files.iter().find(|f| f.file_id == suite.file_id) {
                    if (file.path_str as usize) < db.interner.len() {
                        db.interner.get_or_empty(file.path_str).to_string()
                    } else {
                        String::new()
                    }
                } else {
                    String::new()
                }
            } else {
                String::new()
            };

            // Reconstruct test_id from file::suite::name
            let suite_name = if let Some(suite) = db.suites.iter().find(|s| s.suite_id == suite_id) {
                if (suite.name_str as usize) < db.interner.len() {
                    db.interner.get_or_empty(suite.name_str).to_string()
                } else {
                    "default".to_string()
                }
            } else {
                "default".to_string()
            };
            let test_id = format!("{}::{}::{}", test_file, suite_name, test_name);

            let failure_rate_pct = if total_runs > 0 {
                (failed_count as f64 / total_runs as f64) * 100.0
            } else {
                0.0
            };

            let tags_str = get("tags_str");
            let tags: Vec<String> = if tags_str.is_empty() {
                Vec::new()
            } else {
                tags_str
                    .split(',')
                    .filter(|s| !s.is_empty())
                    .map(|s| s.to_string())
                    .collect()
            };

            let qualified_by = {
                let s = get("qualified_by");
                if s.is_empty() {
                    None
                } else {
                    Some(s)
                }
            };
            let qualified_at = {
                let s = get("qualified_at");
                if s.is_empty() {
                    None
                } else {
                    Some(s)
                }
            };
            let qualified_reason = {
                let s = get("qualified_reason");
                if s.is_empty() {
                    None
                } else {
                    Some(s)
                }
            };

            let record = TestRecord {
                test_id: test_id.clone(),
                test_name,
                test_file,
                category,
                status,
                last_run: String::new(), // Volatile — loaded from runs file
                failure: None,           // Volatile
                execution_history: ExecutionHistory {
                    total_runs,
                    passed: passed_count,
                    failed: failed_count,
                    last_10_runs: Vec::new(), // Rebuilt from timing_runs
                    flaky: flaky_count > 0,
                    failure_rate_pct,
                },
                timing: TimingData::default(), // Volatile — loaded from runs file
                timing_config: None,
                related_bugs: Vec::new(),
                related_features: Vec::new(),
                tags,
                description: get("description_str"),
                valid: get("valid") != "false",
                qualified_by,
                qualified_at,
                qualified_reason,
                suite_id: Some(suite_id),
                name_str_id: Some(name_str),
                category_str_id: Some(category_str),
                status_str_id: Some(status_str),
                last_change,
                flaky_count,
            };

            db.records.insert(test_id, record);
        }
    }

    // Load volatile data from runs file
    let runs_path = runs_file_path(path);
    if runs_path.exists() {
        load_volatile_data(&mut db, &runs_path)?;
    }

    Ok(db)
}

/// Load volatile timing/run data from test_db_runs.sdn.
fn load_volatile_data(db: &mut TestDb, runs_path: &Path) -> Result<(), String> {
    let content = fs::read_to_string(runs_path).map_err(|e| format!("Failed to read runs file: {}", e))?;
    if content.trim().is_empty() {
        return Ok(());
    }

    let doc = parse_document(&content).map_err(|e| format!("Failed to parse runs SDN: {}", e))?;
    let root = doc.root();
    let dict = match root {
        SdnValue::Dict(d) => d,
        _ => return Ok(()), // No dict root, skip
    };

    // Load counters (total_runs, passed, failed, flaky_count, last_change)
    if let Some(SdnValue::Table { rows, .. }) = dict.get("counters") {
        for row in rows {
            let test_id = sdn_row_u32(row, 0);
            let total_runs: usize = sdn_row_u32(row, 1) as usize;
            let passed: usize = sdn_row_u32(row, 2) as usize;
            let failed: usize = sdn_row_u32(row, 3) as usize;
            let flaky_count: u32 = sdn_row_u32(row, 4);
            let last_change_str = sdn_row_string(row, 5);
            let last_change = ChangeType::parse_str(&last_change_str);

            // Find record by name_str_id matching test_id
            for record in db.records.values_mut() {
                if record.name_str_id == Some(test_id) {
                    record.execution_history.total_runs = total_runs;
                    record.execution_history.passed = passed;
                    record.execution_history.failed = failed;
                    record.execution_history.failure_rate_pct = if total_runs > 0 {
                        (failed as f64 / total_runs as f64) * 100.0
                    } else {
                        0.0
                    };
                    record.execution_history.flaky = flaky_count > 0;
                    record.flaky_count = flaky_count;
                    record.last_change = last_change;
                    break;
                }
            }
        }
    }

    // Load timing summaries
    if let Some(SdnValue::Table { rows, .. }) = dict.get("timing") {
        for row in rows {
            let test_id = sdn_row_u32(row, 0);
            let last_ms = sdn_row_f64(row, 1);
            let p50 = sdn_row_f64(row, 2);
            let p90 = sdn_row_f64(row, 3);
            let p95 = sdn_row_f64(row, 4);
            let baseline_median = sdn_row_f64(row, 5);
            db.timing_summaries.insert(
                test_id,
                TimingSummary {
                    test_id,
                    last_ms,
                    p50,
                    p90,
                    p95,
                    baseline_median,
                },
            );
        }
    }

    // Load timing runs
    if let Some(SdnValue::Table { rows, .. }) = dict.get("timing_runs") {
        for row in rows {
            let test_id = sdn_row_u32(row, 0);
            let timestamp = sdn_row_string(row, 1);
            let duration_ms = sdn_row_f64(row, 2);
            let outlier = sdn_row_bool(row, 3);
            let entry = TimingRunEntry {
                test_id,
                timestamp,
                duration_ms,
                outlier,
            };
            db.timing_runs.entry(test_id).or_default().push(entry);
        }
    }

    // Load changes
    if let Some(SdnValue::Table { rows, .. }) = dict.get("changes") {
        for row in rows {
            let test_id = sdn_row_u32(row, 0);
            let change_type_str = sdn_row_string(row, 1);
            let run_id = sdn_row_string(row, 2);
            db.changes.push(ChangeEvent {
                test_id,
                change_type: ChangeType::parse_str(&change_type_str),
                run_id,
            });
        }
    }

    // Populate timing data back into records
    for record in db.records.values_mut() {
        if let Some(name_id) = record.name_str_id {
            if let Some(summary) = db.timing_summaries.get(&name_id) {
                record.timing.last_run_time = summary.last_ms;
                record.timing.p50 = summary.p50;
                record.timing.p90 = summary.p90;
                record.timing.p95 = summary.p95;
                record.timing.baseline_median = summary.baseline_median;
            }
            if let Some(runs) = db.timing_runs.get(&name_id) {
                record.timing.history.runs = runs
                    .iter()
                    .map(|r| TimingRun {
                        timestamp: r.timestamp.clone(),
                        duration_ms: r.duration_ms,
                        outlier: r.outlier,
                    })
                    .collect();
            }
        }
    }

    Ok(())
}

// ============================================================================
// SDN row helpers
// ============================================================================

pub(crate) fn sdn_row_u32(row: &[SdnValue], idx: usize) -> u32 {
    match row.get(idx) {
        Some(SdnValue::Int(n)) => *n as u32,
        Some(SdnValue::String(s)) => s.parse().unwrap_or(0),
        _ => 0,
    }
}

pub(crate) fn sdn_row_f64(row: &[SdnValue], idx: usize) -> f64 {
    match row.get(idx) {
        Some(SdnValue::Float(f)) => *f,
        Some(SdnValue::Int(n)) => *n as f64,
        Some(SdnValue::String(s)) => s.parse().unwrap_or(0.0),
        _ => 0.0,
    }
}

pub(crate) fn sdn_row_string(row: &[SdnValue], idx: usize) -> String {
    match row.get(idx) {
        Some(SdnValue::String(s)) => s.clone(),
        Some(SdnValue::Int(n)) => n.to_string(),
        Some(SdnValue::Float(f)) => f.to_string(),
        _ => String::new(),
    }
}

pub(crate) fn sdn_row_bool(row: &[SdnValue], idx: usize) -> bool {
    match row.get(idx) {
        Some(SdnValue::Bool(b)) => *b,
        Some(SdnValue::String(s)) => s == "true",
        _ => false,
    }
}

/// Parse V2 SDN format (old format with JSON blobs).
fn parse_test_db_sdn_v2(doc: &simple_sdn::SdnDocument) -> Result<TestDb, String> {
    let root = doc.root();
    let tests_table = match root {
        SdnValue::Table { .. } => Some(root),
        SdnValue::Dict(dict) => dict.get("tests"),
        _ => None,
    };

    let mut db = TestDb::new();

    if let Some(SdnValue::Table {
        fields: Some(fields),
        rows,
        ..
    }) = tests_table
    {
        for row in rows {
            if row.len() < fields.len() {
                continue;
            }

            let get_field = |name: &str| -> String {
                fields
                    .iter()
                    .position(|f| f == name)
                    .and_then(|idx| row.get(idx))
                    .map(|v| match v {
                        SdnValue::String(s) => s.clone(),
                        SdnValue::Int(n) => n.to_string(),
                        SdnValue::Float(f) => f.to_string(),
                        SdnValue::Bool(b) => b.to_string(),
                        _ => String::new(),
                    })
                    .unwrap_or_default()
            };

            let test_id = get_field("test_id");
            if test_id.is_empty() {
                continue;
            }

            let status_str = get_field("status");
            let status = match status_str.as_str() {
                "passed" => TestStatus::Passed,
                "failed" => TestStatus::Failed,
                "skipped" => TestStatus::Skipped,
                "ignored" => TestStatus::Ignored,
                "qualifiedignore" | "qualified_ignore" => TestStatus::QualifiedIgnore,
                _ => TestStatus::Passed,
            };

            let failure: Option<TestFailure> = {
                let s = get_field("failure");
                if s.is_empty() {
                    None
                } else {
                    serde_json::from_str(&s).ok()
                }
            };

            let execution_history: ExecutionHistory = {
                let s = get_field("execution_history");
                if s.is_empty() {
                    ExecutionHistory::default()
                } else {
                    serde_json::from_str(&s).unwrap_or_default()
                }
            };

            let timing: TimingData = {
                let s = get_field("timing");
                if s.is_empty() {
                    TimingData::default()
                } else {
                    serde_json::from_str(&s).unwrap_or_default()
                }
            };

            let timing_config: Option<TimingConfig> = {
                let s = get_field("timing_config");
                if s.is_empty() {
                    None
                } else {
                    serde_json::from_str(&s).ok()
                }
            };

            let related_bugs: Vec<String> = get_field("related_bugs")
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            let related_features: Vec<String> = get_field("related_features")
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            let tags: Vec<String> = get_field("tags")
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();

            let qualified_by = {
                let s = get_field("qualified_by");
                if s.is_empty() {
                    None
                } else {
                    Some(s)
                }
            };
            let qualified_at = {
                let s = get_field("qualified_at");
                if s.is_empty() {
                    None
                } else {
                    Some(s)
                }
            };
            let qualified_reason = {
                let s = get_field("qualified_reason");
                if s.is_empty() {
                    None
                } else {
                    Some(s)
                }
            };

            let record = TestRecord {
                test_id: test_id.clone(),
                test_name: get_field("test_name"),
                test_file: get_field("test_file"),
                category: get_field("category"),
                status,
                last_run: get_field("last_run"),
                failure,
                execution_history,
                timing,
                timing_config,
                related_bugs,
                related_features,
                tags,
                description: get_field("description"),
                valid: get_field("valid") == "true",
                qualified_by,
                qualified_at,
                qualified_reason,
                suite_id: None,
                name_str_id: None,
                category_str_id: None,
                status_str_id: None,
                last_change: ChangeType::NoChange,
                flaky_count: 0,
            };

            db.records.insert(test_id, record);
        }
    }

    Ok(db)
}

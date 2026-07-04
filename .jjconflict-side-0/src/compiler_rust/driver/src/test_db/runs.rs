//! Test run management — load, save, start, update, complete, cleanup.

use super::run_record::*;
use super::types::*;
use crate::unified_db::Database;
use std::path::Path;

// ============================================================================
// Helper: runs file path
// ============================================================================

pub(crate) fn runs_file_path(db_path: &Path) -> std::path::PathBuf {
    let parent = db_path.parent().unwrap_or(Path::new("."));
    parent.join("test_db_runs.sdn")
}

// ============================================================================
// Test Run Management Functions
// ============================================================================

pub fn load_test_runs(db_path: &Path) -> Result<Database<TestRunRecord>, String> {
    // V3: load from runs file if it exists, fall back to main db
    let runs_path = runs_file_path(db_path);
    if runs_path.exists() {
        return Database::<TestRunRecord>::load(&runs_path);
    }
    Database::<TestRunRecord>::load(db_path)
}

pub fn save_test_runs(db: &Database<TestRunRecord>) -> Result<(), String> {
    db.save().map_err(|e| e.to_string())
}

pub fn start_test_run(db_path: &Path) -> Result<TestRunRecord, String> {
    let runs_path = runs_file_path(db_path);
    let load_path = if runs_path.exists() { &runs_path } else { db_path };
    let mut db = Database::<TestRunRecord>::load(load_path)?;
    // Ensure we save to runs file going forward
    let run = TestRunRecord::new_running();
    db.insert(run.clone());
    // Save to runs file
    let mut runs_db = Database::<TestRunRecord>::new(&runs_path);
    for (id, rec) in &db.records {
        runs_db.records.insert(id.clone(), rec.clone());
    }
    runs_db.save().map_err(|e| e.to_string())?;
    Ok(run)
}

pub fn update_test_run(db_path: &Path, run: &TestRunRecord) -> Result<(), String> {
    let runs_path = runs_file_path(db_path);
    let load_path = if runs_path.exists() { &runs_path } else { db_path };
    let mut db = Database::<TestRunRecord>::load(load_path)?;
    db.insert(run.clone());
    // Always save to runs file
    let mut runs_db = Database::<TestRunRecord>::new(&runs_path);
    for (id, rec) in &db.records {
        runs_db.records.insert(id.clone(), rec.clone());
    }
    runs_db.save().map_err(|e| e.to_string())
}

pub fn complete_test_run(
    db_path: &Path,
    run_id: &str,
    test_count: usize,
    passed: usize,
    failed: usize,
    crashed: usize,
    timed_out: usize,
) -> Result<(), String> {
    let runs_path = runs_file_path(db_path);
    let load_path = if runs_path.exists() { &runs_path } else { db_path };
    let mut db = Database::<TestRunRecord>::load(load_path)?;
    if let Some(run) = db.get_mut(run_id) {
        run.mark_completed();
        run.test_count = test_count;
        run.passed = passed;
        run.failed = failed;
        run.crashed = crashed;
        run.timed_out = timed_out;
    }
    let mut runs_db = Database::<TestRunRecord>::new(&runs_path);
    for (id, rec) in &db.records {
        runs_db.records.insert(id.clone(), rec.clone());
    }
    runs_db.save().map_err(|e| e.to_string())
}

pub fn mark_run_crashed(db_path: &Path, run_id: &str) -> Result<(), String> {
    let runs_path = runs_file_path(db_path);
    let load_path = if runs_path.exists() { &runs_path } else { db_path };
    let mut db = Database::<TestRunRecord>::load(load_path)?;
    if let Some(run) = db.get_mut(run_id) {
        run.mark_crashed();
    }
    let mut runs_db = Database::<TestRunRecord>::new(&runs_path);
    for (id, rec) in &db.records {
        runs_db.records.insert(id.clone(), rec.clone());
    }
    runs_db.save().map_err(|e| e.to_string())
}

pub fn cleanup_stale_runs(db_path: &Path, max_hours: i64) -> Result<Vec<String>, String> {
    let runs_path = runs_file_path(db_path);
    let load_path = if runs_path.exists() { &runs_path } else { db_path };
    let mut db = Database::<TestRunRecord>::load(load_path)?;
    let mut cleaned = Vec::new();

    let stale_ids: Vec<String> = db
        .records
        .values()
        .filter(|r| r.status == TestRunStatus::Running)
        .filter(|r| r.is_stale(max_hours) || !r.is_process_alive())
        .map(|r| r.run_id.clone())
        .collect();

    for run_id in stale_ids {
        if let Some(run) = db.get_mut(&run_id) {
            run.mark_crashed();
            cleaned.push(run_id);
        }
    }

    if !cleaned.is_empty() {
        let mut runs_db = Database::<TestRunRecord>::new(&runs_path);
        for (id, rec) in &db.records {
            runs_db.records.insert(id.clone(), rec.clone());
        }
        runs_db.save().map_err(|e| e.to_string())?;
    }

    Ok(cleaned)
}

pub fn prune_old_runs(db_path: &Path, keep_count: usize) -> Result<usize, String> {
    let runs_path = runs_file_path(db_path);
    let load_path = if runs_path.exists() { &runs_path } else { db_path };
    let mut db = Database::<TestRunRecord>::load(load_path)?;

    let mut runs: Vec<_> = db.records.values().cloned().collect();
    runs.sort_by(|a, b| b.start_time.cmp(&a.start_time));

    let to_delete: Vec<String> = runs.iter().skip(keep_count).map(|r| r.run_id.clone()).collect();

    let deleted_count = to_delete.len();
    for run_id in to_delete {
        db.delete(&run_id);
    }

    if deleted_count > 0 {
        let mut runs_db = Database::<TestRunRecord>::new(&runs_path);
        for (id, rec) in &db.records {
            runs_db.records.insert(id.clone(), rec.clone());
        }
        runs_db.save().map_err(|e| e.to_string())?;
    }

    Ok(deleted_count)
}

pub fn list_runs(db_path: &Path, status_filter: Option<TestRunStatus>) -> Result<Vec<TestRunRecord>, String> {
    let runs_path = runs_file_path(db_path);
    let load_path = if runs_path.exists() { &runs_path } else { db_path };
    let db = Database::<TestRunRecord>::load(load_path)?;
    let mut runs: Vec<_> = db
        .records
        .values()
        .filter(|r| status_filter.is_none() || Some(r.status) == status_filter)
        .cloned()
        .collect();

    runs.sort_by(|a, b| b.start_time.cmp(&a.start_time));
    Ok(runs)
}

pub fn get_running_runs(db_path: &Path) -> Result<Vec<TestRunRecord>, String> {
    list_runs(db_path, Some(TestRunStatus::Running))
}

//! TODO database backed by SDN.
//!
//! This module manages TODOs extracted from source code, storing them in an SDN database
//! and generating documentation. It integrates with the `todo_parser` module to automatically
//! scan and update TODOs from both Rust and Simple source files.

use crate::todo_parser::{ParseError, TodoItem, TodoParser};
use indexmap::IndexMap;
use rayon::prelude::*;
use sha2::{Digest, Sha256};
use simple_sdn::{parse_document, SdnDocument, SdnValue};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use walkdir::WalkDir;

/// A record in the TODO database
#[derive(Debug, Clone)]
pub struct TodoRecord {
    pub id: String,
    pub keyword: String,
    pub area: String,
    pub priority: String,
    pub description: String,
    pub file: String,
    pub line: usize,
    pub issue: Option<String>,
    pub blocked: Vec<String>,
    pub status: String,
    pub valid: bool,
}

/// File hash cache entry for incremental scanning
#[derive(Debug, Clone)]
pub struct FileCache {
    pub hash: String,
    pub todo_ids: Vec<String>,
}

/// TODO database
#[derive(Debug, Default)]
pub struct TodoDb {
    pub records: BTreeMap<String, TodoRecord>,
    pub file_cache: BTreeMap<String, FileCache>,
    next_id: usize,
}

impl TodoDb {
    pub fn new() -> Self {
        Self::default()
    }

    /// Get the next available ID
    fn next_id(&mut self) -> String {
        let id = self.next_id;
        self.next_id += 1;
        id.to_string()
    }

    /// Insert a record into the database
    pub fn insert(&mut self, record: TodoRecord) {
        self.records.insert(record.id.clone(), record);
    }

    /// Get a record by ID
    pub fn get(&self, id: &str) -> Option<&TodoRecord> {
        self.records.get(id)
    }

    /// Get all valid records
    pub fn valid_records(&self) -> Vec<&TodoRecord> {
        self.records.values().filter(|r| r.valid).collect()
    }

    /// Count by status
    pub fn count_by_status(&self, status: &str) -> usize {
        self.records.values().filter(|r| r.valid && r.status == status).count()
    }

    /// Count by priority
    pub fn count_by_priority(&self, priority: &str) -> usize {
        self.records
            .values()
            .filter(|r| r.valid && r.priority == priority)
            .count()
    }
}

/// Load TODO database from SDN file
pub fn load_todo_db(path: &Path) -> Result<TodoDb, String> {
    eprintln!("DEBUG: load_todo_db called for path: {}", path.display());
    if !path.exists() {
        eprintln!("DEBUG: Database file does not exist, creating new");
        return Ok(TodoDb::new());
    }

    let content = fs::read_to_string(path).map_err(|e| e.to_string())?;
    eprintln!("DEBUG: Loaded {} bytes from file", content.len());
    eprintln!("DEBUG: First 100 chars: {}", &content.chars().take(100).collect::<String>());
    let doc = parse_document(&content).map_err(|e| {
        eprintln!("DEBUG: parse_document failed: {}", e);
        e.to_string()
    })?;
    eprintln!("DEBUG: parse_document succeeded");
    parse_todo_db(&doc, path)
}

fn parse_todo_db(doc: &SdnDocument, path: &Path) -> Result<TodoDb, String> {
    let root = doc.root();
    eprintln!("DEBUG: parse_todo_db called, root type: {:?}", std::mem::discriminant(root));

    // Try to get todos table - might be root itself or in a Dict
    let (todos_table, file_cache_table) = match root {
        SdnValue::Table { .. } => {
            eprintln!("DEBUG: Root is a Table (single table document)");
            (Some(root), None)
        }
        SdnValue::Dict(dict) => {
            eprintln!("DEBUG: Root is Dict with {} keys", dict.len());
            (dict.get("todos"), dict.get("file_cache"))
        }
        _ => {
            eprintln!("DEBUG: Root is neither Table nor Dict");
            (None, None)
        }
    };

    let mut db = TodoDb::new();

    // Parse todos table
    let table = match todos_table {
        Some(SdnValue::Table { fields, rows, .. }) => (fields, rows),
        None => return Ok(db),
        _ => return Err("todos must be a table".to_string()),
    };

    let fields = table
        .0
        .as_ref()
        .ok_or_else(|| "todos table missing fields".to_string())?;

    // Find max ID to set next_id
    let mut max_id = 0;

    for row in table.1 {
        let mut row_map = BTreeMap::new();
        for (idx, field) in fields.iter().enumerate() {
            if let Some(value) = row.get(idx) {
                row_map.insert(field.clone(), sdn_value_to_string(value));
            }
        }

        let id = row_map.get("id").cloned().unwrap_or_default();
        if id.is_empty() {
            continue;
        }

        // Track max ID
        if let Ok(id_num) = id.parse::<usize>() {
            max_id = max_id.max(id_num);
        }

        // Parse blocked issues
        let blocked = row_map
            .get("blocked")
            .map(|s| {
                s.split(',')
                    .map(|x| x.trim().to_string())
                    .filter(|x| !x.is_empty())
                    .collect()
            })
            .unwrap_or_default();

        let record = TodoRecord {
            id: id.clone(),
            keyword: row_map.get("keyword").cloned().unwrap_or_else(|| "TODO".to_string()),
            area: row_map.get("area").cloned().unwrap_or_default(),
            priority: row_map.get("priority").cloned().unwrap_or_else(|| "P2".to_string()),
            description: row_map.get("description").cloned().unwrap_or_default(),
            file: row_map.get("file").cloned().unwrap_or_default(),
            line: row_map.get("line").and_then(|s| s.parse().ok()).unwrap_or(0),
            issue: row_map.get("issue").cloned().filter(|s| !s.is_empty()),
            blocked,
            status: row_map.get("status").cloned().unwrap_or_else(|| "open".to_string()),
            valid: parse_bool_field(row_map.get("valid")).unwrap_or(true),
        };
        db.records.insert(id, record);
    }

    db.next_id = max_id + 1;

    // Load file cache from separate file
    let cache_path = path.with_extension("cache.sdn");
    if cache_path.exists() {
        eprintln!("DEBUG: Loading file cache from {}", cache_path.display());
        if let Ok(cache_content) = fs::read_to_string(&cache_path) {
            if let Ok(cache_doc) = parse_document(&cache_content) {
                let cache_root = cache_doc.root();
                if let SdnValue::Table { fields: Some(fields), rows, .. } = cache_root {
                    eprintln!("DEBUG: Found file_cache table with {} rows", rows.len());
                    for row in rows {
                        let mut row_map = BTreeMap::new();
                        for (idx, field) in fields.iter().enumerate() {
                            if let Some(value) = row.get(idx) {
                                row_map.insert(field.clone(), sdn_value_to_string(value));
                            }
                        }

                        let path_str = row_map.get("path").cloned().unwrap_or_default();
                        if path_str.is_empty() {
                            continue;
                        }

                        let hash = row_map.get("hash").cloned().unwrap_or_default();
                        let todo_ids: Vec<String> = row_map
                            .get("todo_ids")
                            .map(|s| {
                                s.split(';')
                                    .map(|x| x.trim().to_string())
                                    .filter(|x| !x.is_empty())
                                    .collect()
                            })
                            .unwrap_or_default();

                        db.file_cache.insert(path_str, FileCache { hash, todo_ids });
                    }
                }
            }
        }
    } else {
        eprintln!("DEBUG: No file cache found at {}", cache_path.display());
    }

    Ok(db)
}

/// Save TODO database to SDN file
pub fn save_todo_db(path: &Path, db: &TodoDb) -> Result<(), std::io::Error> {
    let fields = vec![
        "id".to_string(),
        "keyword".to_string(),
        "area".to_string(),
        "priority".to_string(),
        "description".to_string(),
        "file".to_string(),
        "line".to_string(),
        "issue".to_string(),
        "blocked".to_string(),
        "status".to_string(),
        "valid".to_string(),
    ];

    let mut rows = Vec::new();
    let mut sorted_records: Vec<_> = db.records.values().collect();
    sorted_records.sort_by_key(|r| r.id.parse::<usize>().unwrap_or(0));

    for record in sorted_records {
        let row = vec![
            SdnValue::String(record.id.clone()),
            SdnValue::String(record.keyword.clone()),
            SdnValue::String(record.area.clone()),
            SdnValue::String(record.priority.clone()),
            SdnValue::String(record.description.clone()),
            SdnValue::String(record.file.clone()),
            SdnValue::int(record.line as i64),
            SdnValue::String(record.issue.clone().unwrap_or_default()),
            SdnValue::String(record.blocked.join(",")),
            SdnValue::String(record.status.clone()),
            SdnValue::Bool(record.valid),
        ];
        rows.push(row);
    }

    let table = SdnValue::named_table(fields.clone(), rows);

    // Create SDN content manually with two tables (not wrapped in Dict)
    // The parser will handle this as a multi-table document
    let mut content = String::new();
    content.push_str("todos |");
    content.push_str(&fields.join(", "));
    content.push_str("|\n");

    // Add each row
    let table_rows = match &table {
        SdnValue::Table { rows, .. } => rows,
        _ => unreachable!(),
    };

    for row in table_rows {
        content.push_str("    ");
        for (i, value) in row.iter().enumerate() {
            if i > 0 {
                content.push_str(", ");
            }
            match value {
                SdnValue::String(s) => {
                    // Quote strings that contain special characters or are empty
                    if s.is_empty() || s.contains(',') || s.contains('"') || s.contains('\n') || s.contains(' ') {
                        content.push_str(&format!("\"{}\"", s.replace("\"", "\\\"")));
                    } else {
                        content.push_str(s);
                    }
                }
                SdnValue::Int(n) => content.push_str(&n.to_string()),
                SdnValue::Float(f) => content.push_str(&f.to_string()),
                SdnValue::Bool(b) => content.push_str(&b.to_string()),
                _ => content.push_str(&format!("{}", value)),
            }
        }
        content.push('\n');
    }

    // Save main todo database
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(path, content)?;

    // Save file cache separately to avoid SDN multi-table parsing issues
    let cache_path = path.with_extension("cache.sdn");
    let mut cache_content = String::new();
    cache_content.push_str("file_cache |path, hash, todo_ids|\n");
    for (path_str, cache) in &db.file_cache {
        cache_content.push_str("    ");
        // Escape path if needed
        if path_str.contains(',') || path_str.contains('"') || path_str.contains(' ') {
            cache_content.push_str(&format!("\"{}\"", path_str.replace("\"", "\\\"")));
        } else {
            cache_content.push_str(path_str);
        }
        cache_content.push_str(", ");
        cache_content.push_str(&cache.hash);
        cache_content.push_str(", ");
        // Join todo_ids with semicolons
        cache_content.push_str(&format!("\"{}\"", cache.todo_ids.join(";")));
        cache_content.push('\n');
    }
    fs::write(cache_path, cache_content)?;

    Ok(())
}

/// Compute SHA256 hash of file contents
fn compute_file_hash(path: &Path) -> Result<String, std::io::Error> {
    let content = fs::read(path)?;
    let mut hasher = Sha256::new();
    hasher.update(&content);
    let result = hasher.finalize();
    Ok(format!("{:x}", result))
}

/// Update TODO database from source code scan (legacy non-parallel version)
pub fn update_todo_db_from_scan(db: &mut TodoDb, scan_root: &Path) -> Result<(usize, usize, usize), String> {
    update_todo_db_incremental_parallel(db, scan_root, false, false)
}

/// Update TODO database with incremental and/or parallel scanning
pub fn update_todo_db_incremental_parallel(
    db: &mut TodoDb,
    scan_root: &Path,
    incremental: bool,
    parallel: bool,
) -> Result<(usize, usize, usize), String> {
    let parser = TodoParser::new();

    // Collect all files to scan
    let mut files_to_scan = Vec::new();
    let mut skipped = 0;

    eprintln!("DEBUG: File cache has {} entries", db.file_cache.len());
    if incremental && db.file_cache.len() > 0 {
        eprintln!("DEBUG: First cache entry: {:?}", db.file_cache.iter().next());
    }

    // Walk directory and collect files
    WalkDir::new(scan_root)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file())
        .for_each(|entry| {
            let path = entry.path();

            // Only scan .rs, .spl, and .md files
            if let Some(ext) = path.extension() {
                if ext == "rs" || ext == "spl" || ext == "md" {
                    let path_str = path.display().to_string();

                    // Incremental: check if file changed
                    if incremental {
                        if let Ok(hash) = compute_file_hash(path) {
                            if let Some(cache) = db.file_cache.get(&path_str) {
                                if cache.hash == hash {
                                    // File unchanged, skip
                                    skipped += 1;
                                    eprintln!("DEBUG: Skipping unchanged file: {}", path_str);
                                    return;
                                }
                            }
                        }
                    }

                    files_to_scan.push(path.to_path_buf());
                }
            }
        });

    // Parse files (parallel or sequential)
    let scanned_todos: Vec<TodoItem> = if parallel {
        // Parallel scanning with rayon
        files_to_scan
            .par_iter()
            .filter_map(|path| parser.parse_file(path).ok().map(|result| result.todos))
            .flatten()
            .collect()
    } else {
        // Sequential scanning
        files_to_scan
            .iter()
            .filter_map(|path| parser.parse_file(path).ok().map(|result| result.todos))
            .flatten()
            .collect()
    };

    // Update file cache if incremental mode enabled
    if incremental {
        for path in &files_to_scan {
            if let Ok(hash) = compute_file_hash(path) {
                let path_str = path.display().to_string();
                let todo_ids: Vec<String> = scanned_todos
                    .iter()
                    .filter(|t| t.file == *path)
                    .map(|_| String::new()) // Will be filled after adding to DB
                    .collect();

                db.file_cache.insert(path_str, FileCache { hash, todo_ids });
            }
        }
    }

    // Create a map of file:line -> TodoItem for quick lookup
    let mut scanned_todos_map: BTreeMap<String, TodoItem> = BTreeMap::new();
    for todo in scanned_todos {
        let key = format!("{}:{}", todo.file.display(), todo.line);
        scanned_todos_map.insert(key, todo);
    }

    // Mark existing records as invalid (we'll re-validate them)
    for record in db.records.values_mut() {
        record.valid = false;
    }

    // Process scanned TODOs
    let mut added = 0;
    let mut updated = 0;

    for (_key, todo) in scanned_todos_map {
        let file = todo.file.display().to_string();
        let line = todo.line;

        // Check if this TODO already exists in database
        let existing = db.records.values_mut().find(|r| r.file == file && r.line == line);

        // Get normalized priority before moving any fields
        let normalized_priority = todo.normalized_priority();

        if let Some(existing_record) = existing {
            // Update existing record
            existing_record.keyword = todo.keyword;
            existing_record.area = todo.area;
            existing_record.priority = normalized_priority;
            existing_record.description = todo.description;
            existing_record.issue = todo.issue;
            existing_record.blocked = todo.blocked;
            existing_record.valid = true;
            updated += 1;
        } else {
            // Add new record
            let normalized_priority = todo.normalized_priority();
            let record = TodoRecord {
                id: db.next_id(),
                keyword: todo.keyword,
                area: todo.area,
                priority: normalized_priority,
                description: todo.description,
                file,
                line,
                issue: todo.issue,
                blocked: todo.blocked,
                status: "open".to_string(),
                valid: true,
            };
            db.insert(record);
            added += 1;
        }
    }

    let removed = db.records.values().filter(|r| !r.valid).count();

    Ok((added, updated, removed))
}

/// Legacy update function (kept for compatibility)
fn update_todo_db_from_scan_legacy(db: &mut TodoDb, scan_root: &Path) -> Result<(usize, usize, usize), String> {
    let parser = TodoParser::new();
    let result = parser.scan_directory(scan_root)?;

    // Create a map of file:line -> TodoItem for quick lookup
    let mut scanned_todos: BTreeMap<String, TodoItem> = BTreeMap::new();
    for todo in result.todos {
        let key = format!("{}:{}", todo.file.display(), todo.line);
        scanned_todos.insert(key, todo);
    }

    // Mark existing records as invalid (we'll re-validate them)
    for record in db.records.values_mut() {
        record.valid = false;
    }

    // Process scanned TODOs
    let mut added = 0;
    let mut updated = 0;

    for (key, todo) in scanned_todos {
        let file = todo.file.display().to_string();
        let line = todo.line;

        // Check if this TODO already exists in database
        let existing = db.records.values_mut().find(|r| r.file == file && r.line == line);

        // Get normalized priority before moving any fields
        let normalized_priority = todo.normalized_priority();

        if let Some(existing_record) = existing {
            // Update existing record
            existing_record.keyword = todo.keyword;
            existing_record.area = todo.area;
            existing_record.priority = normalized_priority;
            existing_record.description = todo.description;
            existing_record.issue = todo.issue;
            existing_record.blocked = todo.blocked;
            existing_record.valid = true;
            updated += 1;
        } else {
            // Add new record
            let record = TodoRecord {
                id: db.next_id(),
                keyword: todo.keyword,
                area: todo.area,
                priority: normalized_priority,
                description: todo.description,
                file,
                line,
                issue: todo.issue,
                blocked: todo.blocked,
                status: "open".to_string(),
                valid: true,
            };
            db.insert(record);
            added += 1;
        }
    }

    let removed = db.records.values().filter(|r| !r.valid).count();

    Ok((added, updated, removed))
}

/// Generate TODO documentation
pub fn generate_todo_docs(db: &TodoDb, output_dir: &Path) -> Result<(), String> {
    let records: Vec<&TodoRecord> = db.valid_records();

    let mut md = String::new();
    md.push_str("# TODO List\n\n");

    // Header with statistics
    let total = records.len();
    let open = db.count_by_status("open");
    let blocked = db.count_by_status("blocked");
    let stale = db.count_by_status("stale");

    md.push_str(&format!("**Generated:** {}\n", chrono::Local::now().format("%Y-%m-%d")));
    md.push_str(&format!(
        "**Total:** {} items | **Open:** {} | **Blocked:** {} | **Stale:** {}\n",
        total, open, blocked, stale
    ));
    md.push_str("**Database:** `doc/todo/todo_db.sdn`\n\n");

    // Statistics by area
    md.push_str("## Statistics\n\n");
    md.push_str("### By Area\n\n");
    md.push_str("| Area | Count | P0 | P1 | P2 | P3 | Blocked |\n");
    md.push_str("|------|-------|----|----|----|----|---------|");

    let mut area_stats: BTreeMap<String, AreaStats> = BTreeMap::new();
    for record in &records {
        let stats = area_stats.entry(record.area.clone()).or_default();
        stats.total += 1;
        match record.priority.as_str() {
            "P0" => stats.p0 += 1,
            "P1" => stats.p1 += 1,
            "P2" => stats.p2 += 1,
            "P3" => stats.p3 += 1,
            _ => {}
        }
        if record.status == "blocked" {
            stats.blocked += 1;
        }
    }

    for (area, stats) in &area_stats {
        md.push_str(&format!(
            "\n| {} | {} | {} | {} | {} | {} | {} |",
            area, stats.total, stats.p0, stats.p1, stats.p2, stats.p3, stats.blocked
        ));
    }

    // Statistics by priority
    md.push_str("\n\n### By Priority\n\n");
    md.push_str("| Priority | Count | Open | Blocked | Stale |\n");
    md.push_str("|----------|-------|------|---------|-------|\n");

    for priority in &["P0", "P1", "P2", "P3"] {
        let count = db.count_by_priority(priority);
        let priority_open = records
            .iter()
            .filter(|r| r.priority == *priority && r.status == "open")
            .count();
        let priority_blocked = records
            .iter()
            .filter(|r| r.priority == *priority && r.status == "blocked")
            .count();
        let priority_stale = records
            .iter()
            .filter(|r| r.priority == *priority && r.status == "stale")
            .count();

        let label = match *priority {
            "P0" => "P0 (critical)",
            "P1" => "P1 (high)",
            "P2" => "P2 (medium)",
            "P3" => "P3 (low)",
            _ => priority,
        };

        md.push_str(&format!(
            "| {} | {} | {} | {} | {} |\n",
            label, count, priority_open, priority_blocked, priority_stale
        ));
    }

    // P0 Critical TODOs
    let p0_todos: Vec<_> = records.iter().filter(|r| r.priority == "P0").collect();
    if !p0_todos.is_empty() {
        md.push_str("\n## P0 Critical TODOs\n\n");
        generate_todo_section(&mut md, &p0_todos);
    }

    // P1 High Priority TODOs
    let p1_todos: Vec<_> = records.iter().filter(|r| r.priority == "P1").collect();
    if !p1_todos.is_empty() {
        md.push_str("\n## P1 High Priority TODOs\n\n");
        generate_todo_section(&mut md, &p1_todos);
    }

    // P2 Medium Priority TODOs (summary only if many)
    let p2_todos: Vec<_> = records.iter().filter(|r| r.priority == "P2").collect();
    if !p2_todos.is_empty() {
        md.push_str(&format!("\n## P2 Medium Priority TODOs ({})\n\n", p2_todos.len()));
        if p2_todos.len() <= 20 {
            generate_todo_section(&mut md, &p2_todos);
        } else {
            md.push_str("*Too many to list individually. See database for details.*\n\n");
            // Group by area
            let mut p2_by_area: BTreeMap<String, Vec<&TodoRecord>> = BTreeMap::new();
            for todo in p2_todos {
                p2_by_area.entry(todo.area.clone()).or_default().push(todo);
            }
            for (area, todos) in p2_by_area {
                md.push_str(&format!("- **{}:** {} TODOs\n", area, todos.len()));
            }
        }
    }

    // P3 Low Priority TODOs (summary only)
    let p3_todos: Vec<_> = records.iter().filter(|r| r.priority == "P3").collect();
    if !p3_todos.is_empty() {
        md.push_str(&format!("\n## P3 Low Priority TODOs ({})\n\n", p3_todos.len()));
        md.push_str("*See database for details.*\n");
    }

    // Stale TODOs
    let stale_todos: Vec<_> = records.iter().filter(|r| r.status == "stale").collect();
    if !stale_todos.is_empty() {
        md.push_str("\n## Stale TODOs\n\n");
        md.push_str("These TODOs may have moved or been modified:\n\n");
        for todo in stale_todos {
            md.push_str(&format!(
                "- **#{}** [{}][{}] {}\n",
                todo.id, todo.area, todo.priority, todo.description
            ));
            md.push_str(&format!("  - File: `{}:{}`\n", todo.file, todo.line));
        }
    }

    // Appendix
    md.push_str("\n## Appendix\n\n");
    md.push_str("### Legend\n\n");
    md.push_str("- **P0/critical:** Blocking, fix immediately\n");
    md.push_str("- **P1/high:** Important, next sprint\n");
    md.push_str("- **P2/medium:** Should do, backlog\n");
    md.push_str("- **P3/low:** Nice to have, someday\n\n");

    md.push_str("### Areas\n\n");
    md.push_str("- `runtime` - GC, values, monoio, concurrency\n");
    md.push_str("- `codegen` - MIR, Cranelift, LLVM, Vulkan\n");
    md.push_str("- `compiler` - HIR, pipeline, interpreter\n");
    md.push_str("- `parser` - Lexer, AST, parsing\n");
    md.push_str("- `type` - Type checker, inference\n");
    md.push_str("- `stdlib` - Simple standard library\n");
    md.push_str("- `gpu` - GPU/SIMD/graphics\n");
    md.push_str("- `ui` - UI framework\n");
    md.push_str("- `test` - Test frameworks\n");
    md.push_str("- `driver` - CLI, tools\n");
    md.push_str("- `loader` - SMF loader\n");
    md.push_str("- `pkg` - Package manager\n");
    md.push_str("- `doc` - Documentation, specs, guides\n");

    let path = output_dir.join("TODO.md");
    fs::create_dir_all(output_dir).map_err(|e| e.to_string())?;
    fs::write(&path, md).map_err(|e| e.to_string())?;

    Ok(())
}

fn generate_todo_section(md: &mut String, todos: &[&&TodoRecord]) {
    let mut by_area: BTreeMap<String, Vec<&TodoRecord>> = BTreeMap::new();
    for todo in todos {
        by_area.entry(todo.area.clone()).or_default().push(todo);
    }

    for (area, area_todos) in by_area {
        md.push_str(&format!("### {}\n\n", area));
        for todo in area_todos {
            md.push_str(&format!(
                "- **#{}** [{}][{}] {}",
                todo.id, todo.area, todo.priority, todo.description
            ));
            if let Some(ref issue) = todo.issue {
                md.push_str(&format!(" [#{}]", issue));
            }
            if !todo.blocked.is_empty() {
                md.push_str(&format!(" [blocked:{}]", todo.blocked.join(",")));
            }
            md.push_str("\n");
            md.push_str(&format!("  - File: `{}:{}`\n", todo.file, todo.line));
            md.push_str(&format!("  - Status: {}\n", todo.status));
            if !todo.blocked.is_empty() {
                md.push_str(&format!("  - Blocked by: {}\n", todo.blocked.join(", ")));
            }
            md.push_str("\n");
        }
    }
}

#[derive(Default)]
struct AreaStats {
    total: usize,
    p0: usize,
    p1: usize,
    p2: usize,
    p3: usize,
    blocked: usize,
}

fn sdn_value_to_string(value: &SdnValue) -> String {
    match value {
        SdnValue::String(s) => s.clone(),
        SdnValue::Int(n) => n.to_string(),
        SdnValue::Float(f) => f.to_string(),
        SdnValue::Bool(b) => b.to_string(),
        SdnValue::Null => String::new(),
        _ => format!("{:?}", value),
    }
}

fn parse_bool_field(value: Option<&String>) -> Option<bool> {
    value.and_then(|s| match s.to_lowercase().as_str() {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_empty_db() {
        let db = TodoDb::new();
        assert_eq!(db.records.len(), 0);
        assert_eq!(db.next_id, 0);
    }

    #[test]
    fn test_insert_record() {
        let mut db = TodoDb::new();
        let record = TodoRecord {
            id: "1".to_string(),
            keyword: "TODO".to_string(),
            area: "runtime".to_string(),
            priority: "P0".to_string(),
            description: "Test TODO".to_string(),
            file: "test.rs".to_string(),
            line: 42,
            issue: Some("123".to_string()),
            blocked: vec![],
            status: "open".to_string(),
            valid: true,
        };

        db.insert(record);
        assert_eq!(db.records.len(), 1);
        assert!(db.get("1").is_some());
    }

    #[test]
    fn test_count_by_status() {
        let mut db = TodoDb::new();
        db.insert(TodoRecord {
            id: "1".to_string(),
            keyword: "TODO".to_string(),
            area: "runtime".to_string(),
            priority: "P0".to_string(),
            description: "Open TODO".to_string(),
            file: "test.rs".to_string(),
            line: 1,
            issue: None,
            blocked: vec![],
            status: "open".to_string(),
            valid: true,
        });
        db.insert(TodoRecord {
            id: "2".to_string(),
            keyword: "TODO".to_string(),
            area: "runtime".to_string(),
            priority: "P1".to_string(),
            description: "Blocked TODO".to_string(),
            file: "test.rs".to_string(),
            line: 2,
            issue: None,
            blocked: vec!["1".to_string()],
            status: "blocked".to_string(),
            valid: true,
        });

        assert_eq!(db.count_by_status("open"), 1);
        assert_eq!(db.count_by_status("blocked"), 1);
    }

    #[test]
    fn test_count_by_priority() {
        let mut db = TodoDb::new();
        db.insert(TodoRecord {
            id: "1".to_string(),
            keyword: "TODO".to_string(),
            area: "runtime".to_string(),
            priority: "P0".to_string(),
            description: "Critical".to_string(),
            file: "test.rs".to_string(),
            line: 1,
            issue: None,
            blocked: vec![],
            status: "open".to_string(),
            valid: true,
        });
        db.insert(TodoRecord {
            id: "2".to_string(),
            keyword: "TODO".to_string(),
            area: "runtime".to_string(),
            priority: "P1".to_string(),
            description: "High".to_string(),
            file: "test.rs".to_string(),
            line: 2,
            issue: None,
            blocked: vec![],
            status: "open".to_string(),
            valid: true,
        });

        assert_eq!(db.count_by_priority("P0"), 1);
        assert_eq!(db.count_by_priority("P1"), 1);
        assert_eq!(db.count_by_priority("P2"), 0);
    }
}

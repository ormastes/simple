//! Task database backed by SDN.
//!
//! Similar to feature_db but for non-feature tasks like refactoring,
//! maintenance, and documentation work.

use indexmap::IndexMap;
use simple_sdn::{parse_document, SdnDocument, SdnValue};
use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

#[derive(Debug, Clone)]
pub struct TaskRecord {
    pub id: String,
    pub category: String,
    pub name: String,
    pub description: String,
    pub priority: String,
    pub status: String,
    pub valid: bool,
}

#[derive(Debug, Default)]
pub struct TaskDb {
    pub records: BTreeMap<String, TaskRecord>,
}

impl TaskDb {
    pub fn new() -> Self {
        Self::default()
    }
}

pub fn load_task_db(path: &Path) -> Result<TaskDb, String> {
    let content = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let doc = parse_document(&content).map_err(|e| e.to_string())?;
    parse_task_db(&doc)
}

fn parse_task_db(doc: &SdnDocument) -> Result<TaskDb, String> {
    let root = doc.root();
    let tasks = match root {
        SdnValue::Dict(dict) => dict.get("tasks"),
        _ => None,
    };

    let mut db = TaskDb::new();
    let table = match tasks {
        Some(SdnValue::Table { fields, rows, .. }) => (fields, rows),
        None => return Ok(db),
        _ => return Err("tasks must be a table".to_string()),
    };

    let fields = table
        .0
        .as_ref()
        .ok_or_else(|| "tasks table missing fields".to_string())?;
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
        let record = TaskRecord {
            id: id.clone(),
            category: row_map.get("category").cloned().unwrap_or_default(),
            name: row_map.get("name").cloned().unwrap_or_default(),
            description: row_map.get("description").cloned().unwrap_or_default(),
            priority: row_map
                .get("priority")
                .cloned()
                .unwrap_or_else(|| "medium".to_string()),
            status: row_map
                .get("status")
                .cloned()
                .unwrap_or_else(|| "planned".to_string()),
            valid: parse_bool_field(row_map.get("valid")).unwrap_or(true),
        };
        db.records.insert(id, record);
    }

    Ok(db)
}

pub fn save_task_db(path: &Path, db: &TaskDb) -> Result<(), std::io::Error> {
    let fields = vec![
        "id".to_string(),
        "category".to_string(),
        "name".to_string(),
        "description".to_string(),
        "priority".to_string(),
        "status".to_string(),
        "valid".to_string(),
    ];

    let mut rows = Vec::new();
    for record in db.records.values() {
        let row = vec![
            SdnValue::String(record.id.clone()),
            SdnValue::String(record.category.clone()),
            SdnValue::String(record.name.clone()),
            SdnValue::String(record.description.clone()),
            SdnValue::String(record.priority.clone()),
            SdnValue::String(record.status.clone()),
            SdnValue::Bool(record.valid),
        ];
        rows.push(row);
    }

    let table = SdnValue::Table {
        fields: Some(fields),
        types: None,
        rows,
    };

    let mut dict = IndexMap::new();
    dict.insert("tasks".to_string(), table);

    let mut doc = SdnDocument::parse("tasks |id|")
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e.to_string()))?;
    *doc.root_mut() = SdnValue::Dict(dict);

    let content = doc.to_sdn();
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    fs::write(path, content)?;
    Ok(())
}

pub fn generate_task_docs(db: &TaskDb, output_dir: &Path) -> Result<(), String> {
    let mut records: Vec<&TaskRecord> = db.records.values().filter(|r| r.valid).collect();
    records.sort_by(|a, b| a.id.cmp(&b.id));

    let last_id = db
        .records
        .values()
        .map(|r| &r.id)
        .max()
        .cloned()
        .unwrap_or_default();

    // Count by category
    let mut categories: BTreeMap<String, CategoryCounts> = BTreeMap::new();
    for record in &records {
        let category = if record.category.is_empty() {
            "Uncategorized".to_string()
        } else {
            record.category.clone()
        };
        categories.entry(category).or_default().add(record);
    }

    // Count by priority
    let mut priorities: BTreeMap<String, usize> = BTreeMap::new();
    for record in &records {
        *priorities.entry(record.priority.clone()).or_default() += 1;
    }

    // Generate task.md
    let mut md = String::new();
    md.push_str("# Task Categories\n\n");
    if !last_id.is_empty() {
        md.push_str(&format!("Last ID: `{}`\n\n", last_id));
    }

    md.push_str("| Category | Tasks | Complete | Planned | In Progress |\n");
    md.push_str("|----------|-------|----------|---------|-------------|\n");
    for (category, counts) in &categories {
        md.push_str(&format!(
            "| {} | {} | {} | {} | {} |\n",
            category, counts.total, counts.complete, counts.planned, counts.in_progress
        ));
    }

    md.push_str("\n## By Priority\n\n");
    md.push_str("| Priority | Count |\n");
    md.push_str("|----------|-------|\n");
    for priority in &["high", "medium", "low"] {
        let count = priorities.get(*priority).copied().unwrap_or(0);
        if count > 0 {
            md.push_str(&format!("| {} | {} |\n", priority, count));
        }
    }

    md.push_str("\n## Recent Tasks\n\n");
    md.push_str("| ID | Name | Status |\n");
    md.push_str("|----|------|--------|\n");
    for record in records.iter().rev().take(10) {
        md.push_str(&format!(
            "| {} | {} | {} |\n",
            record.id, record.name, record.status
        ));
    }

    let path = output_dir.join("task.md");
    fs::create_dir_all(output_dir).map_err(|e| e.to_string())?;
    fs::write(&path, md).map_err(|e| e.to_string())?;

    Ok(())
}

#[derive(Default)]
struct CategoryCounts {
    total: usize,
    complete: usize,
    planned: usize,
    in_progress: usize,
}

impl CategoryCounts {
    fn add(&mut self, record: &TaskRecord) {
        self.total += 1;
        match record.status.as_str() {
            "complete" => self.complete += 1,
            "planned" => self.planned += 1,
            "in_progress" => self.in_progress += 1,
            _ => {}
        }
    }
}

fn sdn_value_to_string(value: &SdnValue) -> String {
    match value {
        SdnValue::Null => "".to_string(),
        SdnValue::Bool(b) => b.to_string(),
        SdnValue::Int(i) => i.to_string(),
        SdnValue::Float(f) => f.to_string(),
        SdnValue::String(s) => s.clone(),
        other => other.to_string(),
    }
}

fn parse_bool_field(value: Option<&String>) -> Option<bool> {
    value.map(|v| v == "true")
}

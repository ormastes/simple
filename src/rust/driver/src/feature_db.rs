//! Feature database backed by SDN.

use crate::db_lock::FileLock;
use crate::unified_db::Record;
use indexmap::IndexMap;
use simple_sdn::{parse_document, SdnDocument, SdnValue};
use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

const DEFAULT_RUN_MODES: [&str; 4] = ["interpreter", "jit", "smf_cranelift", "smf_llvm"];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SupportStatus {
    Supported,
    NotSupported,
}

impl SupportStatus {
    fn as_str(self) -> &'static str {
        match self {
            SupportStatus::Supported => "supported",
            SupportStatus::NotSupported => "not_supported",
        }
    }
}

#[derive(Debug, Clone, Default)]
pub struct ModeSupport {
    pub modes: BTreeMap<String, SupportStatus>,
}

impl ModeSupport {
    pub fn with_defaults() -> Self {
        let mut modes = BTreeMap::new();
        for mode in DEFAULT_RUN_MODES {
            modes.insert(mode.to_string(), SupportStatus::Supported);
        }
        Self { modes }
    }

    pub fn apply_only(&mut self, only: &[String]) {
        for (mode, status) in self.modes.iter_mut() {
            if only.iter().any(|m| m == mode) {
                *status = SupportStatus::Supported;
            } else {
                *status = SupportStatus::NotSupported;
            }
        }
    }

    pub fn apply_skip(&mut self, skip: &[String]) {
        for mode in skip {
            if let Some(status) = self.modes.get_mut(mode) {
                *status = SupportStatus::NotSupported;
            }
        }
    }

    pub fn any_supported(&self) -> bool {
        self.modes.values().any(|status| *status == SupportStatus::Supported)
    }
}

#[derive(Debug, Clone)]
pub struct FeatureRecord {
    pub id: String,
    pub category: String,
    pub name: String,
    pub description: String,
    pub spec: String,
    pub modes: ModeSupport,
    pub platforms: Vec<String>,
    pub status: String,
    pub valid: bool,
}

#[derive(Debug, Clone)]
pub struct SspecItem {
    pub id: String,
    pub name: String,
    pub description: String,
    pub modes: ModeSupport,
    pub platforms: Vec<String>,
    pub ignored: bool,
}

/// Implement Record trait for unified database access
impl Record for FeatureRecord {
    fn id(&self) -> String {
        self.id.clone()
    }

    fn table_name() -> &'static str {
        "features"
    }

    fn from_sdn_row(row: &[String]) -> Result<Self, String> {
        let mut modes = ModeSupport::with_defaults();

        // Parse individual mode support from columns
        if let Some(val) = row.get(5) {
            if val == "not_supported" {
                modes
                    .modes
                    .insert("interpreter".to_string(), SupportStatus::NotSupported);
            }
        }
        if let Some(val) = row.get(6) {
            if val == "not_supported" {
                modes.modes.insert("jit".to_string(), SupportStatus::NotSupported);
            }
        }
        if let Some(val) = row.get(7) {
            if val == "not_supported" {
                modes
                    .modes
                    .insert("smf_cranelift".to_string(), SupportStatus::NotSupported);
            }
        }
        if let Some(val) = row.get(8) {
            if val == "not_supported" {
                modes.modes.insert("smf_llvm".to_string(), SupportStatus::NotSupported);
            }
        }

        Ok(FeatureRecord {
            id: row.get(0).cloned().unwrap_or_default(),
            category: row.get(1).cloned().unwrap_or_default(),
            name: row.get(2).cloned().unwrap_or_default(),
            description: row.get(3).cloned().unwrap_or_default(),
            spec: row.get(4).cloned().unwrap_or_default(),
            modes,
            platforms: row
                .get(9)
                .map(|s| {
                    s.split(',')
                        .map(|x| x.trim().to_string())
                        .filter(|x| !x.is_empty())
                        .collect()
                })
                .unwrap_or_default(),
            status: row.get(10).cloned().unwrap_or_else(|| "planned".to_string()),
            valid: row.get(11).map(|s| s == "true").unwrap_or(true),
        })
    }

    fn to_sdn_row(&self) -> Vec<String> {
        vec![
            self.id.clone(),
            self.category.clone(),
            self.name.clone(),
            self.description.clone(),
            self.spec.clone(),
            mode_status(&self.modes, "interpreter"),
            mode_status(&self.modes, "jit"),
            mode_status(&self.modes, "smf_cranelift"),
            mode_status(&self.modes, "smf_llvm"),
            self.platforms.join(","),
            self.status.clone(),
            self.valid.to_string(),
        ]
    }
}

#[derive(Debug, Default)]
struct PendingAttrs {
    id: Option<String>,
    only_modes: Vec<String>,
    skip_modes: Vec<String>,
    platforms: Vec<String>,
    ignore: bool,
}

pub fn parse_sspec_file(path: &Path) -> Result<Vec<SspecItem>, String> {
    let content = fs::read_to_string(path).map_err(|e| e.to_string())?;
    Ok(parse_sspec_metadata(&content))
}

pub fn parse_sspec_metadata(content: &str) -> Vec<SspecItem> {
    let lines: Vec<&str> = content.lines().collect();
    let mut items = Vec::new();
    let mut pending = PendingAttrs::default();
    let mut last_doc_block = String::new();
    let mut pending_doc_lines: Vec<String> = Vec::new();

    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim();

        if line == "\"\"\"" {
            let mut block = String::new();
            i += 1;
            while i < lines.len() {
                if lines[i].trim() == "\"\"\"" {
                    break;
                }
                block.push_str(lines[i]);
                block.push('\n');
                i += 1;
            }
            last_doc_block = block.trim().to_string();
            pending_doc_lines.clear();
        } else if line.starts_with("///") {
            let doc_line = line.trim_start_matches("///").trim().to_string();
            pending_doc_lines.push(doc_line);
        } else if line.starts_with("#[") {
            parse_attr_line(line, &mut pending);
        } else if let Some(name) = parse_named_call(line, "describe")
            .or_else(|| parse_named_call(line, "context"))
            .or_else(|| parse_named_call(line, "test"))
            .or_else(|| parse_named_call(line, "it"))
        {
            if !pending_doc_lines.is_empty() {
                last_doc_block = pending_doc_lines.join("\n").trim().to_string();
                pending_doc_lines.clear();
            }
            if let Some(id) = pending.id.take() {
                let mut modes = ModeSupport::with_defaults();
                if !pending.only_modes.is_empty() {
                    modes.apply_only(&pending.only_modes);
                }
                if !pending.skip_modes.is_empty() {
                    modes.apply_skip(&pending.skip_modes);
                }

                let description = extract_description(&last_doc_block);
                let item = SspecItem {
                    id,
                    name,
                    description,
                    modes,
                    platforms: pending.platforms.clone(),
                    ignored: pending.ignore,
                };
                items.push(item);
            }

            pending = PendingAttrs::default();
            last_doc_block = String::new();
        }

        i += 1;
    }

    items
}

fn parse_attr_line(line: &str, pending: &mut PendingAttrs) {
    let line = line.trim_start_matches("#[").trim_end_matches(']');
    if let Some(value) = parse_single_attr(line, "id") {
        pending.id = Some(value);
        return;
    }
    if let Some(modes) = parse_list_attr(line, "modes") {
        pending.only_modes = modes;
        return;
    }
    if let Some(modes) = parse_list_attr(line, "skip_modes") {
        pending.skip_modes = modes;
        return;
    }
    if let Some(platforms) = parse_list_attr(line, "platforms") {
        pending.platforms = platforms;
        return;
    }
    if line.trim() == "ignore" {
        pending.ignore = true;
    }
}

fn parse_single_attr(line: &str, name: &str) -> Option<String> {
    let prefix = format!("{}(", name);
    let value = line.strip_prefix(&prefix)?;
    let value = value.trim_end_matches(')').trim();
    if value.starts_with('"') && value.ends_with('"') && value.len() >= 2 {
        return Some(value[1..value.len() - 1].to_string());
    }
    None
}

fn parse_list_attr(line: &str, name: &str) -> Option<Vec<String>> {
    let prefix = format!("{}(", name);
    let values = line.strip_prefix(&prefix)?;
    let values = values.trim_end_matches(')').trim();
    if values.is_empty() {
        return Some(Vec::new());
    }
    Some(
        values
            .split(',')
            .map(|v| v.trim().trim_matches('"').to_string())
            .filter(|v| !v.is_empty())
            .collect(),
    )
}

fn parse_named_call(line: &str, name: &str) -> Option<String> {
    let prefix = format!("{} ", name);
    let rest = line.strip_prefix(&prefix)?;
    let rest = rest.trim();
    if rest.starts_with('"') {
        let end = rest[1..].find('"')?;
        return Some(rest[1..=end].trim_matches('"').to_string());
    }
    None
}

fn extract_description(doc_block: &str) -> String {
    if doc_block.is_empty() {
        return String::new();
    }
    for line in doc_block.lines() {
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        return trimmed.to_string();
    }
    doc_block.lines().next().unwrap_or("").trim().to_string()
}

pub fn update_feature_db_from_sspec(db_path: &Path, specs: &[PathBuf], failed_specs: &[PathBuf]) -> Result<(), String> {
    let mut db = load_feature_db(db_path).unwrap_or_else(|_| FeatureDb::new());
    let failed_set: BTreeMap<String, bool> = failed_specs
        .iter()
        .map(|path| (path.display().to_string(), true))
        .collect();
    let mut seen_ids: BTreeMap<String, String> = BTreeMap::new();

    for path in specs {
        let items = parse_sspec_file(path)?;
        for item in items {
            if !item.modes.any_supported() {
                return Err(format!("feature {} has no supported run modes", item.id));
            }
            if let Some(existing) = seen_ids.insert(item.id.clone(), path.display().to_string()) {
                return Err(format!(
                    "feature id conflict: {} used in {} and {}",
                    item.id,
                    existing,
                    path.display()
                ));
            }
            let failed = failed_set.contains_key(&path.display().to_string());
            db.upsert_from_sspec(&item, path, failed);
        }
    }

    for record in db.records.values_mut() {
        record.valid = seen_ids.contains_key(&record.id);
    }

    save_feature_db(db_path, &db).map_err(|e| e.to_string())?;
    let docs_dir = Path::new("doc/feature");
    let _ = generate_feature_docs(&db, docs_dir);
    Ok(())
}

#[derive(Debug, Default)]
pub struct FeatureDb {
    pub records: BTreeMap<String, FeatureRecord>,
}

impl FeatureDb {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn upsert_from_sspec(&mut self, item: &SspecItem, path: &Path, failed: bool) {
        let derived_category = derive_category_from_path(path);
        let entry = self.records.entry(item.id.clone()).or_insert_with(|| FeatureRecord {
            id: item.id.clone(),
            category: derived_category.clone().unwrap_or_else(|| "Uncategorized".to_string()),
            name: item.name.clone(),
            description: item.description.clone(),
            spec: path.display().to_string(),
            modes: ModeSupport::with_defaults(),
            platforms: item.platforms.clone(),
            status: "planned".to_string(),
            valid: true,
        });

        if (entry.category.is_empty() || entry.category == "Uncategorized") && derived_category.is_some() {
            entry.category = derived_category.unwrap_or_else(|| "Uncategorized".to_string());
        }
        if entry.name.is_empty() {
            entry.name = item.name.clone();
        }
        if entry.description.is_empty() {
            entry.description = item.description.clone();
        }
        entry.spec = path.display().to_string();
        entry.modes = item.modes.clone();
        if !item.platforms.is_empty() {
            entry.platforms = item.platforms.clone();
        }
        if item.ignored {
            entry.status = "ignored".to_string();
        } else if failed {
            entry.status = "failed".to_string();
        } else if entry.status == "ignored" || entry.status == "failed" {
            entry.status = "planned".to_string();
        }
        entry.valid = true;
    }
}

pub fn load_feature_db(path: &Path) -> Result<FeatureDb, String> {
    // Acquire lock before reading
    let _lock = FileLock::acquire(path, 10).map_err(|e| format!("Failed to acquire lock: {:?}", e))?;

    let content = fs::read_to_string(path).map_err(|e| e.to_string())?;
    let doc = parse_document(&content).map_err(|e| e.to_string())?;
    parse_feature_db(&doc)
}

fn parse_feature_db(doc: &SdnDocument) -> Result<FeatureDb, String> {
    let root = doc.root();
    let features = match root {
        SdnValue::Dict(dict) => dict.get("features"),
        _ => None,
    };

    let mut db = FeatureDb::new();
    let table = match features {
        Some(SdnValue::Table { fields, rows, .. }) => (fields, rows),
        None => return Ok(db),
        _ => return Err("features must be a table".to_string()),
    };

    let fields = table
        .0
        .as_ref()
        .ok_or_else(|| "features table missing fields".to_string())?;
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
        let record = FeatureRecord {
            id: id.clone(),
            category: row_map.get("category").cloned().unwrap_or_default(),
            name: row_map.get("name").cloned().unwrap_or_default(),
            description: row_map.get("description").cloned().unwrap_or_default(),
            spec: row_map.get("spec").cloned().unwrap_or_default(),
            modes: parse_modes(&row_map),
            platforms: parse_list_field(row_map.get("platforms")),
            status: row_map.get("status").cloned().unwrap_or_else(|| "planned".to_string()),
            valid: parse_bool_field(row_map.get("valid")).unwrap_or(true),
        };
        db.records.insert(id, record);
    }

    Ok(db)
}

pub fn generate_feature_docs(db: &FeatureDb, output_dir: &Path) -> Result<(), String> {
    let mut all_records: Vec<&FeatureRecord> = db.records.values().collect();
    all_records.sort_by(|a, b| compare_feature_id(&a.id, &b.id));
    let mut records: Vec<&FeatureRecord> = all_records.iter().copied().filter(|record| record.valid).collect();
    records.sort_by(|a, b| compare_feature_id(&a.id, &b.id));
    let last_id = all_records.last().map(|record| record.id.clone()).unwrap_or_default();

    generate_feature_index(output_dir, &records, &last_id)?;
    generate_category_docs(output_dir, &records)?;
    generate_pending_features(output_dir, &records)?;

    Ok(())
}

fn generate_feature_index(output_dir: &Path, records: &[&FeatureRecord], last_id: &str) -> Result<(), String> {
    let mut categories: BTreeMap<String, CategoryCounts> = BTreeMap::new();
    for record in records {
        let category = if record.category.is_empty() {
            "Uncategorized".to_string()
        } else {
            record.category.clone()
        };
        let parts = split_category(&category);
        for idx in 0..parts.len() {
            let key = parts[..=idx].join(".");
            categories
                .entry(key)
                .or_insert_with(CategoryCounts::default)
                .add(record);
        }
    }

    let mut md = String::new();
    md.push_str("# Feature Categories\n\n");
    if !last_id.is_empty() {
        md.push_str(&format!("Last ID: `{}`\n\n", last_id));
    }
    md.push_str("| Category | Features | Skips | Ignores | Fails |\n");
    md.push_str("|----------|----------|-------|---------|-------|\n");

    for (category, counts) in &categories {
        let link = category_link(category);
        md.push_str(&format!(
            "| [{}]({}) | {} | {} | {} | {} |\n",
            category, link, counts.total, counts.skipped, counts.ignored, counts.failed
        ));
    }

    let path = output_dir.join("feature.md");
    fs::write(&path, md).map_err(|e| e.to_string())?;
    Ok(())
}

fn generate_category_docs(output_dir: &Path, records: &[&FeatureRecord]) -> Result<(), String> {
    let mut categories: BTreeMap<String, Vec<&FeatureRecord>> = BTreeMap::new();
    for record in records {
        let category = if record.category.is_empty() {
            "Uncategorized".to_string()
        } else {
            record.category.clone()
        };
        categories.entry(category).or_default().push(record);
    }

    for (category, items) in &categories {
        let path = category_doc_path(output_dir, category);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).map_err(|e| e.to_string())?;
        }
        let mut md = String::new();
        md.push_str(&format!("# {}\n\n", category));

        let mut subcategories = collect_subcategories(category, records);
        subcategories.retain(|sub| sub != category);
        if !subcategories.is_empty() {
            md.push_str("## Subcategories\n\n");
            for sub in subcategories {
                let link = category_link(&sub);
                md.push_str(&format!("- [{}]({})\n", sub, link));
            }
            md.push_str("\n");
        }

        md.push_str("## Features\n\n");
        md.push_str("| ID | Feature | Description | Modes | Platforms | Spec |\n");
        md.push_str("|----|---------|-------------|-------|-----------|------|\n");

        for record in items {
            if record.status == "ignored" {
                continue;
            }
            let modes = record
                .modes
                .modes
                .iter()
                .map(|(mode, status)| format!("{}:{}", mode, status.as_str()))
                .collect::<Vec<_>>()
                .join(", ");
            let platforms = if record.platforms.is_empty() {
                "-".to_string()
            } else {
                record.platforms.join(", ")
            };
            let spec_link = spec_link_for_record(&path, record);
            md.push_str(&format!(
                "| <a id=\"feature-{}\"></a>{} | {} | {} | {} | {} | {} |\n",
                record.id.replace('.', "-"),
                record.id,
                record.name,
                record.description,
                modes,
                platforms,
                spec_link
            ));
        }

        fs::write(path, md).map_err(|e| e.to_string())?;
    }

    Ok(())
}

fn generate_pending_features(output_dir: &Path, records: &[&FeatureRecord]) -> Result<(), String> {
    use std::collections::BTreeMap;

    // Separate features by status
    let mut failed: Vec<&FeatureRecord> = Vec::new();
    let mut in_progress: Vec<&FeatureRecord> = Vec::new();
    let mut planned: Vec<&FeatureRecord> = Vec::new();
    let mut ignored: Vec<&FeatureRecord> = Vec::new();
    let mut complete: Vec<&FeatureRecord> = Vec::new();

    for record in records {
        match record.status.as_str() {
            "failed" => failed.push(record),
            "in_progress" => in_progress.push(record),
            "planned" => planned.push(record),
            "ignored" => ignored.push(record),
            "complete" => complete.push(record),
            _ => planned.push(record), // Unknown status -> treat as planned
        }
    }

    let total_pending = failed.len() + in_progress.len() + planned.len() + ignored.len();
    let total_features = records.len();
    let completion_pct = if total_features > 0 {
        complete.len() as f64 / total_features as f64 * 100.0
    } else {
        0.0
    };

    let mut md = String::new();
    md.push_str("# Pending Features\n\n");
    md.push_str(&format!("**Generated:** {}\n", chrono::Local::now().format("%Y-%m-%d")));
    md.push_str(&format!("**Total Pending:** {} features\n\n", total_pending));

    // Summary table
    md.push_str("## Summary\n\n");
    md.push_str("| Status | Count | Priority |\n");
    md.push_str("|--------|-------|---------|\n");
    md.push_str(&format!("| Failed | {} | 🔴 Critical |\n", failed.len()));
    md.push_str(&format!("| In Progress | {} | 🟡 High |\n", in_progress.len()));
    md.push_str(&format!("| Planned | {} | 🟢 Medium |\n", planned.len()));
    md.push_str(&format!("| Ignored | {} | ⚪ Low |\n\n", ignored.len()));
    md.push_str(&format!(
        "**Completion:** {:.1}% ({} complete / {} total)\n\n",
        completion_pct,
        complete.len(),
        total_features
    ));
    md.push_str("---\n\n");

    // Failed features section
    if !failed.is_empty() {
        md.push_str(&format!("## 🔴 Failed Features ({})\n\n", failed.len()));
        md.push_str("Features with failing tests - **needs immediate attention**\n\n");
        md.push_str("| ID | Category | Feature | Spec |\n");
        md.push_str("|----|----------|---------|------|\n");
        for record in &failed {
            let spec_link = if !record.spec.is_empty() {
                format!("[spec]({})", record.spec)
            } else {
                "-".to_string()
            };
            md.push_str(&format!(
                "| {} | {} | {} | {} |\n",
                record.id, record.category, record.name, spec_link
            ));
        }
        md.push_str("\n---\n\n");
    }

    // In Progress features section (grouped by category)
    if !in_progress.is_empty() {
        md.push_str(&format!("## 🟡 In Progress Features ({})\n\n", in_progress.len()));
        md.push_str("Features currently being implemented\n\n");

        let grouped = group_by_category(&in_progress);
        for (category, features) in grouped {
            md.push_str(&format!("### {} ({})\n\n", category, features.len()));
            md.push_str("| ID | Feature | Description | Spec |\n");
            md.push_str("|----|---------|-------------|------|\n");
            for record in features {
                let spec_link = if !record.spec.is_empty() {
                    format!("[spec]({})", record.spec)
                } else {
                    "-".to_string()
                };
                md.push_str(&format!(
                    "| {} | {} | {} | {} |\n",
                    record.id, record.name, record.description, spec_link
                ));
            }
            md.push_str("\n");
        }
        md.push_str("---\n\n");
    }

    // Planned features section (grouped by category)
    if !planned.is_empty() {
        md.push_str(&format!("## 🟢 Planned Features ({})\n\n", planned.len()));
        md.push_str("Features specified but not yet implemented\n\n");

        let grouped = group_by_category(&planned);
        for (category, features) in grouped {
            md.push_str(&format!("### {} ({})\n\n", category, features.len()));
            md.push_str("| ID | Feature | Description | Spec |\n");
            md.push_str("|----|---------|-------------|------|\n");
            for record in features {
                let spec_link = if !record.spec.is_empty() {
                    format!("[spec]({})", record.spec)
                } else {
                    "-".to_string()
                };
                md.push_str(&format!(
                    "| {} | {} | {} | {} |\n",
                    record.id, record.name, record.description, spec_link
                ));
            }
            md.push_str("\n");
        }
        md.push_str("---\n\n");
    }

    // Ignored features section
    if !ignored.is_empty() {
        md.push_str(&format!("## ⚪ Ignored Features ({})\n\n", ignored.len()));
        md.push_str("Features with tests marked `#[ignore]`\n\n");
        md.push_str("| ID | Category | Feature | Spec |\n");
        md.push_str("|----|----------|---------|------|\n");
        for record in &ignored {
            let spec_link = if !record.spec.is_empty() {
                format!("[spec]({})", record.spec)
            } else {
                "-".to_string()
            };
            md.push_str(&format!(
                "| {} | {} | {} | {} |\n",
                record.id, record.category, record.name, spec_link
            ));
        }
        md.push_str("\n---\n\n");
    }

    // Progress by category
    md.push_str("## Progress by Category\n\n");
    md.push_str("| Category | Total | Complete | Pending | % Complete |\n");
    md.push_str("|----------|-------|----------|---------|------------|\n");

    let mut category_stats: BTreeMap<String, (usize, usize)> = BTreeMap::new();
    for record in records {
        let cat = if record.category.is_empty() {
            "Uncategorized".to_string()
        } else {
            record.category.clone()
        };
        let entry = category_stats.entry(cat).or_insert((0, 0));
        entry.0 += 1; // total
        if record.status == "complete" {
            entry.1 += 1; // complete
        }
    }

    for (category, (total, complete_count)) in category_stats {
        let pending = total - complete_count;
        let pct = if total > 0 {
            complete_count as f64 / total as f64 * 100.0
        } else {
            0.0
        };
        md.push_str(&format!(
            "| {} | {} | {} | {} | {:.1}% |\n",
            category, total, complete_count, pending, pct
        ));
    }

    md.push_str("\n---\n\n");

    // Implementation priority
    md.push_str("## Implementation Priority\n\n");
    md.push_str("### Critical (Do First)\n");
    if !failed.is_empty() {
        md.push_str(&format!("1. Fix failed features ({} features)\n", failed.len()));
    }
    if !in_progress.is_empty() {
        md.push_str(&format!(
            "2. Complete in_progress features ({} features)\n",
            in_progress.len()
        ));
    }
    md.push_str("\n### High (Next Sprint)\n");
    md.push_str("3. Planned features with dependencies\n");
    md.push_str("\n### Medium (Backlog)\n");
    if !planned.is_empty() {
        md.push_str(&format!("4. Remaining planned features ({} features)\n", planned.len()));
    }
    md.push_str("\n### Low (Future)\n");
    if !ignored.is_empty() {
        md.push_str(&format!(
            "5. Ignored features ({} features) - requires special setup\n",
            ignored.len()
        ));
    }

    let path = output_dir.join("pending_feature.md");
    fs::write(&path, md).map_err(|e| e.to_string())?;

    Ok(())
}

// Helper function to group features by category
fn group_by_category<'a>(features: &[&'a FeatureRecord]) -> BTreeMap<String, Vec<&'a FeatureRecord>> {
    let mut grouped: BTreeMap<String, Vec<&FeatureRecord>> = BTreeMap::new();
    for record in features {
        let cat = if record.category.is_empty() {
            "Uncategorized".to_string()
        } else {
            record.category.clone()
        };
        grouped.entry(cat).or_default().push(record);
    }
    grouped
}

#[derive(Default)]
struct CategoryCounts {
    total: usize,
    skipped: usize,
    ignored: usize,
    failed: usize,
}

impl CategoryCounts {
    fn add(&mut self, record: &FeatureRecord) {
        self.total += 1;
        if record.status == "ignored" {
            self.ignored += 1;
        }
        if record.status == "failed" {
            self.failed += 1;
        }
        if record
            .modes
            .modes
            .values()
            .any(|status| *status == SupportStatus::NotSupported)
        {
            self.skipped += 1;
        }
    }
}

fn split_category(category: &str) -> Vec<String> {
    category
        .split('.')
        .map(|part| part.trim().to_string())
        .filter(|part| !part.is_empty())
        .collect()
}

fn collect_subcategories(category: &str, records: &[&FeatureRecord]) -> Vec<String> {
    let prefix = if category.is_empty() {
        "".to_string()
    } else {
        format!("{}.", category)
    };
    let mut subs = BTreeMap::new();
    for record in records {
        if record.category.starts_with(&prefix) {
            let rest = record.category[prefix.len()..].to_string();
            if rest.is_empty() {
                continue;
            }
            let part = rest.split('.').next().unwrap_or(&rest);
            let sub = format!("{}{}", prefix, part);
            subs.insert(sub, true);
        }
    }
    subs.keys().cloned().collect()
}

fn category_doc_path(output_dir: &Path, category: &str) -> PathBuf {
    let parts = split_category(category);
    let mut path = output_dir.join("category");
    for part in &parts[..parts.len().saturating_sub(1)] {
        path = path.join(slugify(part));
    }
    let file_name = parts.last().cloned().unwrap_or_else(|| "index".to_string());
    path.join(format!("{}.md", slugify(&file_name)))
}

pub fn category_link(category: &str) -> String {
    let parts = split_category(category);
    let mut link = String::from("category");
    if !parts.is_empty() {
        for part in &parts[..parts.len().saturating_sub(1)] {
            link.push('/');
            link.push_str(&slugify(part));
        }
        link.push('/');
        link.push_str(&slugify(parts.last().unwrap()));
        link.push_str(".md");
    } else {
        link.push_str("/index.md");
    }
    link
}

fn spec_link_for_record(doc_path: &Path, record: &FeatureRecord) -> String {
    if record.spec.is_empty() {
        return "-".to_string();
    }
    let doc_dir = match doc_path.parent() {
        Some(dir) => dir,
        None => return record.spec.clone(),
    };
    let spec_path = Path::new(&record.spec);
    if spec_path.is_absolute() || record.spec.contains("://") {
        return record.spec.clone();
    }
    let relative = relative_path(doc_dir, spec_path);
    let anchor = record.id.replace('.', "-");
    format!("[{}]({}#feature-{})", record.spec, relative, anchor)
}

fn relative_path(from_dir: &Path, to: &Path) -> String {
    let from_parts = normalized_parts(from_dir);
    let to_parts = normalized_parts(to);
    let mut common = 0usize;
    while common < from_parts.len() && common < to_parts.len() && from_parts[common] == to_parts[common] {
        common += 1;
    }
    let mut rel_parts: Vec<String> = Vec::new();
    for _ in common..from_parts.len() {
        rel_parts.push("..".to_string());
    }
    rel_parts.extend_from_slice(&to_parts[common..]);
    if rel_parts.is_empty() {
        ".".to_string()
    } else {
        rel_parts.join("/")
    }
}

fn normalized_parts(path: &Path) -> Vec<String> {
    let mut parts = Vec::new();
    for comp in path.components() {
        match comp {
            std::path::Component::Normal(value) => {
                parts.push(value.to_string_lossy().to_string());
            }
            std::path::Component::ParentDir => {
                parts.pop();
            }
            std::path::Component::CurDir => {}
            _ => {}
        }
    }
    parts
}

fn slugify(value: &str) -> String {
    value
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

pub fn save_feature_db(path: &Path, db: &FeatureDb) -> Result<(), std::io::Error> {
    // Acquire lock before writing
    let _lock =
        FileLock::acquire(path, 10).map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, format!("{:?}", e)))?;

    let mut fields = vec![
        "id".to_string(),
        "category".to_string(),
        "name".to_string(),
        "description".to_string(),
        "spec".to_string(),
        "mode_interpreter".to_string(),
        "mode_jit".to_string(),
        "mode_smf_cranelift".to_string(),
        "mode_smf_llvm".to_string(),
        "platforms".to_string(),
        "status".to_string(),
        "valid".to_string(),
    ];

    let mut rows = Vec::new();
    for record in db.records.values() {
        let mut row = Vec::new();
        row.push(SdnValue::String(record.id.clone()));
        row.push(SdnValue::String(record.category.clone()));
        row.push(SdnValue::String(record.name.clone()));
        row.push(SdnValue::String(record.description.clone()));
        row.push(SdnValue::String(record.spec.clone()));
        row.push(SdnValue::String(mode_status(&record.modes, "interpreter")));
        row.push(SdnValue::String(mode_status(&record.modes, "jit")));
        row.push(SdnValue::String(mode_status(&record.modes, "smf_cranelift")));
        row.push(SdnValue::String(mode_status(&record.modes, "smf_llvm")));
        row.push(SdnValue::String(record.platforms.join(",")));
        row.push(SdnValue::String(record.status.clone()));
        row.push(SdnValue::Bool(record.valid));
        rows.push(row);
    }

    let table = SdnValue::Table {
        fields: Some(fields),
        types: None,
        rows,
    };

    let mut root = BTreeMap::new();
    root.insert("features".to_string(), table);
    let mut doc = SdnDocument::parse("features |id|").map_err(|e| std::io::Error::other(e.to_string()))?;
    let mut dict = IndexMap::new();
    for (key, value) in root {
        dict.insert(key, value);
    }
    *doc.root_mut() = SdnValue::Dict(dict);

    let content = doc.to_sdn();
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    // Atomic write: temp file then rename
    let temp_path = path.with_extension("sdn.tmp");
    fs::write(&temp_path, content)?;
    fs::rename(&temp_path, path)?;
    Ok(())
}

fn parse_modes(row: &BTreeMap<String, String>) -> ModeSupport {
    let mut support = ModeSupport::with_defaults();
    for mode in DEFAULT_RUN_MODES {
        let key = format!("mode_{}", mode);
        if let Some(value) = row.get(&key) {
            if value == "not_supported" {
                support.modes.insert(mode.to_string(), SupportStatus::NotSupported);
            }
        }
    }
    support
}

fn parse_list_field(value: Option<&String>) -> Vec<String> {
    value
        .map(|v| {
            v.split(',')
                .map(|item| item.trim().to_string())
                .filter(|item| !item.is_empty())
                .collect()
        })
        .unwrap_or_default()
}

fn mode_status(modes: &ModeSupport, key: &str) -> String {
    modes
        .modes
        .get(key)
        .copied()
        .unwrap_or(SupportStatus::Supported)
        .as_str()
        .to_string()
}

fn parse_bool_field(value: Option<&String>) -> Option<bool> {
    value.map(|v| v == "true")
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

fn compare_feature_id(left: &str, right: &str) -> std::cmp::Ordering {
    let left_parts = parse_feature_id_parts(left);
    let right_parts = parse_feature_id_parts(right);
    left_parts.cmp(&right_parts)
}

fn parse_feature_id_parts(value: &str) -> Vec<FeatureIdPart> {
    value
        .split('.')
        .map(|part| {
            if let Ok(num) = part.parse::<u64>() {
                FeatureIdPart::Number(num)
            } else {
                FeatureIdPart::Text(part.to_string())
            }
        })
        .collect()
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum FeatureIdPart {
    Number(u64),
    Text(String),
}

fn derive_category_from_path(path: &Path) -> Option<String> {
    let parts: Vec<String> = path
        .components()
        .filter_map(|comp| match comp {
            std::path::Component::Normal(value) => Some(value.to_string_lossy().to_string()),
            _ => None,
        })
        .collect();
    let features_idx = parts.iter().position(|p| p == "features")?;
    let category = parts.get(features_idx + 1)?.to_string();
    Some(title_case_category(&category))
}

fn title_case_category(value: &str) -> String {
    value
        .split('_')
        .map(|part| {
            let mut chars = part.chars();
            match chars.next() {
                Some(first) => format!("{}{}", first.to_ascii_uppercase(), chars.as_str().to_ascii_lowercase()),
                None => String::new(),
            }
        })
        .collect::<Vec<String>>()
        .join(" ")
}

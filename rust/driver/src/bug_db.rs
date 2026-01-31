//! Bug tracking database - links bugs to reproducible test cases.
//!
//! Stores:
//! - Bug identification and status
//! - Required links to test cases that reproduce the bug
//! - Timing impact (for performance bugs)
//! - Build impact (if bug causes compilation errors)
//! - Resolution information
//!
//! Auto-generates: doc/bug/bug_report.md

use crate::db_lock::FileLock;
use serde::{Deserialize, Serialize};
use simple_sdn::{parse_document, SdnValue};
use std::collections::HashMap;
use std::fs;
use std::path::Path;

/// Bug database
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BugDb {
    pub version: String,
    pub last_updated: String,
    pub bugs: HashMap<String, BugRecord>,
}

/// Bug record
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BugRecord {
    // Identification
    pub bug_id: String,
    pub title: String,

    // Status
    pub status: BugStatus,
    pub priority: Priority,
    pub severity: Severity,

    // Description
    pub description: String,

    // Reproducibility (REQUIRED)
    pub reproducible_by: Vec<String>, // Test IDs that reproduce this bug
    pub reproduction_steps: String,

    // Timing impact (optional, for performance bugs)
    pub timing_impact: Option<TimingImpact>,

    // Build impact (optional, if bug causes compilation errors)
    pub build_impact: Option<BuildImpact>,

    // Links
    pub related_tests: Vec<String>,
    pub related_bugs: Vec<String>,
    pub related_features: Vec<String>,

    // Metadata
    pub created: String,
    pub updated: String,
    pub assignee: Option<String>,
    pub reporter: Option<String>,
    pub tags: Vec<String>,

    // Resolution (when status = fixed/closed)
    pub resolution: Option<BugResolution>,

    // Record validity
    pub valid: bool,
}

/// Bug status
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum BugStatus {
    Open,
    InProgress,
    Fixed,
    Closed,
    WontFix,
}

/// Bug priority
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Priority {
    P0, // Critical
    P1, // High
    P2, // Medium
    P3, // Low
}

/// Bug severity
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    Critical,
    Major,
    Minor,
    Trivial,
}

/// Timing impact (for performance bugs)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimingImpact {
    pub affected_tests: Vec<String>,
    pub regression_pct: f64,
    pub intermittent: bool,
}

/// Build impact (if bug causes compilation errors)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BuildImpact {
    pub causes_errors: bool,
    pub error_codes: Vec<String>,
    pub affected_files: Vec<String>,
}

/// Bug resolution
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BugResolution {
    pub fixed_in_commit: String,
    pub verified_by: Vec<String>, // Test IDs that verify the fix
    pub fixed_date: String,
}

impl BugDb {
    pub fn new() -> Self {
        BugDb {
            version: "1.0".to_string(),
            last_updated: chrono::Utc::now().to_rfc3339(),
            bugs: HashMap::new(),
        }
    }

    pub fn valid_records(&self) -> Vec<&BugRecord> {
        self.bugs.values().filter(|b| b.valid).collect()
    }
}

impl BugRecord {
    pub fn new(bug_id: String, title: String, description: String, reproducible_by: Vec<String>) -> Self {
        BugRecord {
            bug_id,
            title,
            status: BugStatus::Open,
            priority: Priority::P2,
            severity: Severity::Minor,
            description,
            reproducible_by,
            reproduction_steps: String::new(),
            timing_impact: None,
            build_impact: None,
            related_tests: Vec::new(),
            related_bugs: Vec::new(),
            related_features: Vec::new(),
            created: chrono::Utc::now().to_rfc3339(),
            updated: chrono::Utc::now().to_rfc3339(),
            assignee: None,
            reporter: None,
            tags: Vec::new(),
            resolution: None,
            valid: true,
        }
    }
}

/// Load bug database from SDN file
pub fn load_bug_db(path: &Path) -> Result<BugDb, String> {
    if !path.exists() {
        return Ok(BugDb::new());
    }

    let _lock = FileLock::acquire(path, 10).map_err(|e| format!("Failed to acquire lock: {:?}", e))?;
    let content = fs::read_to_string(path).map_err(|e| e.to_string())?;

    // Try SDN format first, fall back to JSON for backward compatibility
    if let Ok(doc) = parse_document(&content) {
        parse_bug_db_sdn(&doc)
    } else {
        // Fallback to JSON format for existing databases
        serde_json::from_str(&content).map_err(|e| e.to_string())
    }
}

/// Parse bug database from SDN document
fn parse_bug_db_sdn(doc: &simple_sdn::SdnDocument) -> Result<BugDb, String> {
    let root = doc.root();
    let bugs_table = match root {
        SdnValue::Table { .. } => Some(root),
        SdnValue::Dict(dict) => dict.get("bugs"),
        _ => None,
    };

    let mut db = BugDb::new();

    if let Some(SdnValue::Table {
        fields: Some(fields),
        rows,
        ..
    }) = bugs_table
    {
        for row in rows {
            if row.len() < fields.len() {
                continue; // Skip malformed rows
            }

            // Helper to get field value
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

            let bug_id = get_field("bug_id");
            if bug_id.is_empty() {
                continue;
            }

            let status_str = get_field("status");
            let status = match status_str.as_str() {
                "open" => BugStatus::Open,
                "inprogress" | "in_progress" => BugStatus::InProgress,
                "fixed" => BugStatus::Fixed,
                "closed" => BugStatus::Closed,
                "wontfix" | "wont_fix" => BugStatus::WontFix,
                _ => BugStatus::Open,
            };

            let priority_str = get_field("priority");
            let priority = match priority_str.as_str() {
                "P0" => Priority::P0,
                "P1" => Priority::P1,
                "P2" => Priority::P2,
                "P3" => Priority::P3,
                _ => Priority::P2,
            };

            let severity_str = get_field("severity");
            let severity = match severity_str.as_str() {
                "critical" => Severity::Critical,
                "major" => Severity::Major,
                "minor" => Severity::Minor,
                "trivial" => Severity::Trivial,
                _ => Severity::Minor,
            };

            // Parse JSON-encoded complex fields
            let timing_impact: Option<TimingImpact> = {
                let s = get_field("timing_impact");
                if s.is_empty() {
                    None
                } else {
                    serde_json::from_str(&s).ok()
                }
            };

            let build_impact: Option<BuildImpact> = {
                let s = get_field("build_impact");
                if s.is_empty() {
                    None
                } else {
                    serde_json::from_str(&s).ok()
                }
            };

            let resolution: Option<BugResolution> = {
                let s = get_field("resolution");
                if s.is_empty() {
                    None
                } else {
                    serde_json::from_str(&s).ok()
                }
            };

            let reproducible_by: Vec<String> = get_field("reproducible_by")
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
            let related_tests: Vec<String> = get_field("related_tests")
                .split(',')
                .map(|s| s.trim().to_string())
                .filter(|s| !s.is_empty())
                .collect();
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

            let assignee_str = get_field("assignee");
            let assignee = if assignee_str.is_empty() {
                None
            } else {
                Some(assignee_str)
            };
            let reporter_str = get_field("reporter");
            let reporter = if reporter_str.is_empty() {
                None
            } else {
                Some(reporter_str)
            };

            let record = BugRecord {
                bug_id: bug_id.clone(),
                title: get_field("title"),
                status,
                priority,
                severity,
                description: get_field("description"),
                reproducible_by,
                reproduction_steps: get_field("reproduction_steps"),
                timing_impact,
                build_impact,
                related_tests,
                related_bugs,
                related_features,
                created: get_field("created"),
                updated: get_field("updated"),
                assignee,
                reporter,
                tags,
                resolution,
                valid: get_field("valid") == "true",
            };

            db.bugs.insert(bug_id, record);
        }
    }

    Ok(db)
}

/// Save bug database to SDN file (with file locking)
pub fn save_bug_db(path: &Path, db: &BugDb) -> Result<(), String> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }

    let _lock = FileLock::acquire(path, 10).map_err(|e| format!("Failed to acquire lock: {:?}", e))?;

    let mut content = String::new();
    content.push_str("bugs |bug_id, title, description, status, priority, severity, reproducible_by, reproduction_steps, timing_impact, build_impact, related_tests, related_bugs, related_features, created, updated, assignee, reporter, tags, resolution, valid|\n");

    let mut sorted_bugs: Vec<_> = db.bugs.values().collect();
    sorted_bugs.sort_by(|a, b| a.bug_id.cmp(&b.bug_id));

    for bug in sorted_bugs {
        let status_str = match bug.status {
            BugStatus::Open => "open",
            BugStatus::InProgress => "in_progress",
            BugStatus::Fixed => "fixed",
            BugStatus::Closed => "closed",
            BugStatus::WontFix => "wont_fix",
        };

        let priority_str = match bug.priority {
            Priority::P0 => "P0",
            Priority::P1 => "P1",
            Priority::P2 => "P2",
            Priority::P3 => "P3",
        };

        let severity_str = match bug.severity {
            Severity::Critical => "critical",
            Severity::Major => "major",
            Severity::Minor => "minor",
            Severity::Trivial => "trivial",
        };

        let timing_impact_json = bug
            .timing_impact
            .as_ref()
            .map(|t| serde_json::to_string(t).unwrap_or_default())
            .unwrap_or_default();
        let build_impact_json = bug
            .build_impact
            .as_ref()
            .map(|b| serde_json::to_string(b).unwrap_or_default())
            .unwrap_or_default();
        let resolution_json = bug
            .resolution
            .as_ref()
            .map(|r| serde_json::to_string(r).unwrap_or_default())
            .unwrap_or_default();

        let quote = |s: &str| {
            if s.is_empty() || s.contains(',') || s.contains('"') || s.contains('\n') {
                format!("\"{}\"", s.replace("\"", "\\\"").replace("\n", "\\n"))
            } else {
                s.to_string()
            }
        };

        let row = vec![
            quote(&bug.bug_id),
            quote(&bug.title),
            quote(&bug.description),
            quote(status_str),
            quote(priority_str),
            quote(severity_str),
            quote(&bug.reproducible_by.join(",")),
            quote(&bug.reproduction_steps),
            quote(&timing_impact_json),
            quote(&build_impact_json),
            quote(&bug.related_tests.join(",")),
            quote(&bug.related_bugs.join(",")),
            quote(&bug.related_features.join(",")),
            quote(&bug.created),
            quote(&bug.updated),
            quote(&bug.assignee.clone().unwrap_or_default()),
            quote(&bug.reporter.clone().unwrap_or_default()),
            quote(&bug.tags.join(",")),
            quote(&resolution_json),
            bug.valid.to_string(),
        ];

        content.push_str("    ");
        content.push_str(&row.join(", "));
        content.push('\n');
    }

    let temp_path = path.with_extension("sdn.tmp");
    fs::write(&temp_path, &content).map_err(|e| e.to_string())?;
    fs::rename(&temp_path, path).map_err(|e| e.to_string())?;

    Ok(())
}

/// Add a bug to the database
pub fn add_bug(
    db: &mut BugDb,
    bug_id: String,
    title: String,
    description: String,
    reproducible_by: Vec<String>,
    priority: Priority,
    severity: Severity,
) -> Result<(), String> {
    // Validate: bug must have at least one reproducible test case
    if reproducible_by.is_empty() {
        return Err(format!(
            "Bug {} must have at least one test case that reproduces it",
            bug_id
        ));
    }

    let mut bug = BugRecord::new(bug_id.clone(), title, description, reproducible_by);
    bug.priority = priority;
    bug.severity = severity;

    db.bugs.insert(bug_id, bug);
    db.last_updated = chrono::Utc::now().to_rfc3339();

    Ok(())
}

/// Update bug status
pub fn update_bug_status(db: &mut BugDb, bug_id: &str, status: BugStatus) -> Result<(), String> {
    let bug = db
        .bugs
        .get_mut(bug_id)
        .ok_or_else(|| format!("Bug {} not found", bug_id))?;

    bug.status = status;
    bug.updated = chrono::Utc::now().to_rfc3339();
    db.last_updated = chrono::Utc::now().to_rfc3339();

    Ok(())
}

/// Mark bug as fixed
pub fn mark_bug_fixed(db: &mut BugDb, bug_id: &str, commit: String, verified_by: Vec<String>) -> Result<(), String> {
    let bug = db
        .bugs
        .get_mut(bug_id)
        .ok_or_else(|| format!("Bug {} not found", bug_id))?;

    bug.status = BugStatus::Fixed;
    bug.resolution = Some(BugResolution {
        fixed_in_commit: commit,
        verified_by,
        fixed_date: chrono::Utc::now().to_rfc3339(),
    });
    bug.updated = chrono::Utc::now().to_rfc3339();
    db.last_updated = chrono::Utc::now().to_rfc3339();

    Ok(())
}

/// Validate bug record
pub fn validate_bug_record(bug: &BugRecord) -> Result<(), String> {
    if bug.reproducible_by.is_empty() {
        return Err(format!("Bug {} has no reproducible test cases", bug.bug_id));
    }

    Ok(())
}

/// Generate bug report documentation
pub fn generate_bug_report(db: &BugDb, output_dir: &Path) -> Result<(), String> {
    let mut md = String::new();

    // Header
    md.push_str("# Bug Report\n\n");
    md.push_str(&format!(
        "**Generated:** {}\n",
        chrono::Local::now().format("%Y-%m-%d %H:%M:%S")
    ));

    // Count bugs by status
    let mut open = 0;
    let mut in_progress = 0;
    let mut fixed = 0;
    let mut closed = 0;
    let mut wontfix = 0;

    for bug in db.valid_records() {
        match bug.status {
            BugStatus::Open => open += 1,
            BugStatus::InProgress => in_progress += 1,
            BugStatus::Fixed => fixed += 1,
            BugStatus::Closed => closed += 1,
            BugStatus::WontFix => wontfix += 1,
        }
    }

    let total = open + in_progress + fixed + closed + wontfix;
    let active = open + in_progress;

    md.push_str(&format!("**Total Bugs:** {}\n", total));
    md.push_str(&format!("**Active Bugs:** {}\n\n", active));

    // Summary table
    md.push_str("## Summary\n\n");
    md.push_str("| Status | Count |\n");
    md.push_str("|--------|-------|\n");
    md.push_str(&format!("| 🔴 Open | {} |\n", open));
    md.push_str(&format!("| 🟡 In Progress | {} |\n", in_progress));
    md.push_str(&format!("| ✅ Fixed | {} |\n", fixed));
    md.push_str(&format!("| ⚪ Closed | {} |\n", closed));
    md.push_str(&format!("| ❌ Won't Fix | {} |\n\n", wontfix));

    // Open bugs section (priority sorted)
    if open > 0 {
        md.push_str("---\n\n");
        md.push_str(&format!("## 🔴 Open Bugs ({})\n\n", open));

        let mut open_bugs: Vec<&BugRecord> = db
            .valid_records()
            .into_iter()
            .filter(|b| b.status == BugStatus::Open)
            .collect();

        // Sort by priority
        open_bugs.sort_by_key(|b| match b.priority {
            Priority::P0 => 0,
            Priority::P1 => 1,
            Priority::P2 => 2,
            Priority::P3 => 3,
        });

        for bug in open_bugs {
            generate_bug_section(&mut md, bug);
        }
    }

    // In Progress bugs section
    if in_progress > 0 {
        md.push_str("---\n\n");
        md.push_str(&format!("## 🟡 In Progress Bugs ({})\n\n", in_progress));

        let in_progress_bugs: Vec<&BugRecord> = db
            .valid_records()
            .into_iter()
            .filter(|b| b.status == BugStatus::InProgress)
            .collect();

        for bug in in_progress_bugs {
            generate_bug_section(&mut md, bug);
        }
    }

    // Recently fixed bugs section (last 10)
    if fixed > 0 {
        md.push_str("---\n\n");
        md.push_str(&format!("## ✅ Recently Fixed Bugs (showing up to 10)\n\n"));

        let mut fixed_bugs: Vec<&BugRecord> = db
            .valid_records()
            .into_iter()
            .filter(|b| b.status == BugStatus::Fixed)
            .collect();

        // Sort by fixed date (most recent first)
        fixed_bugs.sort_by(|a, b| {
            let a_date = a.resolution.as_ref().map(|r| &r.fixed_date);
            let b_date = b.resolution.as_ref().map(|r| &r.fixed_date);
            b_date.cmp(&a_date)
        });

        for bug in fixed_bugs.iter().take(10) {
            generate_bug_section(&mut md, bug);
        }
    }

    // Write to file
    let output_path = output_dir.join("bug_report.md");
    fs::create_dir_all(output_dir).map_err(|e| e.to_string())?;
    fs::write(&output_path, md).map_err(|e| e.to_string())?;

    Ok(())
}

/// Generate a single bug section
fn generate_bug_section(md: &mut String, bug: &BugRecord) {
    let priority_str = match bug.priority {
        Priority::P0 => "P0 (Critical)",
        Priority::P1 => "P1 (High)",
        Priority::P2 => "P2 (Medium)",
        Priority::P3 => "P3 (Low)",
    };

    let severity_str = match bug.severity {
        Severity::Critical => "Critical",
        Severity::Major => "Major",
        Severity::Minor => "Minor",
        Severity::Trivial => "Trivial",
    };

    md.push_str(&format!("### {} - {}\n\n", bug.bug_id, bug.title));
    md.push_str(&format!(
        "**Priority:** {} | **Severity:** {}\n",
        priority_str, severity_str
    ));
    md.push_str(&format!("**Status:** {:?}\n", bug.status));
    md.push_str(&format!("**Created:** {}\n\n", bug.created));

    md.push_str(&format!("**Description:**\n{}\n\n", bug.description));

    // Reproducible by (REQUIRED)
    md.push_str("**Reproducible By:**\n");
    for test_id in &bug.reproducible_by {
        md.push_str(&format!("- `{}`\n", test_id));
    }
    md.push_str("\n");

    // Reproduction steps
    if !bug.reproduction_steps.is_empty() {
        md.push_str("**Reproduction Steps:**\n");
        md.push_str(&bug.reproduction_steps);
        md.push_str("\n\n");
    }

    // Timing impact
    if let Some(ref timing) = bug.timing_impact {
        md.push_str(&format!(
            "**Performance Impact:** {:+.1}% regression",
            timing.regression_pct
        ));
        if timing.intermittent {
            md.push_str(" (intermittent)");
        }
        md.push_str("\n\n");
    }

    // Build impact
    if let Some(ref build) = bug.build_impact {
        if build.causes_errors {
            md.push_str("**Build Impact:** Causes compilation errors\n");
            if !build.error_codes.is_empty() {
                md.push_str(&format!("- Error codes: {}\n", build.error_codes.join(", ")));
            }
            if !build.affected_files.is_empty() {
                md.push_str("- Affected files:\n");
                for file in &build.affected_files {
                    md.push_str(&format!("  - `{}`\n", file));
                }
            }
            md.push_str("\n");
        }
    }

    // Resolution
    if let Some(ref resolution) = bug.resolution {
        md.push_str(&format!("**Fixed:** {}\n", resolution.fixed_date));
        md.push_str(&format!("**Fixed in commit:** `{}`\n", resolution.fixed_in_commit));
        if !resolution.verified_by.is_empty() {
            md.push_str("**Verified by:**\n");
            for test_id in &resolution.verified_by {
                md.push_str(&format!("- `{}`\n", test_id));
            }
        }
        md.push_str("\n");
    }

    // Assignee
    if let Some(ref assignee) = bug.assignee {
        md.push_str(&format!("**Assignee:** {}\n\n", assignee));
    }

    md.push_str("---\n\n");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_bug_db() {
        let db = BugDb::new();
        assert_eq!(db.version, "1.0");
        assert_eq!(db.bugs.len(), 0);
    }

    #[test]
    fn test_add_bug() {
        let mut db = BugDb::new();
        let result = add_bug(
            &mut db,
            "bug_001".to_string(),
            "Test bug".to_string(),
            "Description".to_string(),
            vec!["test_001".to_string()],
            Priority::P1,
            Severity::Major,
        );

        assert!(result.is_ok());
        assert_eq!(db.bugs.len(), 1);
        let bug = db.bugs.get("bug_001").unwrap();
        assert_eq!(bug.status, BugStatus::Open);
    }

    #[test]
    fn test_add_bug_without_test_fails() {
        let mut db = BugDb::new();
        let result = add_bug(
            &mut db,
            "bug_002".to_string(),
            "Test bug".to_string(),
            "Description".to_string(),
            vec![], // Empty reproducible_by
            Priority::P1,
            Severity::Major,
        );

        assert!(result.is_err());
        assert_eq!(db.bugs.len(), 0);
    }

    #[test]
    fn test_update_bug_status() {
        let mut db = BugDb::new();
        add_bug(
            &mut db,
            "bug_003".to_string(),
            "Test bug".to_string(),
            "Description".to_string(),
            vec!["test_001".to_string()],
            Priority::P1,
            Severity::Major,
        )
        .unwrap();

        let result = update_bug_status(&mut db, "bug_003", BugStatus::InProgress);
        assert!(result.is_ok());

        let bug = db.bugs.get("bug_003").unwrap();
        assert_eq!(bug.status, BugStatus::InProgress);
    }

    #[test]
    fn test_mark_bug_fixed() {
        let mut db = BugDb::new();
        add_bug(
            &mut db,
            "bug_004".to_string(),
            "Test bug".to_string(),
            "Description".to_string(),
            vec!["test_001".to_string()],
            Priority::P1,
            Severity::Major,
        )
        .unwrap();

        let result = mark_bug_fixed(&mut db, "bug_004", "abc123".to_string(), vec!["test_001".to_string()]);
        assert!(result.is_ok());

        let bug = db.bugs.get("bug_004").unwrap();
        assert_eq!(bug.status, BugStatus::Fixed);
        assert!(bug.resolution.is_some());
    }

    #[test]
    fn test_validate_bug_record() {
        let bug = BugRecord::new(
            "bug_005".to_string(),
            "Test".to_string(),
            "Desc".to_string(),
            vec!["test_001".to_string()],
        );

        assert!(validate_bug_record(&bug).is_ok());
    }

    #[test]
    fn test_validate_bug_record_fails_without_tests() {
        let mut bug = BugRecord::new("bug_006".to_string(), "Test".to_string(), "Desc".to_string(), vec![]);

        assert!(validate_bug_record(&bug).is_err());
    }
}

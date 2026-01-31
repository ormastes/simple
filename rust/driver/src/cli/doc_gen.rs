//! Documentation generation commands.
//!
//! Commands:
//! - `simple feature-gen` - Generate feature.md from feature_db.sdn
//! - `simple task-gen` - Generate task.md from task_db.sdn
//! - `simple spec-gen` - Generate doc/spec/ from tests/spec/*_spec.spl
//! - `simple todo-scan` - Scan source code and update todo_db.sdn
//! - `simple todo-gen` - Generate TODO.md from todo_db.sdn
//! - `simple test-result-gen` - Generate test_result.md from test_db.sdn
//! - `simple bug-add` - Add a new bug
//! - `simple bug-gen` - Generate bug_report.md from bug_db.sdn
//! - `simple bug-update` - Update bug status

use std::fs;
use std::path::{Path, PathBuf};

use crate::bug_db::{
    add_bug, generate_bug_report, load_bug_db, save_bug_db, update_bug_status, mark_bug_fixed, BugStatus, Priority,
    Severity,
};
use crate::feature_db::{generate_feature_docs, load_feature_db};
use crate::task_db::{generate_task_docs, load_task_db};
use crate::test_db::{generate_test_result_docs, load_test_db};
use crate::todo_db::{generate_todo_docs, load_todo_db, save_todo_db, update_todo_db_incremental_parallel};

/// Run feature-gen command
pub fn run_feature_gen(args: &[String]) -> i32 {
    let db_path = args
        .iter()
        .position(|a| a == "--db")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("doc/feature/feature_db.sdn"));

    let output_dir = args
        .iter()
        .position(|a| a == "-o" || a == "--output")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("doc/feature"));

    println!("Generating feature docs from {}...", db_path.display());

    let db = match load_feature_db(&db_path) {
        Ok(db) => db,
        Err(e) => {
            eprintln!("error: failed to load feature db: {}", e);
            return 1;
        }
    };

    if let Err(e) = generate_feature_docs(&db, &output_dir) {
        eprintln!("error: failed to generate docs: {}", e);
        return 1;
    }

    let count = db.records.values().filter(|r| r.valid).count();
    println!("Generated docs for {} features", count);
    println!("  -> {}/feature.md", output_dir.display());
    println!("  -> {}/category/*.md", output_dir.display());

    0
}

/// Run task-gen command
pub fn run_task_gen(args: &[String]) -> i32 {
    let db_path = args
        .iter()
        .position(|a| a == "--db")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("doc/task/task_db.sdn"));

    let output_dir = args
        .iter()
        .position(|a| a == "-o" || a == "--output")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("doc/task"));

    println!("Generating task docs from {}...", db_path.display());

    let db = match load_task_db(&db_path) {
        Ok(db) => db,
        Err(e) => {
            eprintln!("error: failed to load task db: {}", e);
            return 1;
        }
    };

    if let Err(e) = generate_task_docs(&db, &output_dir) {
        eprintln!("error: failed to generate docs: {}", e);
        return 1;
    }

    let count = db.records.values().filter(|r| r.valid).count();
    println!("Generated docs for {} tasks", count);
    println!("  -> {}/task.md", output_dir.display());

    0
}

/// Run spec-gen command
pub fn run_spec_gen(args: &[String]) -> i32 {
    let spec_dir = args
        .iter()
        .position(|a| a == "--input")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("tests/specs"));

    let output_dir = args
        .iter()
        .position(|a| a == "-o" || a == "--output")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("doc/spec/generated"));

    println!("Generating spec docs from {}...", spec_dir.display());

    // Find all _spec.spl files
    let spec_files = match find_spec_files(&spec_dir) {
        Ok(files) => files,
        Err(e) => {
            eprintln!("error: failed to find spec files: {}", e);
            return 1;
        }
    };

    if spec_files.is_empty() {
        println!("No spec files found in {}", spec_dir.display());
        return 0;
    }

    // Create output directory
    if let Err(e) = fs::create_dir_all(&output_dir) {
        eprintln!("error: failed to create output dir: {}", e);
        return 1;
    }

    let mut generated = 0;
    for spec_file in &spec_files {
        match generate_spec_doc(spec_file, &output_dir) {
            Ok(output_path) => {
                println!("  {} -> {}", spec_file.display(), output_path.display());
                generated += 1;
            }
            Err(e) => {
                eprintln!("  warning: {}: {}", spec_file.display(), e);
            }
        }
    }

    println!("Generated {} spec docs", generated);
    println!("  -> {}/*.md", output_dir.display());

    0
}

fn find_spec_files(dir: &Path) -> Result<Vec<PathBuf>, String> {
    let mut files = Vec::new();

    if !dir.exists() {
        return Ok(files);
    }

    fn walk_dir(dir: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
        let entries = fs::read_dir(dir).map_err(|e| e.to_string())?;
        for entry in entries {
            let entry = entry.map_err(|e| e.to_string())?;
            let path = entry.path();
            if path.is_dir() {
                walk_dir(&path, files)?;
            } else if path.extension().map(|e| e == "spl").unwrap_or(false) {
                if let Some(stem) = path.file_stem() {
                    if stem.to_string_lossy().ends_with("_spec") {
                        files.push(path);
                    }
                }
            }
        }
        Ok(())
    }

    walk_dir(dir, &mut files)?;
    files.sort();
    Ok(files)
}

fn generate_spec_doc(spec_file: &Path, output_dir: &Path) -> Result<PathBuf, String> {
    let content = fs::read_to_string(spec_file).map_err(|e| e.to_string())?;

    // Extract spec name from filename
    let stem = spec_file
        .file_stem()
        .ok_or_else(|| "invalid filename".to_string())?
        .to_string_lossy();
    let name = stem.strip_suffix("_spec").unwrap_or(&stem);
    let title = title_case(name);

    // Parse spec content and extract documentation
    let doc = parse_spec_to_markdown(&content, &title);

    // Write output
    let output_path = output_dir.join(format!("{}.md", name));
    fs::write(&output_path, doc).map_err(|e| e.to_string())?;

    Ok(output_path)
}

fn parse_spec_to_markdown(content: &str, title: &str) -> String {
    let mut md = String::new();
    md.push_str(&format!("# {}\n\n", title));
    md.push_str("*Generated from spec file*\n\n");

    let mut in_doc_block = false;
    let mut doc_lines: Vec<String> = Vec::new();
    let mut current_section: Option<String> = None;
    let mut examples: Vec<(String, String)> = Vec::new();

    for line in content.lines() {
        let trimmed = line.trim();

        // Handle doc blocks
        if trimmed == "\"\"\"" {
            if in_doc_block {
                // End of doc block
                if !doc_lines.is_empty() {
                    let doc_text = doc_lines.join("\n");
                    if current_section.is_some() {
                        md.push_str(&doc_text);
                        md.push_str("\n\n");
                    }
                    doc_lines.clear();
                }
                in_doc_block = false;
            } else {
                in_doc_block = true;
            }
            continue;
        }

        if in_doc_block {
            doc_lines.push(line.to_string());
            continue;
        }

        // Handle /// comments
        if trimmed.starts_with("///") {
            let doc_line = trimmed.trim_start_matches("///").trim();
            doc_lines.push(doc_line.to_string());
            continue;
        }

        // Handle describe/context/it blocks
        if let Some(name) = extract_block_name(trimmed, "describe") {
            if !doc_lines.is_empty() {
                md.push_str(&doc_lines.join("\n"));
                md.push_str("\n\n");
                doc_lines.clear();
            }
            md.push_str(&format!("## {}\n\n", name));
            current_section = Some(name);
        } else if let Some(name) = extract_block_name(trimmed, "context") {
            if !doc_lines.is_empty() {
                md.push_str(&doc_lines.join("\n"));
                md.push_str("\n\n");
                doc_lines.clear();
            }
            md.push_str(&format!("### {}\n\n", name));
        } else if let Some(name) = extract_block_name(trimmed, "it") {
            if !doc_lines.is_empty() {
                md.push_str(&doc_lines.join("\n"));
                md.push_str("\n\n");
                doc_lines.clear();
            }
            md.push_str(&format!("- **{}**\n", name));
        } else if let Some(name) = extract_block_name(trimmed, "test") {
            if !doc_lines.is_empty() {
                md.push_str(&doc_lines.join("\n"));
                md.push_str("\n\n");
                doc_lines.clear();
            }
            md.push_str(&format!("- **{}**\n", name));
        }

        // Clear doc lines if we hit non-doc content
        if !trimmed.is_empty() && !trimmed.starts_with("#") && !trimmed.starts_with("///") {
            doc_lines.clear();
        }
    }

    // Append any remaining doc content
    if !doc_lines.is_empty() {
        md.push_str(&doc_lines.join("\n"));
        md.push_str("\n");
    }

    md
}

fn extract_block_name(line: &str, keyword: &str) -> Option<String> {
    let prefix = format!("{} ", keyword);
    let rest = line.strip_prefix(&prefix)?;
    let rest = rest.trim();
    if rest.starts_with('"') {
        let end = rest[1..].find('"')?;
        Some(rest[1..=end].to_string())
    } else {
        None
    }
}

fn title_case(s: &str) -> String {
    s.split('_')
        .map(|word| {
            let mut chars = word.chars();
            match chars.next() {
                Some(first) => format!("{}{}", first.to_uppercase(), chars.as_str()),
                None => String::new(),
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

/// Run todo-scan command
pub fn run_todo_scan(args: &[String]) -> i32 {
    let db_path = args
        .iter()
        .position(|a| a == "--db")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("doc/todo/todo_db.sdn"));

    let scan_path = args
        .iter()
        .position(|a| a == "--path")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("."));

    let validate_only = args.contains(&"--validate".to_string());
    let incremental = args.contains(&"--incremental".to_string());
    let parallel = args.contains(&"--parallel".to_string());

    if incremental {
        println!("Scanning TODOs from {} (incremental mode)...", scan_path.display());
    } else if parallel {
        println!("Scanning TODOs from {} (parallel mode)...", scan_path.display());
    } else {
        println!("Scanning TODOs from {}...", scan_path.display());
    }

    // Load existing database
    let mut db = match load_todo_db(&db_path) {
        Ok(db) => db,
        Err(e) => {
            eprintln!("warning: failed to load existing database: {}", e);
            eprintln!("Creating new database...");
            crate::todo_db::TodoDb::new()
        }
    };

    // Scan and update with incremental/parallel support
    match update_todo_db_incremental_parallel(&mut db, &scan_path, incremental, parallel) {
        Ok((added, updated, removed)) => {
            println!("Scan complete:");
            println!("  Added:   {} TODOs", added);
            println!("  Updated: {} TODOs", updated);
            println!("  Removed: {} TODOs", removed);
            println!("  Total:   {} TODOs", db.valid_records().len());

            if !validate_only {
                // Save database
                if let Err(e) = save_todo_db(&db_path, &db) {
                    eprintln!("error: failed to save database: {}", e);
                    return 1;
                }
                println!("Database saved to {}", db_path.display());

                // Auto-generate docs (like feature system)
                let output_dir = std::path::PathBuf::from("doc");
                match generate_todo_docs(&db, &output_dir) {
                    Ok(_) => {
                        println!("Generated docs to {}/TODO.md", output_dir.display());
                    }
                    Err(e) => {
                        eprintln!("warning: failed to generate docs: {}", e);
                        eprintln!("  Run 'simple todo-gen' to retry");
                    }
                }
            } else {
                println!("Validation only - database and docs not updated");
            }

            0
        }
        Err(e) => {
            eprintln!("error: failed to scan: {}", e);
            1
        }
    }
}

/// Run todo-gen command
pub fn run_todo_gen(args: &[String]) -> i32 {
    let db_path = args
        .iter()
        .position(|a| a == "--db")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("doc/todo/todo_db.sdn"));

    let output_dir = args
        .iter()
        .position(|a| a == "-o" || a == "--output")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("doc"));

    println!("Generating TODO docs from {}...", db_path.display());

    let db = match load_todo_db(&db_path) {
        Ok(db) => db,
        Err(e) => {
            eprintln!("error: failed to load TODO database: {}", e);
            return 1;
        }
    };

    if let Err(e) = generate_todo_docs(&db, &output_dir) {
        eprintln!("error: failed to generate docs: {}", e);
        return 1;
    }

    let count = db.valid_records().len();
    println!("Generated docs for {} TODOs", count);
    println!("  -> {}/TODO.md", output_dir.display());

    0
}

/// Run test-result-gen command
pub fn run_test_result_gen(args: &[String]) -> i32 {
    let db_path = args
        .iter()
        .position(|a| a == "--db")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("doc/test/test_db.sdn"));

    let output_dir = args
        .iter()
        .position(|a| a == "-o" || a == "--output")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("doc/test"));

    println!("Generating test result docs from {}...", db_path.display());

    let db = match load_test_db(&db_path) {
        Ok(db) => db,
        Err(e) => {
            eprintln!("error: failed to load test database: {}", e);
            return 1;
        }
    };

    if let Err(e) = generate_test_result_docs(&db, &output_dir) {
        eprintln!("error: failed to generate docs: {}", e);
        return 1;
    }

    let count = db.valid_records().len();
    println!("Generated test result docs for {} tests", count);
    println!("  -> {}/test_result.md", output_dir.display());

    0
}

/// Run bug-add command
pub fn run_bug_add(args: &[String]) -> i32 {
    let db_path = args
        .iter()
        .position(|a| a == "--db")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("doc/bug/bug_db.sdn"));

    // Parse arguments
    let bug_id = match args.iter().position(|a| a == "--id").and_then(|i| args.get(i + 1)) {
        Some(id) => id.to_string(),
        None => {
            eprintln!("error: --id is required");
            return 1;
        }
    };

    let title = match args.iter().position(|a| a == "--title").and_then(|i| args.get(i + 1)) {
        Some(t) => t.to_string(),
        None => {
            eprintln!("error: --title is required");
            return 1;
        }
    };

    let description = args
        .iter()
        .position(|a| a == "--description")
        .and_then(|i| args.get(i + 1))
        .map(|s| s.to_string())
        .unwrap_or_default();

    let reproducible_by: Vec<String> = args
        .iter()
        .position(|a| a == "--reproducible-by")
        .and_then(|i| args.get(i + 1))
        .map(|s| s.split(',').map(|t| t.trim().to_string()).collect())
        .unwrap_or_default();

    let priority = args
        .iter()
        .position(|a| a == "--priority")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| match s.as_str() {
            "P0" => Some(Priority::P0),
            "P1" => Some(Priority::P1),
            "P2" => Some(Priority::P2),
            "P3" => Some(Priority::P3),
            _ => None,
        })
        .unwrap_or(Priority::P2);

    let severity = args
        .iter()
        .position(|a| a == "--severity")
        .and_then(|i| args.get(i + 1))
        .and_then(|s| match s.as_str() {
            "critical" => Some(Severity::Critical),
            "major" => Some(Severity::Major),
            "minor" => Some(Severity::Minor),
            "trivial" => Some(Severity::Trivial),
            _ => None,
        })
        .unwrap_or(Severity::Minor);

    // Load database
    let mut db = match load_bug_db(&db_path) {
        Ok(db) => db,
        Err(e) => {
            eprintln!("warning: failed to load existing database: {}", e);
            eprintln!("Creating new database...");
            crate::bug_db::BugDb::new()
        }
    };

    // Add bug
    if let Err(e) = add_bug(
        &mut db,
        bug_id.clone(),
        title,
        description,
        reproducible_by,
        priority,
        severity,
    ) {
        eprintln!("error: {}", e);
        return 1;
    }

    // Save database
    if let Err(e) = save_bug_db(&db_path, &db) {
        eprintln!("error: failed to save database: {}", e);
        return 1;
    }

    println!("Bug {} added successfully", bug_id);
    println!("Database saved to {}", db_path.display());

    0
}

/// Run bug-gen command
pub fn run_bug_gen(args: &[String]) -> i32 {
    let db_path = args
        .iter()
        .position(|a| a == "--db")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("doc/bug/bug_db.sdn"));

    let output_dir = args
        .iter()
        .position(|a| a == "-o" || a == "--output")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("doc/bug"));

    println!("Generating bug report from {}...", db_path.display());

    let db = match load_bug_db(&db_path) {
        Ok(db) => db,
        Err(e) => {
            eprintln!("error: failed to load bug database: {}", e);
            return 1;
        }
    };

    if let Err(e) = generate_bug_report(&db, &output_dir) {
        eprintln!("error: failed to generate report: {}", e);
        return 1;
    }

    let count = db.valid_records().len();
    println!("Generated bug report for {} bugs", count);
    println!("  -> {}/bug_report.md", output_dir.display());

    0
}

/// Run bug-update command
pub fn run_bug_update(args: &[String]) -> i32 {
    let db_path = args
        .iter()
        .position(|a| a == "--db")
        .and_then(|i| args.get(i + 1))
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("doc/bug/bug_db.sdn"));

    let bug_id = match args.iter().position(|a| a == "--id").and_then(|i| args.get(i + 1)) {
        Some(id) => id,
        None => {
            eprintln!("error: --id is required");
            return 1;
        }
    };

    let status = match args.iter().position(|a| a == "--status").and_then(|i| args.get(i + 1)) {
        Some(s) => match s.as_str() {
            "open" => BugStatus::Open,
            "in_progress" | "in-progress" => BugStatus::InProgress,
            "fixed" => BugStatus::Fixed,
            "closed" => BugStatus::Closed,
            "wontfix" | "wont-fix" => BugStatus::WontFix,
            _ => {
                eprintln!("error: invalid status: {}", s);
                eprintln!("Valid statuses: open, in_progress, fixed, closed, wontfix");
                return 1;
            }
        },
        None => {
            eprintln!("error: --status is required");
            return 1;
        }
    };

    // Load database
    let mut db = match load_bug_db(&db_path) {
        Ok(db) => db,
        Err(e) => {
            eprintln!("error: failed to load database: {}", e);
            return 1;
        }
    };

    // Update status or mark as fixed
    if status == BugStatus::Fixed {
        let commit = args
            .iter()
            .position(|a| a == "--commit")
            .and_then(|i| args.get(i + 1))
            .map(|s| s.to_string())
            .unwrap_or_else(|| "unknown".to_string());

        let verified_by: Vec<String> = args
            .iter()
            .position(|a| a == "--verified-by")
            .and_then(|i| args.get(i + 1))
            .map(|s| s.split(',').map(|t| t.trim().to_string()).collect())
            .unwrap_or_default();

        if let Err(e) = mark_bug_fixed(&mut db, bug_id, commit, verified_by) {
            eprintln!("error: {}", e);
            return 1;
        }
    } else {
        if let Err(e) = update_bug_status(&mut db, bug_id, status) {
            eprintln!("error: {}", e);
            return 1;
        }
    }

    // Save database
    if let Err(e) = save_bug_db(&db_path, &db) {
        eprintln!("error: failed to save database: {}", e);
        return 1;
    }

    println!("Bug {} updated to status: {:?}", bug_id, status);
    println!("Database saved to {}", db_path.display());

    0
}

/// Print help for doc generation commands
pub fn print_doc_gen_help() {
    eprintln!("Documentation Generation Commands");
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  simple feature-gen [options]      - Generate feature docs from feature_db.sdn");
    eprintln!("  simple task-gen [options]         - Generate task docs from task_db.sdn");
    eprintln!("  simple spec-gen [options]         - Generate spec docs from *_spec.spl files");
    eprintln!("  simple todo-scan [options]        - Scan source code and update todo_db.sdn");
    eprintln!("  simple todo-gen [options]         - Generate TODO.md from todo_db.sdn");
    eprintln!("  simple test-result-gen [options]  - Generate test_result.md from test_db.sdn");
    eprintln!("  simple bug-add [options]          - Add a new bug");
    eprintln!("  simple bug-gen [options]          - Generate bug_report.md from bug_db.sdn");
    eprintln!("  simple bug-update [options]       - Update bug status");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  --db <path>              Input database file");
    eprintln!("  --input <path>           Input directory (spec-gen)");
    eprintln!("  --path <path>            Scan directory (todo-scan, default: .)");
    eprintln!("  --validate               Validate only, don't update database (todo-scan)");
    eprintln!("  -o, --output <path>      Output directory");
    eprintln!();
    eprintln!("  Bug-specific options:");
    eprintln!("  --id <bug_id>            Bug ID (required for bug-add, bug-update)");
    eprintln!("  --title <title>          Bug title (required for bug-add)");
    eprintln!("  --description <desc>     Bug description");
    eprintln!("  --reproducible-by <ids>  Comma-separated test IDs (required for bug-add)");
    eprintln!("  --priority <P0-P3>       Bug priority (default: P2)");
    eprintln!("  --severity <level>       Bug severity: critical, major, minor, trivial");
    eprintln!("  --status <status>        Bug status: open, in_progress, fixed, closed, wontfix");
    eprintln!("  --commit <hash>          Commit hash (for --status=fixed)");
    eprintln!("  --verified-by <ids>      Comma-separated test IDs that verify fix");
    eprintln!();
    eprintln!("Defaults:");
    eprintln!("  feature-gen:     doc/feature/feature_db.sdn -> doc/feature/");
    eprintln!("  task-gen:        doc/task/task_db.sdn -> doc/task/");
    eprintln!("  spec-gen:        tests/spec/ -> doc/spec/generated/");
    eprintln!("  todo-scan:       . -> doc/todo/todo_db.sdn");
    eprintln!("  todo-gen:        doc/todo/todo_db.sdn -> doc/TODO.md");
    eprintln!("  test-result-gen: doc/test/test_db.sdn -> doc/test/");
    eprintln!("  bug-add/update:  doc/bug/bug_db.sdn");
    eprintln!("  bug-gen:         doc/bug/bug_db.sdn -> doc/bug/");
}

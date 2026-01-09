//! Documentation generation commands.
//!
//! Commands:
//! - `simple feature-gen` - Generate feature.md from feature_db.sdn
//! - `simple task-gen` - Generate task.md from task_db.sdn
//! - `simple spec-gen` - Generate doc/spec/ from tests/spec/*_spec.spl

use std::fs;
use std::path::{Path, PathBuf};

use simple_driver::feature_db::{generate_feature_docs, load_feature_db};
use simple_driver::task_db::{generate_task_docs, load_task_db};

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

/// Print help for doc generation commands
pub fn print_doc_gen_help() {
    eprintln!("Documentation Generation Commands");
    eprintln!();
    eprintln!("Usage:");
    eprintln!("  simple feature-gen [options]  - Generate feature docs from feature_db.sdn");
    eprintln!("  simple task-gen [options]     - Generate task docs from task_db.sdn");
    eprintln!("  simple spec-gen [options]     - Generate spec docs from *_spec.spl files");
    eprintln!();
    eprintln!("Options:");
    eprintln!("  --db <path>       Input database file (feature-gen, task-gen)");
    eprintln!("  --input <path>    Input directory (spec-gen)");
    eprintln!("  -o, --output <path>  Output directory");
    eprintln!();
    eprintln!("Defaults:");
    eprintln!("  feature-gen: doc/feature/feature_db.sdn -> doc/feature/");
    eprintln!("  task-gen:    doc/task/task_db.sdn -> doc/task/");
    eprintln!("  spec-gen:    tests/spec/ -> doc/spec/generated/");
}

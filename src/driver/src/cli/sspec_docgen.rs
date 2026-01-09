// sspec documentation generator
//
// Extracts markdown documentation from sspec test files ("""...""" blocks)
// and generates BDD-style documentation in docs/spec/

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

/// Documentation block extracted from sspec file
#[derive(Debug, Clone)]
pub struct DocBlock {
    pub content: String,
    pub line_start: usize,
    pub line_end: usize,
}

/// Parsed sspec file with documentation and test structure
#[derive(Debug)]
pub struct SspecDoc {
    pub file_path: PathBuf,
    pub doc_blocks: Vec<DocBlock>,
    pub feature_title: Option<String>,
    pub feature_ids: Vec<String>,
}

/// Parse sspec file and extract documentation blocks
pub fn parse_sspec_file(path: &Path) -> Result<SspecDoc, Box<dyn std::error::Error>> {
    let content = fs::read_to_string(path)?;
    let lines: Vec<&str> = content.lines().collect();
    
    let mut doc_blocks = Vec::new();
    let mut feature_title = None;
    let mut feature_ids = Vec::new();
    
    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim();
        
        if line.starts_with("#[id(") {
            if let Some(id) = parse_id_attr(line) {
                feature_ids.push(id);
            }
        }

        // Check for doc block start
        if line == "\"\"\"" {
            let start_line = i;
            i += 1;
            
            let mut block_content = String::new();
            let mut found_end = false;
            
            // Collect lines until closing """
            while i < lines.len() {
                let block_line = lines[i];
                
                if block_line.trim() == "\"\"\"" {
                    found_end = true;
                    break;
                }
                
                block_content.push_str(block_line);
                block_content.push('\n');
                i += 1;
            }
            
            if found_end {
                // Extract feature title from first doc block if present
                if feature_title.is_none() && block_content.contains("# ") {
                    if let Some(title_line) = block_content.lines().find(|l| l.trim().starts_with("# ")) {
                        feature_title = Some(title_line.trim().trim_start_matches('#').trim().to_string());
                    }
                }
                
                doc_blocks.push(DocBlock {
                    content: block_content.trim().to_string(),
                    line_start: start_line,
                    line_end: i,
                });
            }
        }
        
        i += 1;
    }
    
    Ok(SspecDoc {
        file_path: path.to_path_buf(),
        doc_blocks,
        feature_title,
        feature_ids,
    })
}

/// Generate markdown documentation from sspec files
pub fn generate_sspec_docs(
    sspec_files: &[PathBuf],
    output_dir: &Path,
) -> Result<(), Box<dyn std::error::Error>> {
    fs::create_dir_all(output_dir)?;
    
    // Parse all sspec files
    let mut parsed_files = Vec::new();
    for file_path in sspec_files {
        match parse_sspec_file(file_path) {
            Ok(parsed) => parsed_files.push(parsed),
            Err(e) => eprintln!("Warning: Failed to parse {}: {}", file_path.display(), e),
        }
    }
    
    // Generate individual feature docs
    for sspec_doc in &parsed_files {
        generate_feature_doc(sspec_doc, output_dir)?;
    }
    
    // Generate index page
    generate_index_page(&parsed_files, output_dir)?;
    
    Ok(())
}

/// Generate documentation for a single feature
fn generate_feature_doc(
    sspec_doc: &SspecDoc,
    output_dir: &Path,
) -> Result<(), Box<dyn std::error::Error>> {
    let file_name = sspec_doc
        .file_path
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("unknown");
    
    let feature_name = sspec_doc
        .feature_title
        .as_deref()
        .unwrap_or(file_name);
    
    let mut md = String::new();
    
    // Add header
    md.push_str(&format!("# {}\n\n", feature_name));
    md.push_str(&format!(
        "*Source: `{}`*\n\n",
        sspec_doc.file_path.display()
    ));
    if !sspec_doc.feature_ids.is_empty() {
        md.push_str("## Feature IDs\n\n");
        for id in &sspec_doc.feature_ids {
            let anchor = id.replace('.', "-");
            md.push_str(&format!("- <a id=\"feature-{}\"></a>{}\n", anchor, id));
        }
        md.push_str("\n");
    }
    md.push_str("---\n\n");
    
    // Add all documentation blocks
    for (idx, doc_block) in sspec_doc.doc_blocks.iter().enumerate() {
        if idx > 0 {
            md.push_str("\n");
        }
        md.push_str(&doc_block.content);
        md.push_str("\n");
    }
    
    // Write to file
    let output_path = output_dir.join(format!("{}.md", file_name));
    let mut file = fs::File::create(output_path)?;
    file.write_all(md.as_bytes())?;
    
    Ok(())
}

fn parse_id_attr(line: &str) -> Option<String> {
    let line = line.trim_start_matches("#[id(").trim_end_matches(")]").trim();
    if line.starts_with('"') && line.ends_with('"') && line.len() >= 2 {
        Some(line[1..line.len() - 1].to_string())
    } else {
        None
    }
}

/// Generate index page for all features
fn generate_index_page(
    parsed_files: &[SspecDoc],
    output_dir: &Path,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut md = String::new();
    
    md.push_str("# Test Specification Index\n\n");
    md.push_str(&format!(
        "*Generated: {}*\n\n",
        chrono::Local::now().format("%Y-%m-%d %H:%M:%S")
    ));
    md.push_str("## Features\n\n");
    
    for sspec_doc in parsed_files {
        let file_name = sspec_doc
            .file_path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown");
        
        let feature_name = sspec_doc
            .feature_title
            .as_deref()
            .unwrap_or(file_name);
        
        md.push_str(&format!(
            "- [{}]({}.md)\n",
            feature_name, file_name
        ));
    }
    
    // Write to file
    let output_path = output_dir.join("INDEX.md");
    let mut file = fs::File::create(output_path)?;
    file.write_all(md.as_bytes())?;
    
    Ok(())
}

//! Parser for extracting documentation from SSpec files

use std::fs;
use std::path::Path;

use super::types::{DocBlock, SspecDoc};

/// Parse sspec file and extract documentation blocks
pub fn parse_sspec_file(path: &Path) -> Result<SspecDoc, Box<dyn std::error::Error>> {
    let content = fs::read_to_string(path)?;
    let lines: Vec<&str> = content.lines().collect();

    let mut doc_blocks = Vec::new();
    let mut feature_title = None;
    let mut feature_ids = Vec::new();

    // Pre-scan: Extract comment-based documentation (# ## Section pattern)
    // Many feature specs use comment-based docs instead of """ blocks.
    let mut comment_doc_lines: Vec<String> = Vec::new();
    let mut comment_scan_i = 0;
    // Skip leading blank lines
    while comment_scan_i < lines.len() && lines[comment_scan_i].trim().is_empty() {
        comment_scan_i += 1;
    }
    // Collect consecutive comment lines
    while comment_scan_i < lines.len() {
        let cline = lines[comment_scan_i].trim();
        if cline.starts_with("# ") && !cline.starts_with("#[") {
            comment_doc_lines.push(cline[2..].to_string());
        } else if cline == "#" {
            comment_doc_lines.push(String::new());
        } else {
            break;
        }
        comment_scan_i += 1;
    }

    // If comment docs contain markdown structure, synthesize a DocBlock
    if !comment_doc_lines.is_empty() {
        let comment_content = comment_doc_lines.join("\n").trim().to_string();
        if comment_content.contains("## ") || comment_content.contains("**Category:**") {
            // Extract feature title from "# Title" pattern
            if feature_title.is_none() {
                for cl in &comment_doc_lines {
                    let cl_trimmed = cl.trim();
                    if cl_trimmed.starts_with("# ") {
                        feature_title = Some(cl_trimmed[2..].trim().to_string());
                        break;
                    }
                }
            }

            doc_blocks.push(DocBlock {
                content: comment_content,
                line_start: 0,
                line_end: comment_scan_i,
            });
        }
    }

    let mut i = 0;
    while i < lines.len() {
        let line = lines[i].trim();

        // Extract feature IDs from #[id(...)] attributes
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
        raw_content: content,
        doc_blocks,
        feature_title,
        feature_ids,
        metadata: Default::default(), // Will be extracted by metadata module
    })
}

/// Parse #[id("...")] attribute to extract ID
fn parse_id_attr(line: &str) -> Option<String> {
    let line = line.trim_start_matches("#[id(").trim_end_matches(")]").trim();
    if line.starts_with('"') && line.ends_with('"') && line.len() >= 2 {
        Some(line[1..line.len() - 1].to_string())
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_id_attr() {
        assert_eq!(parse_id_attr("#[id(\"feature.20\")]"), Some("feature.20".to_string()));
        assert_eq!(parse_id_attr("#[id(\"test\")]"), Some("test".to_string()));
        assert_eq!(parse_id_attr("#[invalid]"), None);
    }
}

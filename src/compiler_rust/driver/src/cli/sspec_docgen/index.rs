//! INDEX.md generation with categorization

use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};

use super::generator::output_stem;
use super::types::{DocStats, SspecDoc, ValidationResult};

/// Category of features
struct Category {
    name: String,
    features: Vec<FeatureEntry>,
}

/// Single feature entry for INDEX
struct FeatureEntry {
    title: String,
    filename: String,
    status: String,
    docs_status: String,
    difficulty: String,
    test_count: usize,
    summary: String,
}

/// Generate INDEX.md with categorization and metadata
pub fn generate_index_page(
    parsed_files: &[(SspecDoc, ValidationResult)],
    output_dir: &Path,
    stats: &DocStats,
) -> Result<(), Box<dyn std::error::Error>> {
    let mut md = String::new();

    // Header
    md.push_str("# Test Specification Index\n\n");
    md.push_str(&format!(
        "*Generated: {}*\n\n",
        chrono::Local::now().format("%Y-%m-%d %H:%M:%S")
    ));

    // Quick stats
    md.push_str("## Quick Stats\n\n");
    md.push_str(&format!("- **Total Features:** {}\n", stats.total_specs));
    md.push_str(&format!(
        "- **Complete Documentation:** {} ({:.0}%)\n",
        stats.specs_with_docs,
        stats.coverage_percent()
    ));
    md.push_str(&format!("- **Stubs Remaining:** {}\n", stats.specs_without_docs));
    md.push_str(&format!("- **Total Lines:** {}\n", stats.total_doc_lines));
    if stats.total_warnings > 0 {
        md.push_str(&format!("- **Warnings:** {}\n", stats.total_warnings));
    }
    md.push_str("\n---\n\n");

    // Group by category
    let categories = group_by_category(parsed_files);
    let unmanaged_files = find_unmanaged_files(parsed_files, output_dir)?;

    // Generate categorized tables
    for category in categories {
        md.push_str(&format!(
            "## {} ({} features)\n\n",
            category.name,
            category.features.len()
        ));
        md.push_str("| Feature | Status | Docs | Difficulty | Tests | Summary |\n");
        md.push_str("|---------|--------|------|------------|-------|---------|\n");

        for feature in category.features {
            md.push_str(&format!(
                "| [{}]({}) | {} | {} | {} | {} | {} |\n",
                feature.title,
                feature.filename,
                feature.status,
                feature.docs_status,
                feature.difficulty,
                feature.test_count,
                escape_table_cell(&feature.summary)
            ));
        }
        md.push('\n');
    }

    if !unmanaged_files.is_empty() {
        md.push_str("## Residual Files\n\n");
        md.push_str(
            "These files are present in `doc/06_spec` but were not regenerated in this run.\n\n",
        );
        md.push_str("| File | Type |\n");
        md.push_str("|------|------|\n");
        for path in unmanaged_files {
            let file_name = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("unknown");
            let file_type = path
                .extension()
                .and_then(|ext| ext.to_str())
                .map(classify_residual_file)
                .unwrap_or("Artifact");
            md.push_str(&format!("| {} | {} |\n", file_name, file_type));
        }
        md.push('\n');
    }

    for file_name in ["INDEX.md", "README.md"] {
        let output_path = output_dir.join(file_name);
        let mut file = fs::File::create(output_path)?;
        file.write_all(md.as_bytes())?;
    }

    Ok(())
}

fn find_unmanaged_files(
    parsed_files: &[(SspecDoc, ValidationResult)],
    output_dir: &Path,
) -> Result<Vec<PathBuf>, Box<dyn std::error::Error>> {
    let mut managed = std::collections::HashSet::new();
    managed.insert("INDEX.md".to_string());
    managed.insert("README.md".to_string());

    for (sspec_doc, _) in parsed_files {
        managed.insert(format!("{}.md", output_stem(sspec_doc)));
    }

    let mut unmanaged = Vec::new();
    for entry in fs::read_dir(output_dir)? {
        let entry = entry?;
        let path = entry.path();
        if !path.is_file() {
            continue;
        }

        let file_name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or_default()
            .to_string();

        if file_name == ".gitkeep" || managed.contains(&file_name) {
            continue;
        }

        unmanaged.push(path);
    }

    unmanaged.sort();
    Ok(unmanaged)
}

fn classify_residual_file(extension: &str) -> &'static str {
    match extension {
        "md" => "Legacy markdown",
        "sdn" => "Data/config artifact",
        other if !other.is_empty() => "Residual artifact",
        _ => "Artifact",
    }
}

/// Group specs by category
fn group_by_category(parsed_files: &[(SspecDoc, ValidationResult)]) -> Vec<Category> {
    let mut category_map: HashMap<String, Vec<FeatureEntry>> = HashMap::new();

    for (sspec_doc, validation) in parsed_files {
        // Determine category
        let category_name = if let Some(ref cat) = sspec_doc.metadata.category {
            cat.clone()
        } else {
            // Infer from file path
            infer_category_from_path(&sspec_doc.file_path)
        };

        // Create feature entry
        let file_name = output_stem(sspec_doc);

        let title = sspec_doc
            .feature_title
            .clone()
            .filter(|title| {
                let trimmed = title.trim();
                !trimmed.is_empty()
                    && !trimmed.starts_with('-')
                    && trimmed != "Test Specification"
                    && trimmed != "- Test Specification"
            })
            .unwrap_or_else(|| humanize_filename(&file_name));

        let status = if let Some(status) = &sspec_doc.metadata.status {
            status.clone()
        } else if validation.has_docs {
            if validation.doc_lines >= 200 {
                "✅ Complete".to_string()
            } else {
                "⚠️ Partial".to_string()
            }
        } else {
            "❌ Stub".to_string()
        };

        let difficulty = sspec_doc
            .metadata
            .difficulty
            .clone()
            .unwrap_or_else(|| "N/A".to_string());

        let entry = FeatureEntry {
            title,
            filename: format!("{}.md", file_name),
            status,
            docs_status: docs_status(validation),
            difficulty,
            test_count: count_test_cases(&sspec_doc.raw_content),
            summary: extract_summary(sspec_doc),
        };

        category_map.entry(category_name).or_default().push(entry);
    }

    // Convert to sorted vector
    let mut categories: Vec<Category> = category_map
        .into_iter()
        .map(|(name, mut features)| {
            // Sort features: complete first, then by name
            features.sort_by(|a, b| {
                let a_complete = a.status.contains('✅');
                let b_complete = b.status.contains('✅');
                match (a_complete, b_complete) {
                    (true, false) => std::cmp::Ordering::Less,
                    (false, true) => std::cmp::Ordering::Greater,
                    _ => a.title.cmp(&b.title),
                }
            });
            Category { name, features }
        })
        .collect();

    // Sort categories alphabetically
    categories.sort_by(|a, b| a.name.cmp(&b.name));

    categories
}

/// Infer category from file path
fn infer_category_from_path(path: &std::path::Path) -> String {
    // Try to extract category from path like "test/features/infrastructure/ast_spec.spl"
    let path_str = path.to_string_lossy();

    if path_str.contains("/infrastructure/") {
        "Infrastructure".to_string()
    } else if path_str.contains("/language/") {
        "Language Features".to_string()
    } else if path_str.contains("/types/") {
        "Type System".to_string()
    } else if path_str.contains("/data_structures/") {
        "Data Structures".to_string()
    } else if path_str.contains("/control_flow/") {
        "Control Flow".to_string()
    } else if path_str.contains("/concurrency/") {
        "Concurrency".to_string()
    } else if path_str.contains("/codegen/") {
        "Code Generation".to_string()
    } else if path_str.contains("/testing_framework/") {
        "Testing Framework".to_string()
    } else if path_str.contains("/stdlib/") {
        "Standard Library".to_string()
    } else if path_str.contains("/ml/") {
        "ML/AI Infrastructure".to_string()
    } else if path_str.contains("/syntax/") {
        "Syntax Features".to_string()
    } else {
        "Other".to_string()
    }
}

fn humanize_filename(stem: &str) -> String {
    let base = stem.strip_suffix("_spec").unwrap_or(stem);
    let words: Vec<String> = base
        .split('_')
        .filter(|w| !w.is_empty())
        .map(|word| {
            let mut chars = word.chars();
            match chars.next() {
                Some(first) => format!("{}{}", first.to_ascii_uppercase(), chars.as_str()),
                None => String::new(),
            }
        })
        .collect();

    if words.is_empty() {
        "Specification".to_string()
    } else {
        format!("{} Specification", words.join(" "))
    }
}

fn count_test_cases(content: &str) -> usize {
    content
        .lines()
        .filter(|line| {
            let trimmed = line.trim();
            trimmed.starts_with("it ")
                || trimmed.starts_with("slow_it ")
                || trimmed.starts_with("skip_it ")
                || trimmed.starts_with("pending ")
        })
        .count()
}

fn docs_status(validation: &ValidationResult) -> String {
    if !validation.has_docs {
        "Stub".to_string()
    } else if validation.warnings.is_empty() && validation.doc_lines >= 100 {
        "Healthy".to_string()
    } else if validation.doc_lines >= 50 {
        "Needs detail".to_string()
    } else {
        "Thin".to_string()
    }
}

fn extract_summary(sspec_doc: &SspecDoc) -> String {
    let body = render_doc_body(sspec_doc);
    let summary = extract_summary_from_markdown(&body)
        .unwrap_or_else(|| "Summary not provided in the doc blocks.".to_string());
    truncate_summary(&summary, 120)
}

fn render_doc_body(sspec_doc: &SspecDoc) -> String {
    let mut sections = Vec::new();

    if let Some(first_block) = sspec_doc.doc_blocks.first() {
        let first = strip_header_metadata(&first_block.content);
        if !first.is_empty() {
            sections.push(first);
        }
        for block in sspec_doc.doc_blocks.iter().skip(1) {
            let content = block.content.trim();
            if !content.is_empty() {
                sections.push(content.to_string());
            }
        }
    }

    sections.join("\n\n")
}

fn strip_header_metadata(content: &str) -> String {
    let mut out = Vec::new();
    let mut skipping_leading_blanks = true;
    let mut skipping_metadata_list = false;

    for line in content.lines() {
        let trimmed = line.trim();
        let is_metadata = trimmed.starts_with("**Feature ID:**")
            || trimmed.starts_with("**Feature IDs:**")
            || trimmed.starts_with("**Category:**")
            || trimmed.starts_with("**Difficulty:**")
            || trimmed.starts_with("**Status:**")
            || trimmed.starts_with("**Source:**")
            || trimmed.starts_with("**Type:**")
            || trimmed.starts_with("**Requirements:**")
            || trimmed.starts_with("**Plan:**")
            || trimmed.starts_with("**Design:**")
            || trimmed.starts_with("**Research:**")
            || trimmed.starts_with("**Related:**")
            || trimmed.starts_with("**Dependencies:**")
            || trimmed.starts_with("**Artifacts:**")
            || trimmed.starts_with("**Screenshots:**")
            || trimmed.starts_with("**TUI Captures:**")
            || trimmed.starts_with("**Logs:**");

        if trimmed.starts_with("# ") || is_metadata {
            skipping_metadata_list = is_metadata;
            continue;
        }

        if skipping_metadata_list {
            if trimmed.starts_with("- ") || trimmed.starts_with("* ") {
                continue;
            }
            if trimmed.is_empty() {
                continue;
            }
            skipping_metadata_list = false;
        }

        if skipping_leading_blanks && trimmed.is_empty() {
            continue;
        }

        skipping_leading_blanks = false;
        out.push(line);
    }

    out.join("\n").trim().to_string()
}

fn extract_summary_from_markdown(content: &str) -> Option<String> {
    let mut in_overview = false;
    let mut paragraph = Vec::new();

    for line in content.lines() {
        let trimmed = line.trim();

        if trimmed.starts_with("## ") {
            in_overview = trimmed == "## Overview" || trimmed == "## Description";
            if !paragraph.is_empty() {
                break;
            }
            continue;
        }

        if trimmed.starts_with('#') || trimmed.starts_with("```") {
            if !paragraph.is_empty() {
                break;
            }
            continue;
        }

        if is_metadata_line(trimmed) {
            if !paragraph.is_empty() {
                break;
            }
            continue;
        }

        if trimmed.is_empty() {
            if !paragraph.is_empty() {
                break;
            }
            continue;
        }

        if in_overview || paragraph.is_empty() {
            if !trimmed.starts_with("- ") && !trimmed.starts_with("* ") {
                paragraph.push(trimmed.to_string());
            }
        }
    }

    if paragraph.is_empty() {
        None
    } else {
        Some(paragraph.join(" "))
    }
}

fn is_metadata_line(trimmed: &str) -> bool {
    trimmed.starts_with("**") && trimmed.contains(":**")
}

fn truncate_summary(summary: &str, max_len: usize) -> String {
    if summary.chars().count() <= max_len {
        return summary.to_string();
    }

    let truncated: String = summary.chars().take(max_len.saturating_sub(1)).collect();
    format!("{}…", truncated.trim_end())
}

fn escape_table_cell(value: &str) -> String {
    value.replace('|', "\\|")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;
    use std::fs;
    use std::path::PathBuf;
    use tempfile::tempdir;

    fn validation(doc_lines: usize, warnings: &[&str]) -> ValidationResult {
        ValidationResult {
            file_path: PathBuf::from("test/example_spec.spl"),
            has_docs: doc_lines > 0,
            doc_lines,
            has_sections: HashSet::new(),
            warnings: warnings.iter().map(|s| s.to_string()).collect(),
        }
    }

    #[test]
    fn test_docs_status_prefers_quality_labels() {
        assert_eq!(docs_status(&validation(0, &[])), "Stub");
        assert_eq!(docs_status(&validation(40, &["short"])), "Thin");
        assert_eq!(docs_status(&validation(80, &["short"])), "Needs detail");
        assert_eq!(docs_status(&validation(120, &[])), "Healthy");
    }

    #[test]
    fn test_extract_summary_prefers_overview_paragraph() {
        let doc = SspecDoc {
            file_path: PathBuf::from("test/example_spec.spl"),
            raw_content: String::new(),
            doc_blocks: vec![super::super::types::DocBlock {
                content: r#"
# Example

**Status:** Implemented

## Overview

This summary should appear in the generated index before any code examples.

## Examples

```simple
expect(true).to_equal(true)
```
"#
                .trim()
                .to_string(),
                line_start: 0,
                line_end: 14,
            }],
            feature_title: Some("Example".to_string()),
            feature_ids: vec![],
            metadata: Default::default(),
        };

        assert_eq!(
            extract_summary(&doc),
            "This summary should appear in the generated index before any code examples."
        );
    }

    #[test]
    fn test_index_uses_reference_filename_for_extracted_examples() {
        let doc = SspecDoc {
            file_path: PathBuf::from("test/specs/functions_spec.spl"),
            raw_content: String::new(),
            doc_blocks: vec![],
            feature_title: Some("Functions".to_string()),
            feature_ids: vec![],
            metadata: super::super::types::FeatureMetadata {
                source_doc: Some("functions.md".to_string()),
                ..Default::default()
            },
        };

        assert_eq!(output_stem(&doc), "functions");
    }

    #[test]
    fn test_find_unmanaged_files_excludes_regenerated_pages() {
        let dir = tempdir().expect("tempdir");
        fs::write(dir.path().join("functions.md"), "").expect("functions");
        fs::write(dir.path().join("shell_api.md"), "").expect("shell_api");
        fs::write(dir.path().join("feature_db.sdn"), "").expect("feature_db");
        fs::write(dir.path().join("README.md"), "").expect("readme");
        fs::write(dir.path().join("INDEX.md"), "").expect("index");

        let parsed = vec![(
            SspecDoc {
                file_path: PathBuf::from("test/specs/functions_spec.spl"),
                raw_content: String::new(),
                doc_blocks: vec![],
                feature_title: None,
                feature_ids: vec![],
                metadata: super::super::types::FeatureMetadata {
                    source_doc: Some("functions.md".to_string()),
                    ..Default::default()
                },
            },
            ValidationResult {
                file_path: PathBuf::from("test/specs/functions_spec.spl"),
                has_docs: true,
                doc_lines: 10,
                has_sections: HashSet::new(),
                warnings: vec![],
            },
        )];

        let unmanaged = find_unmanaged_files(&parsed, dir.path()).expect("unmanaged");
        let names: Vec<_> = unmanaged
            .iter()
            .map(|path| path.file_name().and_then(|name| name.to_str()).unwrap_or_default().to_string())
            .collect();

        assert_eq!(names, vec!["feature_db.sdn".to_string(), "shell_api.md".to_string()]);
    }
}

//! INDEX.md generation with categorization

use std::collections::HashMap;
use std::fs;
use std::io::Write;
use std::path::Path;

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
    difficulty: String,
    coverage: String,
    doc_lines: usize,
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

    // Generate categorized tables
    for category in categories {
        md.push_str(&format!(
            "## {} ({} features)\n\n",
            category.name,
            category.features.len()
        ));
        md.push_str("| Feature | Status | Difficulty | Coverage | Details |\n");
        md.push_str("|---------|--------|------------|----------|----------|\n");

        for feature in category.features {
            md.push_str(&format!(
                "| [{}]({}) | {} | {} | {} | {} lines |\n",
                feature.title,
                feature.filename,
                feature.status,
                feature.difficulty,
                feature.coverage,
                feature.doc_lines
            ));
        }
        md.push_str("\n");
    }

    // Write to file
    let output_path = output_dir.join("INDEX.md");
    let mut file = fs::File::create(output_path)?;
    file.write_all(md.as_bytes())?;

    Ok(())
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
        let file_name = sspec_doc
            .file_path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown");

        let title = sspec_doc.feature_title.as_deref().unwrap_or(file_name);

        let status = if validation.has_docs {
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

        let coverage = if validation.has_docs {
            format!("{}%", calculate_coverage(validation))
        } else {
            "0%".to_string()
        };

        let entry = FeatureEntry {
            title: title.to_string(),
            filename: format!("{}.md", file_name),
            status,
            difficulty,
            coverage,
            doc_lines: validation.doc_lines,
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

/// Calculate coverage percentage (simple heuristic)
fn calculate_coverage(validation: &ValidationResult) -> u32 {
    if validation.doc_lines >= 500 {
        100
    } else if validation.doc_lines >= 300 {
        90
    } else if validation.doc_lines >= 200 {
        80
    } else if validation.doc_lines >= 100 {
        60
    } else if validation.doc_lines >= 50 {
        40
    } else if validation.doc_lines > 0 {
        20
    } else {
        0
    }
}

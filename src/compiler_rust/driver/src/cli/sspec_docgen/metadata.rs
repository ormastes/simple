//! Metadata extraction from documentation blocks

use super::types::{FeatureMetadata, SspecDoc};

/// Extract metadata from documentation blocks
pub fn extract_metadata(sspec_doc: &mut SspecDoc) {
    let mut metadata = FeatureMetadata::default();

    // Concatenate all doc blocks for metadata extraction
    let full_content = sspec_doc
        .doc_blocks
        .iter()
        .map(|b| b.content.as_str())
        .collect::<Vec<&str>>()
        .join("\n");
    let lines: Vec<&str> = full_content.lines().collect();

    // Extract metadata fields from markdown
    let mut i = 0;
    while i < lines.len() {
        let trimmed = lines[i].trim();

        // Match patterns like "**Feature ID:** #20"
        if trimmed.starts_with("**Feature ID:**") {
            if let Some(id) = extract_field_value(trimmed, "**Feature ID:**") {
                metadata.id = Some(id);
            }
        } else if trimmed.starts_with("**Feature IDs:**") {
            if let Some(id) = extract_field_value(trimmed, "**Feature IDs:**") {
                metadata.id = Some(id);
            }
        } else if trimmed.starts_with("**Category:**") {
            if let Some(category) = extract_field_value(trimmed, "**Category:**") {
                metadata.category = Some(category);
            }
        } else if trimmed.starts_with("**Difficulty:**") {
            if let Some(diff) = extract_field_value(trimmed, "**Difficulty:**") {
                metadata.difficulty = Some(diff);
            }
        } else if trimmed.starts_with("**Status:**") {
            if let Some(status) = extract_field_value(trimmed, "**Status:**") {
                metadata.status = Some(status);
            }
        } else if trimmed.starts_with("**Source:**") {
            if let Some(source_doc) = extract_field_value(trimmed, "**Source:**") {
                metadata.source_doc = Some(source_doc);
            }
        } else if trimmed.starts_with("**Type:**") {
            if let Some(doc_type) = extract_field_value(trimmed, "**Type:**") {
                metadata.doc_type = Some(doc_type);
            }
        } else if trimmed.starts_with("**Requirements:**") {
            if let Some(requirements) = extract_field_value(trimmed, "**Requirements:**") {
                metadata.requirements = Some(requirements);
            }
        } else if trimmed.starts_with("**Plan:**") {
            if let Some(plan) = extract_field_value(trimmed, "**Plan:**") {
                metadata.plan = Some(plan);
            }
        } else if trimmed.starts_with("**Design:**") {
            if let Some(design) = extract_field_value(trimmed, "**Design:**") {
                metadata.design = Some(design);
            }
        } else if trimmed.starts_with("**Research:**") {
            if let Some(research) = extract_field_value(trimmed, "**Research:**") {
                metadata.research = Some(research);
            }
        } else if trimmed.starts_with("**Related:**") {
            metadata.related = extract_list_field(&lines, &mut i, "**Related:**");
        } else if trimmed.starts_with("**Dependencies:**") {
            metadata.dependencies = extract_list_field(&lines, &mut i, "**Dependencies:**");
        } else if trimmed.starts_with("**Artifacts:**") {
            metadata.artifacts = extract_list_field(&lines, &mut i, "**Artifacts:**");
        } else if trimmed.starts_with("**Screenshots:**") {
            metadata.screenshots = extract_list_field(&lines, &mut i, "**Screenshots:**");
        } else if trimmed.starts_with("**TUI Captures:**") {
            metadata.tui_captures = extract_list_field(&lines, &mut i, "**TUI Captures:**");
        } else if trimmed.starts_with("**Logs:**") {
            metadata.logs = extract_list_field(&lines, &mut i, "**Logs:**");
        }
        i += 1;
    }

    // Extract feature ID from feature_ids if metadata.id is not set
    if metadata.id.is_none() && !sspec_doc.feature_ids.is_empty() {
        metadata.id = Some(sspec_doc.feature_ids[0].clone());
    }

    sspec_doc.metadata = metadata;
}

/// Extract value from a metadata field line
fn extract_field_value(line: &str, prefix: &str) -> Option<String> {
    if let Some(value_part) = line.strip_prefix(prefix) {
        let value = value_part.trim();
        if !value.is_empty() {
            return Some(value.to_string());
        }
    }
    None
}

fn extract_list_field(lines: &[&str], index: &mut usize, prefix: &str) -> Vec<String> {
    let mut values = Vec::new();
    let current = lines[*index].trim();

    if let Some(inline) = extract_field_value(current, prefix) {
        values.extend(split_inline_list(&inline));
        return values;
    }

    let mut j = *index + 1;
    while j < lines.len() {
        let trimmed = lines[j].trim();
        if trimmed.is_empty() {
            break;
        }
        if trimmed.starts_with("**") || trimmed.starts_with("## ") || trimmed.starts_with("# ") {
            break;
        }
        if let Some(item) = trimmed.strip_prefix("- ").or_else(|| trimmed.strip_prefix("* ")) {
            let item = item.trim();
            if !item.is_empty() {
                values.push(item.to_string());
            }
            j += 1;
            continue;
        }
        break;
    }

    if j > *index + 1 {
        *index = j - 1;
    }

    values
}

fn split_inline_list(value: &str) -> Vec<String> {
    value
        .split(';')
        .flat_map(|part| part.split(','))
        .map(str::trim)
        .filter(|part| !part.is_empty())
        .map(ToString::to_string)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_field_value() {
        assert_eq!(
            extract_field_value("**Feature ID:** #20", "**Feature ID:**"),
            Some("#20".to_string())
        );
        assert_eq!(
            extract_field_value("**Category:** Data Structures", "**Category:**"),
            Some("Data Structures".to_string())
        );
        assert_eq!(extract_field_value("Invalid line", "**Feature ID:**"), None);
    }

    #[test]
    fn test_extract_list_field_inline_and_bullets() {
        let inline = vec!["**Artifacts:** out/a.png; out/b.ansi"];
        let mut idx = 0;
        assert_eq!(
            extract_list_field(&inline, &mut idx, "**Artifacts:**"),
            vec!["out/a.png".to_string(), "out/b.ansi".to_string()]
        );

        let bullets = vec!["**Logs:**", "- logs/run.txt", "- logs/bridge.txt", "", "## Next"];
        let mut idx = 0;
        assert_eq!(
            extract_list_field(&bullets, &mut idx, "**Logs:**"),
            vec!["logs/run.txt".to_string(), "logs/bridge.txt".to_string()]
        );
        assert_eq!(idx, 2);
    }

    #[test]
    fn test_extract_metadata_related_and_dependencies() {
        let mut doc = SspecDoc {
            file_path: "test/example_spec.spl".into(),
            raw_content: String::new(),
            doc_blocks: vec![super::super::types::DocBlock {
                content: r#"
**Related:** doc/04_architecture/example.md, doc/05_design/example.md
**Dependencies:**
- std.test
- app.runtime
"#
                .trim()
                .to_string(),
                line_start: 0,
                line_end: 4,
            }],
            feature_title: None,
            feature_ids: vec![],
            metadata: Default::default(),
        };

        extract_metadata(&mut doc);

        assert_eq!(
            doc.metadata.related,
            vec![
                "doc/04_architecture/example.md".to_string(),
                "doc/05_design/example.md".to_string()
            ]
        );
        assert_eq!(
            doc.metadata.dependencies,
            vec!["std.test".to_string(), "app.runtime".to_string()]
        );
    }

    #[test]
    fn test_extract_metadata_source_and_type() {
        let mut doc = SspecDoc {
            file_path: "test/specs/functions_spec.spl".into(),
            raw_content: String::new(),
            doc_blocks: vec![super::super::types::DocBlock {
                content: r#"
**Status:** Reference
**Source:** functions.md
**Type:** Extracted Examples (Category B)
"#
                .trim()
                .to_string(),
                line_start: 0,
                line_end: 3,
            }],
            feature_title: None,
            feature_ids: vec![],
            metadata: Default::default(),
        };

        extract_metadata(&mut doc);

        assert_eq!(doc.metadata.source_doc.as_deref(), Some("functions.md"));
        assert_eq!(
            doc.metadata.doc_type.as_deref(),
            Some("Extracted Examples (Category B)")
        );
    }
}

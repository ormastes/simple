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

    // Extract metadata fields from markdown
    for line in full_content.lines() {
        let trimmed = line.trim();

        // Match patterns like "**Feature ID:** #20"
        if trimmed.starts_with("**Feature ID:**") {
            if let Some(id) = extract_field_value(trimmed, "**Feature ID:**") {
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
        }
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
}

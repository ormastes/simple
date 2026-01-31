//! Validation of SSpec documentation quality

use std::collections::HashSet;

use super::types::{SspecDoc, ValidationResult};

/// Validate a spec file and return warnings
pub fn validate_spec(sspec_doc: &SspecDoc) -> ValidationResult {
    let mut warnings = Vec::new();
    let mut has_sections = HashSet::new();

    let has_docs = !sspec_doc.doc_blocks.is_empty();
    let doc_lines: usize = sspec_doc.doc_blocks.iter().map(|b| b.content.lines().count()).sum();

    // Check if doc blocks exist
    if !has_docs {
        warnings.push("No documentation blocks found (stub generated)".to_string());
    } else {
        // Check total documentation length
        if doc_lines < 100 {
            warnings.push(format!("Only {} lines of documentation (recommended: 100+)", doc_lines));
        }

        // Concatenate all docs to check for sections
        let full_content = sspec_doc
            .doc_blocks
            .iter()
            .map(|b| b.content.as_str())
            .collect::<Vec<&str>>()
            .join("\n");

        // Check for standard sections
        for line in full_content.lines() {
            let trimmed = line.trim();
            if trimmed.starts_with("## ") {
                let section = trimmed.trim_start_matches("## ").trim().to_string();
                has_sections.insert(section);
            }
        }

        // Warn about missing important sections
        if !has_sections.contains("Overview") && !has_sections.contains("Description") {
            warnings.push("Missing '## Overview' or '## Description' section".to_string());
        }

        if !has_sections.contains("Syntax") && !has_sections.contains("Examples") {
            warnings.push("Missing '## Syntax' or '## Examples' section".to_string());
        }
    }

    ValidationResult {
        file_path: sspec_doc.file_path.clone(),
        has_docs,
        doc_lines,
        has_sections,
        warnings,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn test_validate_empty_spec() {
        let spec = SspecDoc {
            file_path: PathBuf::from("test.spl"),
            doc_blocks: vec![],
            feature_title: None,
            feature_ids: vec![],
            metadata: Default::default(),
        };

        let result = validate_spec(&spec);
        assert!(!result.has_docs);
        assert!(result.warnings.iter().any(|w| w.contains("No documentation blocks")));
    }
}

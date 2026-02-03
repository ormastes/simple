//! Data structures for SSpec documentation generation

use std::collections::HashSet;
use std::path::PathBuf;

/// Documentation block extracted from sspec file
#[derive(Debug, Clone)]
pub struct DocBlock {
    pub content: String,
    pub line_start: usize,
    pub line_end: usize,
}

/// Feature metadata extracted from documentation
#[derive(Debug, Clone, Default)]
pub struct FeatureMetadata {
    pub id: Option<String>,
    pub category: Option<String>,
    pub difficulty: Option<String>,
    pub status: Option<String>,
    pub related: Vec<String>,
    pub dependencies: Vec<String>,
}

/// Parsed sspec file with documentation and test structure
#[derive(Debug)]
pub struct SspecDoc {
    pub file_path: PathBuf,
    pub doc_blocks: Vec<DocBlock>,
    pub feature_title: Option<String>,
    pub feature_ids: Vec<String>,
    pub metadata: FeatureMetadata,
}

/// Validation result for a spec file
#[derive(Debug, Clone)]
pub struct ValidationResult {
    pub file_path: PathBuf,
    pub has_docs: bool,
    pub doc_lines: usize,
    pub has_sections: HashSet<String>,
    pub warnings: Vec<String>,
}

/// Statistics for documentation generation
#[derive(Debug, Default)]
pub struct DocStats {
    pub total_specs: usize,
    pub specs_with_docs: usize,
    pub specs_without_docs: usize,
    pub total_doc_lines: usize,
    pub total_warnings: usize,
}

impl DocStats {
    pub fn add_spec(&mut self, has_docs: bool, doc_lines: usize, warnings: usize) {
        self.total_specs += 1;
        if has_docs {
            self.specs_with_docs += 1;
        } else {
            self.specs_without_docs += 1;
        }
        self.total_doc_lines += doc_lines;
        self.total_warnings += warnings;
    }

    pub fn coverage_percent(&self) -> f32 {
        if self.total_specs == 0 {
            return 0.0;
        }
        (self.specs_with_docs as f32 / self.total_specs as f32) * 100.0
    }
}

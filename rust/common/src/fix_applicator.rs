//! Fix application engine for EasyFix diagnostics.
//!
//! Applies machine-applicable fixes to source files, handling
//! overlapping spans by sorting and rejecting conflicts.

use crate::diagnostic::{EasyFix, FixConfidence, Replacement, SourceRegistry};
use std::collections::HashMap;
use std::fmt;
use std::path::Path;

/// Error type for fix application
#[derive(Debug)]
pub enum FixError {
    /// Two replacements overlap in the same file
    ConflictingReplacements {
        file: String,
        fix_id_a: String,
        fix_id_b: String,
    },
    /// File not found in source registry
    FileNotFound(String),
    /// IO error writing to disk
    IoError(std::io::Error),
}

impl fmt::Display for FixError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FixError::ConflictingReplacements {
                file,
                fix_id_a,
                fix_id_b,
            } => {
                write!(f, "conflicting fixes in {}: {} and {}", file, fix_id_a, fix_id_b)
            }
            FixError::FileNotFound(file) => write!(f, "file not found: {}", file),
            FixError::IoError(e) => write!(f, "IO error: {}", e),
        }
    }
}

impl std::error::Error for FixError {}

impl From<std::io::Error> for FixError {
    fn from(e: std::io::Error) -> Self {
        FixError::IoError(e)
    }
}

/// Report of applied fixes
#[derive(Debug, Default)]
pub struct FixReport {
    /// Number of fixes applied
    pub applied: usize,
    /// Number of fixes skipped due to conflicts
    pub skipped: usize,
    /// Files that were modified
    pub modified_files: Vec<String>,
    /// Details of each applied fix
    pub details: Vec<String>,
}

/// Fix application engine
pub struct FixApplicator;

impl FixApplicator {
    /// Apply fixes to source content. Returns map of file -> new content.
    pub fn apply(fixes: &[EasyFix], sources: &SourceRegistry) -> Result<HashMap<String, String>, FixError> {
        // Group replacements by file, tagged with fix ID
        let mut by_file: HashMap<String, Vec<(&str, &Replacement)>> = HashMap::new();
        for fix in fixes {
            for replacement in &fix.replacements {
                by_file
                    .entry(replacement.file.clone())
                    .or_default()
                    .push((&fix.id, replacement));
            }
        }

        let mut results = HashMap::new();

        for (file, mut replacements) in by_file {
            let source = sources.get(&file).ok_or_else(|| FixError::FileNotFound(file.clone()))?;

            // Sort by start position (descending) so we can apply from end to start
            // without invalidating earlier offsets
            replacements.sort_by(|a, b| b.1.span.start.cmp(&a.1.span.start));

            // Check for overlapping spans
            for i in 0..replacements.len().saturating_sub(1) {
                let (id_a, rep_a) = replacements[i];
                let (id_b, rep_b) = replacements[i + 1];
                // Since sorted descending, rep_a.start >= rep_b.start
                // Overlap if rep_b.end > rep_a.start
                if rep_b.span.end > rep_a.span.start {
                    return Err(FixError::ConflictingReplacements {
                        file: file.clone(),
                        fix_id_a: id_a.to_string(),
                        fix_id_b: id_b.to_string(),
                    });
                }
            }

            // Apply replacements from end to start
            let mut new_source = source.to_string();
            for (_id, replacement) in &replacements {
                let start = replacement.span.start;
                let end = replacement.span.end;
                if start <= new_source.len() && end <= new_source.len() {
                    new_source.replace_range(start..end, &replacement.new_text);
                }
            }

            results.insert(file, new_source);
        }

        Ok(results)
    }

    /// Apply fixes in-place to files on disk.
    pub fn apply_to_disk(fixes: &[EasyFix], sources: &SourceRegistry, dry_run: bool) -> Result<FixReport, FixError> {
        let new_contents = Self::apply(fixes, sources)?;
        let mut report = FixReport::default();

        report.applied = fixes.len();

        for (file, content) in &new_contents {
            report.modified_files.push(file.clone());
            if !dry_run {
                std::fs::write(Path::new(file), content)?;
            }
        }

        for fix in fixes {
            report.details.push(format!("[{}] {}", fix.id, fix.description));
        }

        Ok(report)
    }

    /// Filter fixes by confidence level
    pub fn filter_by_confidence(fixes: &[EasyFix], min_confidence: FixConfidence) -> Vec<&EasyFix> {
        fixes
            .iter()
            .filter(|f| match (min_confidence, f.confidence) {
                (FixConfidence::Safe, FixConfidence::Safe) => true,
                (FixConfidence::Likely, FixConfidence::Safe | FixConfidence::Likely) => true,
                (FixConfidence::Uncertain, _) => true,
                _ => false,
            })
            .collect()
    }

    /// Filter fixes by specific ID prefix
    pub fn filter_by_id<'a>(fixes: &'a [EasyFix], id_prefix: &str) -> Vec<&'a EasyFix> {
        fixes.iter().filter(|f| f.id.starts_with(id_prefix)).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diagnostic::Span;

    fn make_fix(id: &str, file: &str, start: usize, end: usize, new_text: &str) -> EasyFix {
        EasyFix {
            id: id.to_string(),
            description: format!("Fix {}", id),
            replacements: vec![Replacement {
                file: file.to_string(),
                span: Span::new(start, end, 1, start + 1),
                new_text: new_text.to_string(),
            }],
            confidence: FixConfidence::Safe,
        }
    }

    #[test]
    fn test_apply_single_fix() {
        let mut sources = SourceRegistry::new();
        sources.add("test.spl", "hello world");

        let fixes = vec![make_fix("f1", "test.spl", 0, 5, "goodbye")];
        let result = FixApplicator::apply(&fixes, &sources).unwrap();

        assert_eq!(result.get("test.spl").unwrap(), "goodbye world");
    }

    #[test]
    fn test_apply_multiple_non_overlapping() {
        let mut sources = SourceRegistry::new();
        sources.add("test.spl", "aaa bbb ccc");

        let fixes = vec![
            make_fix("f1", "test.spl", 0, 3, "xxx"),
            make_fix("f2", "test.spl", 8, 11, "zzz"),
        ];
        let result = FixApplicator::apply(&fixes, &sources).unwrap();

        assert_eq!(result.get("test.spl").unwrap(), "xxx bbb zzz");
    }

    #[test]
    fn test_conflicting_replacements() {
        let mut sources = SourceRegistry::new();
        sources.add("test.spl", "hello world");

        let fixes = vec![
            make_fix("f1", "test.spl", 0, 8, "xxx"),
            make_fix("f2", "test.spl", 5, 11, "yyy"),
        ];
        let result = FixApplicator::apply(&fixes, &sources);
        assert!(result.is_err());
    }

    #[test]
    fn test_filter_by_confidence() {
        let fixes = vec![
            EasyFix {
                id: "safe".to_string(),
                description: "safe fix".to_string(),
                replacements: vec![],
                confidence: FixConfidence::Safe,
            },
            EasyFix {
                id: "likely".to_string(),
                description: "likely fix".to_string(),
                replacements: vec![],
                confidence: FixConfidence::Likely,
            },
            EasyFix {
                id: "uncertain".to_string(),
                description: "uncertain fix".to_string(),
                replacements: vec![],
                confidence: FixConfidence::Uncertain,
            },
        ];

        assert_eq!(
            FixApplicator::filter_by_confidence(&fixes, FixConfidence::Safe).len(),
            1
        );
        assert_eq!(
            FixApplicator::filter_by_confidence(&fixes, FixConfidence::Likely).len(),
            2
        );
        assert_eq!(
            FixApplicator::filter_by_confidence(&fixes, FixConfidence::Uncertain).len(),
            3
        );
    }
}

//! Text-based diff using Longest Common Subsequence (LCS) algorithm.
//!
//! Provides line-by-line diffing with unified diff format output.

use std::cmp::max;
use std::collections::HashMap;

/// Line-by-line text diff result
#[derive(Debug, Clone)]
pub struct TextDiff {
    pub hunks: Vec<DiffHunk>,
}

/// A hunk of changes in the diff
#[derive(Debug, Clone)]
pub struct DiffHunk {
    pub old_start: usize,
    pub old_count: usize,
    pub new_start: usize,
    pub new_count: usize,
    pub lines: Vec<DiffLine>,
}

/// A single line in a diff
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DiffLine {
    Context(String),
    Addition(String),
    Deletion(String),
}

impl TextDiff {
    /// Compute diff between two texts
    pub fn new(old_text: &str, new_text: &str) -> Self {
        let old_lines: Vec<&str> = old_text.lines().collect();
        let new_lines: Vec<&str> = new_text.lines().collect();

        let lcs = Self::compute_lcs(&old_lines, &new_lines);
        let hunks = Self::build_hunks(&old_lines, &new_lines, &lcs);

        Self { hunks }
    }

    /// Compute LCS table using dynamic programming
    fn compute_lcs(old_lines: &[&str], new_lines: &[&str]) -> Vec<Vec<usize>> {
        let m = old_lines.len();
        let n = new_lines.len();
        let mut lcs = vec![vec![0; n + 1]; m + 1];

        for i in 1..=m {
            for j in 1..=n {
                if old_lines[i - 1] == new_lines[j - 1] {
                    lcs[i][j] = lcs[i - 1][j - 1] + 1;
                } else {
                    lcs[i][j] = max(lcs[i - 1][j], lcs[i][j - 1]);
                }
            }
        }

        lcs
    }

    /// Build diff hunks from LCS table
    fn build_hunks(old_lines: &[&str], new_lines: &[&str], lcs: &[Vec<usize>]) -> Vec<DiffHunk> {
        let mut hunks = Vec::new();
        let mut current_hunk: Option<DiffHunk> = None;

        let mut i = old_lines.len();
        let mut j = new_lines.len();

        let mut changes: Vec<(usize, usize, DiffLine)> = Vec::new();

        // Backtrack through LCS table to find differences
        while i > 0 || j > 0 {
            if i > 0 && j > 0 && old_lines[i - 1] == new_lines[j - 1] {
                changes.push((i - 1, j - 1, DiffLine::Context(old_lines[i - 1].to_string())));
                i -= 1;
                j -= 1;
            } else if j > 0 && (i == 0 || lcs[i][j - 1] >= lcs[i - 1][j]) {
                changes.push((i, j - 1, DiffLine::Addition(new_lines[j - 1].to_string())));
                j -= 1;
            } else if i > 0 {
                changes.push((i - 1, j, DiffLine::Deletion(old_lines[i - 1].to_string())));
                i -= 1;
            }
        }

        changes.reverse();

        // Group changes into hunks
        for (old_idx, new_idx, line) in changes {
            match (&mut current_hunk, &line) {
                (None, DiffLine::Context(_)) => {
                    // Skip leading context
                }
                (None, _) => {
                    // Start new hunk
                    current_hunk = Some(DiffHunk {
                        old_start: old_idx + 1,
                        old_count: 0,
                        new_start: new_idx + 1,
                        new_count: 0,
                        lines: vec![line.clone()],
                    });
                }
                (Some(hunk), DiffLine::Context(_)) => {
                    hunk.lines.push(line.clone());
                    // Check if we should close the hunk
                    if hunk
                        .lines
                        .iter()
                        .rev()
                        .take(3)
                        .all(|l| matches!(l, DiffLine::Context(_)))
                    {
                        // Close hunk
                        if let Some(h) = current_hunk.take() {
                            hunks.push(Self::finalize_hunk(h));
                        }
                    }
                }
                (Some(hunk), _) => {
                    hunk.lines.push(line.clone());
                }
            }
        }

        // Close final hunk
        if let Some(h) = current_hunk {
            hunks.push(Self::finalize_hunk(h));
        }

        hunks
    }

    /// Finalize hunk by computing counts
    fn finalize_hunk(mut hunk: DiffHunk) -> DiffHunk {
        for line in &hunk.lines {
            match line {
                DiffLine::Context(_) => {
                    hunk.old_count += 1;
                    hunk.new_count += 1;
                }
                DiffLine::Deletion(_) => {
                    hunk.old_count += 1;
                }
                DiffLine::Addition(_) => {
                    hunk.new_count += 1;
                }
            }
        }
        hunk
    }

    /// Format as unified diff
    pub fn format_unified(&self, old_path: &str, new_path: &str, context: usize) -> String {
        let mut output = String::new();

        output.push_str(&format!("--- {}\n", old_path));
        output.push_str(&format!("+++ {}\n", new_path));

        for hunk in &self.hunks {
            output.push_str(&format!(
                "@@ -{},{} +{},{} @@\n",
                hunk.old_start, hunk.old_count, hunk.new_start, hunk.new_count
            ));

            for line in &hunk.lines {
                match line {
                    DiffLine::Context(s) => output.push_str(&format!(" {}\n", s)),
                    DiffLine::Deletion(s) => output.push_str(&format!("-{}\n", s)),
                    DiffLine::Addition(s) => output.push_str(&format!("+{}\n", s)),
                }
            }
        }

        output
    }

    /// Count total additions
    pub fn additions(&self) -> usize {
        self.hunks
            .iter()
            .flat_map(|h| &h.lines)
            .filter(|l| matches!(l, DiffLine::Addition(_)))
            .count()
    }

    /// Count total deletions
    pub fn deletions(&self) -> usize {
        self.hunks
            .iter()
            .flat_map(|h| &h.lines)
            .filter(|l| matches!(l, DiffLine::Deletion(_)))
            .count()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_diff() {
        let old = "line1\nline2\nline3";
        let new = "line1\nline2 modified\nline3";

        let diff = TextDiff::new(old, new);
        assert!(!diff.hunks.is_empty());
        assert_eq!(diff.deletions(), 1);
        assert_eq!(diff.additions(), 1);
    }

    #[test]
    fn test_addition_only() {
        let old = "line1\nline2";
        let new = "line1\nline2\nline3";

        let diff = TextDiff::new(old, new);
        assert_eq!(diff.additions(), 1);
        assert_eq!(diff.deletions(), 0);
    }

    #[test]
    fn test_deletion_only() {
        let old = "line1\nline2\nline3";
        let new = "line1\nline3";

        let diff = TextDiff::new(old, new);
        assert_eq!(diff.additions(), 0);
        assert_eq!(diff.deletions(), 1);
    }

    #[test]
    fn test_no_changes() {
        let text = "line1\nline2\nline3";
        let diff = TextDiff::new(text, text);
        assert_eq!(diff.additions(), 0);
        assert_eq!(diff.deletions(), 0);
    }
}

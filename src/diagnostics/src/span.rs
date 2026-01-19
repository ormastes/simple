//! Source location tracking

use serde::{Deserialize, Serialize};

/// Source location span (line, column, offset)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
}

impl Span {
    /// Create a new span
    pub fn new(start: usize, end: usize, line: usize, column: usize) -> Self {
        Self {
            start,
            end,
            line,
            column,
        }
    }

    /// Create a zero-length span at the given position
    pub fn at(pos: usize, line: usize, column: usize) -> Self {
        Self {
            start: pos,
            end: pos,
            line,
            column,
        }
    }

    /// Combine two spans into one covering both
    pub fn to(self, other: Span) -> Span {
        Span {
            start: self.start.min(other.start),
            end: self.end.max(other.end),
            line: self.line.min(other.line),
            column: self.column,
        }
    }

    /// Get the length of this span
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// Check if this span is empty (zero-length)
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }
}

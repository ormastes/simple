//! Custom block handlers for DSL embedding.
//!
//! This module provides handlers for custom blocks:
//! - `m{}` - Math block (Simple-compatible math expressions)
//! - `sh{}` - Shell block (portable shell scripting)
//! - `sql{}` - SQL block (parameterized queries)
//! - `re{}` - Regex block (compiled regular expressions)
//! - `md{}` - Markdown block (document embedding) - not yet implemented
//! - `html{}` - HTML block (HTML content) - not yet implemented
//! - `graph{}` - Graph block (diagrams) - not yet implemented
//! - `img{}` - Image block (image embedding) - not yet implemented
//!
//! ## Math Block Syntax
//!
//! The math block supports Simple-compatible syntax (preferred) and LaTeX aliases:
//!
//! ### Preferred Syntax
//! ```simple
//! m{ sqrt(16) }        // Square root
//! m{ frac(1, 2) }      // Fraction
//! m{ pi * r^2 }        // Constants and power
//! m{ sin(x) + cos(x) } // Trig functions
//! m{ sum(i, 1..n) i^2 }// Summation
//! m{ x[i] }            // Subscript
//! ```
//!
//! ### LaTeX Compatibility (warns)
//! ```simple
//! m{ \sqrt{16} }       // Use sqrt(16) instead
//! m{ \frac{1}{2} }     // Use frac(1, 2) instead
//! m{ \pi r^2 }         // Use pi instead
//! m{ x_i }             // Use x[i] instead
//! ```

mod math;
mod regex;
mod shell;
mod sql;

pub use math::MathBlock;
pub use regex::RegexBlock;
pub use shell::ShellBlock;
pub use sql::SqlBlock;

use crate::error::CompileError;
use crate::value::Value;

/// Result of evaluating a custom block
pub type BlockResult = Result<Value, CompileError>;

/// Trait for custom block handlers
pub trait BlockHandler {
    /// Parse and evaluate the block payload
    fn evaluate(&self, payload: &str) -> BlockResult;

    /// Get the block kind name
    fn kind(&self) -> &'static str;
}

/// Evaluate a custom block based on its kind
pub fn evaluate_block(kind: &str, payload: &str) -> BlockResult {
    match kind {
        "m" => MathBlock.evaluate(payload),
        "sh" => ShellBlock.evaluate(payload),
        "sql" => SqlBlock.evaluate(payload),
        "re" => RegexBlock.evaluate(payload),
        // md, html, graph, img are not yet implemented
        _ => Err(CompileError::Semantic(format!("unknown block kind: {}", kind))),
    }
}

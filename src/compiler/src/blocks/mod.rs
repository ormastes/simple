//! Custom block handlers for DSL embedding.
//!
//! This module provides handlers for custom blocks:
//! - `m{}` - Math block (LaTeX-like expressions)
//! - `sh{}` - Shell block (portable shell scripting)
//! - `sql{}` - SQL block (parameterized queries)
//! - `re{}` - Regex block (compiled regular expressions)
//! - `md{}` - Markdown block (document embedding)
//! - `html{}` - HTML block (HTML content)
//! - `graph{}` - Graph block (diagrams)
//! - `img{}` - Image block (image embedding)

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
        _ => Err(CompileError::Semantic(format!(
            "unknown block kind: {}",
            kind
        ))),
    }
}

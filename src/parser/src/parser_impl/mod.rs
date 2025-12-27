//! Simple language parser
//!
//! This module provides a recursive descent parser with Pratt parsing for expressions.
//! The parser is split into multiple submodules for maintainability:
//! - `expressions/` - Expression parsing (Pratt parser)
//! - `statements/` - Statement parsing (let, if, for, etc.)
//! - `types_def/` - Type definition parsing (struct, class, enum, etc.)
//! - `parser_types` - Type parsing methods
//! - `parser_patterns` - Pattern parsing methods
//!
//! ## Parser Organization
//! - `core` - Parser struct, constructor, main parse entry point
//! - `doc_comments` - Doc comment parsing
//! - `items` - Top-level item parsing (pub items, attributed items)
//! - `functions` - Function parsing with decorators and contracts
//! - `definitions` - Type definition parsing (struct, class, enum, union, trait)
//! - `attributes` - Attribute and decorator parsing

pub(crate) mod core;
mod doc_comments;
mod items;
mod functions;
mod definitions;
mod attributes;

// Re-export the Parser struct and ParserMode
pub use core::{Parser, ParserMode};

// Integration tests moved to tests/ directory - no longer using #[path] include

//! SUI Template Parser
//!
//! Parses `.sui` template files into an AST.

pub mod ast;
mod parser_expr;
mod error;
mod parser;
mod directive;
mod declarations;
mod blocks;
mod nodes;
mod elements;
mod attributes;
mod control;
mod statements;
mod types;
mod helpers;

#[cfg(test)]
mod tests;

pub use ast::*;
pub use error::ParseError;
pub use parser::SuiParser;

//! SUI Template Parser
//!
//! Parses `.sui` template files into an AST.

pub mod ast;
mod attributes;
mod blocks;
mod control;
mod declarations;
mod directive;
mod elements;
mod error;
mod helpers;
mod nodes;
mod parser;
mod parser_expr;
mod statements;
mod types;

#[cfg(test)]
mod tests;

pub use ast::*;
pub use error::ParseError;
pub use parser::SuiParser;

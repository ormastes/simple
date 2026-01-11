// Allow warnings for incomplete features
#![allow(dead_code)]
#![allow(clippy::large_enum_variant)]

pub mod arena;
pub mod ast;
pub mod diagnostic;
pub mod doc_gen;
pub mod error;
pub mod error_recovery;
pub mod interner;
pub mod lexer;
pub mod macro_registry;
pub mod sui_parser;
pub mod token;

// Parser implementation (split across multiple modules)
mod parser_impl;

// Parser submodules (split from parser.rs for maintainability)
mod expressions;
mod parser_helpers;
mod parser_patterns;
mod parser_types;
mod stmt_parsing;
mod types_def;

pub use arena::*;
pub use ast::*;
pub use diagnostic::*;
pub use doc_gen::{generate as generate_docs, DocItem, DocItemKind, ModuleDocs};
pub use error::*;
pub use error_recovery::*;
pub use interner::*;
pub use lexer::*;
pub use macro_registry::*;
pub use parser_impl::{DebugMode, Parser, ParserMode, MAX_LOOP_ITERATIONS};
pub use sui_parser::*;
pub use token::*;

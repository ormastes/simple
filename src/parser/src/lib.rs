pub mod ast;
pub mod diagnostic;
pub mod doc_gen;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod token;

// Parser submodules (split from parser.rs for maintainability)
mod expressions;
mod parser_patterns;
mod parser_types;
mod parser_helpers;
mod statements;
mod types_def;

pub use ast::*;
pub use diagnostic::*;
pub use doc_gen::{generate as generate_docs, DocItem, DocItemKind, ModuleDocs};
pub use error::*;
pub use lexer::*;
pub use parser::*;
pub use token::*;

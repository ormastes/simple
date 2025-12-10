pub mod ast;
pub mod error;
pub mod lexer;
pub mod parser;
pub mod token;

// Parser submodules (split from parser.rs for maintainability)
mod expressions;
mod statements;
mod types_def;

pub use ast::*;
pub use error::*;
pub use lexer::*;
pub use parser::*;
pub use token::*;

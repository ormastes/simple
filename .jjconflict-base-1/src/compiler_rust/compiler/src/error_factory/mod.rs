//! Error factory functions split into submodules by category.
mod resolve;
mod codegen_ops;

pub mod factory {
    pub use super::resolve::*;
    pub use super::codegen_ops::*;
}

mod context;
mod error;
mod expr_lowering;
mod lowerer;
mod module_lowering;
mod stmt_lowering;
mod type_resolver;

pub use error::{LowerError, LowerResult};
pub use lowerer::Lowerer;

use simple_parser::Module;
use super::types::HirModule;

/// Convenience function to lower an AST module to HIR
pub fn lower(module: &Module) -> LowerResult<HirModule> {
    Lowerer::new().lower_module(module)
}

#[cfg(test)]
#[path = "lower_tests.rs"]
mod tests;

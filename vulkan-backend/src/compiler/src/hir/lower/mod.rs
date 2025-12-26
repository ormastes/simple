mod context;
mod error;
mod expr;
mod lowerer;
mod module_lowering;
pub mod parallel;
mod stmt_lowering;
mod type_resolver;

pub use error::{LowerError, LowerResult};
pub use lowerer::Lowerer;
pub use parallel::{
    lower_modules_parallel, lower_modules_parallel_with_config, BatchLowerer, LoweringStats,
    ParallelLowerConfig, ParallelModuleLowerer,
};

use simple_parser::Module;
use super::types::HirModule;

/// Convenience function to lower an AST module to HIR
pub fn lower(module: &Module) -> LowerResult<HirModule> {
    Lowerer::new().lower_module(module)
}

#[cfg(test)]
mod tests;

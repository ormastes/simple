mod context;
mod error;
mod expr;
mod import_loader;
mod lowerer;
mod module_lowering;
pub mod parallel;
mod stmt_lowering;
mod type_registration;
mod type_resolver;

pub use error::{LowerError, LowerResult};
pub use lowerer::Lowerer;
pub use parallel::{
    lower_modules_parallel, lower_modules_parallel_with_config, BatchLowerer, LoweringStats, ParallelLowerConfig,
    ParallelModuleLowerer,
};

use super::types::HirModule;
use crate::module_resolver::ModuleResolver;
use simple_parser::Module;
use std::path::Path;

/// Convenience function to lower an AST module to HIR
pub fn lower(module: &Module) -> LowerResult<HirModule> {
    Lowerer::new().lower_module(module)
}

/// Lower an AST module to HIR with module resolution support for loading imported types.
///
/// This enables compile-time type checking for imports by loading type definitions
/// from imported modules. If the current file path is provided, relative imports
/// can be resolved.
///
/// # Arguments
/// * `module` - The AST module to lower
/// * `current_file` - Path to the current file being compiled (for resolving relative imports)
///
/// # Returns
/// The lowered HIR module with all imported types loaded
pub fn lower_with_context(module: &Module, current_file: &Path) -> LowerResult<HirModule> {
    // Create a module resolver for this compilation
    let module_resolver = ModuleResolver::single_file(current_file);

    Lowerer::with_module_resolver(module_resolver, current_file.to_path_buf()).lower_module(module)
}

#[cfg(test)]
mod tests;

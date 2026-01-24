mod context;
pub mod deprecation_warning;
mod error;
mod expr;
mod import_loader;
mod lowerer;
mod memory_check;
pub mod memory_warning;
mod module_lowering;
pub mod parallel;
mod stmt_lowering;
mod type_registration;
mod type_resolver;

pub use deprecation_warning::{DeprecationWarning, DeprecationWarningCollector};
pub use error::{LowerError, LowerResult};
pub use memory_warning::{MemoryWarning, MemoryWarningCode, MemoryWarningCollector, WarningSummary};
pub use lowerer::Lowerer;

use super::lifetime::LifetimeViolation;
use super::types::HirModule;

/// Result of lowering that includes both the module and memory warnings
#[derive(Debug)]
pub struct LoweringOutput {
    /// The lowered HIR module
    pub module: HirModule,
    /// Memory safety warnings collected during lowering
    pub warnings: MemoryWarningCollector,
    /// Lean 4 verification code for lifetime constraints (if any)
    pub lifetime_lean4: Option<String>,
    /// Lifetime violations detected (stored for reporting even if lowering succeeds)
    pub lifetime_violations: Vec<LifetimeViolation>,
}

impl LoweringOutput {
    /// Create a new lowering output
    pub fn new(module: HirModule, warnings: MemoryWarningCollector) -> Self {
        Self {
            module,
            warnings,
            lifetime_lean4: None,
            lifetime_violations: Vec::new(),
        }
    }

    /// Create a new lowering output with lifetime information
    pub fn with_lifetime(
        module: HirModule,
        warnings: MemoryWarningCollector,
        lifetime_lean4: String,
        lifetime_violations: Vec<LifetimeViolation>,
    ) -> Self {
        Self {
            module,
            warnings,
            lifetime_lean4: Some(lifetime_lean4),
            lifetime_violations,
        }
    }

    /// Check if there are any warnings
    pub fn has_warnings(&self) -> bool {
        self.warnings.has_warnings()
    }

    /// Get the warning count
    pub fn warning_count(&self) -> usize {
        self.warnings.count()
    }

    /// Get the warning summary
    pub fn summary(&self) -> WarningSummary {
        self.warnings.summary()
    }

    /// Check if there are any lifetime violations
    pub fn has_lifetime_violations(&self) -> bool {
        !self.lifetime_violations.is_empty()
    }

    /// Get lifetime violation count
    pub fn lifetime_violation_count(&self) -> usize {
        self.lifetime_violations.len()
    }

    /// Get Lean 4 lifetime verification code
    pub fn get_lifetime_lean4(&self) -> Option<&str> {
        self.lifetime_lean4.as_deref()
    }
}

/// Convenience function to lower an AST module to HIR with warnings
pub fn lower_with_warnings(module: &simple_parser::Module) -> LowerResult<LoweringOutput> {
    Lowerer::new().lower_module_with_warnings(module)
}

pub use parallel::{
    lower_modules_parallel, lower_modules_parallel_with_config, BatchLowerer, LoweringStats, ParallelLowerConfig,
    ParallelModuleLowerer,
};

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

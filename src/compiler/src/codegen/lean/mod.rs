//! Lean 4 code generation module.
//!
//! This module generates Lean 4 code from verified Simple code, enabling
//! formal verification of Simple programs using the Lean theorem prover.
//!
//! ## Generated Artifacts
//!
//! - `structure` definitions from Simple classes/structs
//! - `inductive` types from Simple enums
//! - `def` functions from verified Simple functions
//! - `theorem` statements from contracts (requires/ensures)
//! - `Prop` definitions from class invariants
//!
//! ## Usage
//!
//! ```ignore
//! use simple_compiler::codegen::lean::LeanCodegen;
//!
//! let codegen = LeanCodegen::new();
//! let lean_code = codegen.generate_module(&hir_module)?;
//! ```

mod types;
mod functions;
mod contracts;
mod expressions;
mod emitter;
mod verification_diagnostics;
mod verification_checker;
mod runner;

pub use types::{LeanType, TypeTranslator};
pub use functions::{FunctionTranslator, LeanFunction};
pub use contracts::{ContractTranslator, LeanTheorem, LeanProp, LeanClassInvariant};
pub use expressions::{ExprTranslator, LeanExpr, LeanLit, LeanDoStmt};
pub use emitter::{LeanEmitter, LeanModule};
pub use verification_diagnostics::{
    VerificationErrorCode, VerificationDiagnostic, VerificationDiagnostics
};
pub use verification_checker::{VerificationChecker, check_module};
pub use runner::{LeanRunner, LeanCheckResult, VerificationSummary};

use crate::hir::{HirModule, HirFunction};
use crate::CompileError;

/// Lean code generator
pub struct LeanCodegen {
    /// Module name for the generated Lean file
    module_name: Option<String>,
    /// Whether to generate proof stubs (sorry) or leave as axioms
    generate_stubs: bool,
}

impl LeanCodegen {
    /// Create a new Lean code generator
    pub fn new() -> Self {
        Self {
            module_name: None,
            generate_stubs: true,
        }
    }

    /// Set the module name
    pub fn with_module_name(mut self, name: String) -> Self {
        self.module_name = Some(name);
        self
    }

    /// Set whether to generate proof stubs
    pub fn with_stubs(mut self, generate: bool) -> Self {
        self.generate_stubs = generate;
        self
    }

    /// Generate Lean code from a HIR module
    pub fn generate_module(&self, module: &HirModule) -> Result<String, CompileError> {
        let mut emitter = LeanEmitter::new();

        // Generate module header
        let module_name = self.module_name.clone()
            .or_else(|| module.name.clone())
            .unwrap_or_else(|| "Main".to_string());

        emitter.emit_header(&module_name);

        // Generate type definitions from structs and enums in functions
        let type_translator = TypeTranslator::new(&module.types);

        // Emit type definitions for types used by verified functions
        // (A more complete implementation would track all named types)

        // Generate function definitions (only verified ones)
        let func_translator = FunctionTranslator::new(&type_translator);
        let contract_translator = ContractTranslator::new(&type_translator);

        for func in &module.functions {
            if func.verification_mode.is_verified() {
                // Generate function
                let lean_func = func_translator.translate_function(func)?;
                emitter.emit_function(&lean_func);

                // Generate contracts as theorems
                if let Some(ref contract) = func.contract {
                    let theorems = contract_translator.translate_contract(func, contract)?;
                    for theorem in theorems {
                        emitter.emit_theorem(&theorem, self.generate_stubs);
                    }
                }
            }
        }

        emitter.emit_footer(&module_name);
        Ok(emitter.finish())
    }

    /// Generate Lean code for a single verified function
    pub fn generate_function(&self, func: &HirFunction, module: &HirModule) -> Result<String, CompileError> {
        if !func.verification_mode.is_verified() {
            return Err(CompileError::Semantic(format!(
                "Function '{}' is not marked @verify",
                func.name
            )));
        }

        let mut emitter = LeanEmitter::new();
        let type_translator = TypeTranslator::new(&module.types);
        let func_translator = FunctionTranslator::new(&type_translator);

        let lean_func = func_translator.translate_function(func)?;
        emitter.emit_function(&lean_func);

        Ok(emitter.finish())
    }
}

impl Default for LeanCodegen {
    fn default() -> Self {
        Self::new()
    }
}

/// Statistics from Lean code generation
#[derive(Debug, Default)]
pub struct LeanGenStats {
    /// Number of types generated
    pub types_generated: usize,
    /// Number of functions generated
    pub functions_generated: usize,
    /// Number of theorems generated
    pub theorems_generated: usize,
    /// Number of proof stubs (sorry) generated
    pub stubs_generated: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_codegen_creation() {
        let codegen = LeanCodegen::new();
        assert!(codegen.generate_stubs);
        assert!(codegen.module_name.is_none());
    }

    #[test]
    fn test_codegen_with_module_name() {
        let codegen = LeanCodegen::new().with_module_name("TestModule".to_string());
        assert_eq!(codegen.module_name, Some("TestModule".to_string()));
    }
}

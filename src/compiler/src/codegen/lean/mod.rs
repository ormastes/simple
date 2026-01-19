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
//! ```no_run
//! use simple_compiler::codegen::lean::LeanCodegen;
//! use simple_compiler::hir::HirModule;
//!
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! # let hir_module = HirModule::default();
//! let codegen = LeanCodegen::new();
//! let lean_code = codegen.generate_module(&hir_module)?;
//! # Ok(())
//! # }
//! ```

mod contracts;
mod emitter;
mod expressions;
mod functions;
pub mod memory_safety;
pub mod naming;
mod runner;
mod traits;
mod types;
mod verification_checker;
mod verification_diagnostics;

pub use contracts::{ContractTranslator, LeanClassInvariant, LeanProp, LeanTheorem};
pub use emitter::{LeanEmitter, LeanModule};
pub use expressions::{ExprTranslator, LeanDoStmt, LeanExpr, LeanLit};
pub use functions::{FunctionTranslator, LeanFunction};
pub use memory_safety::{generate_memory_safety_lean, MemorySafetyLeanGen};
pub use runner::{LeanCheckResult, LeanRunner, VerificationSummary};
pub use traits::{LeanBinding, LeanClass, LeanInstance, LeanMethodSig, StaticPolyTheorems, TraitTranslator};
pub use types::{LeanType, TypeTranslator};
pub use verification_checker::{check_module, VerificationChecker};
pub use verification_diagnostics::{VerificationDiagnostic, VerificationDiagnostics, VerificationErrorCode};

use crate::hir::{HirFunction, HirModule};
use crate::CompileError;
use simple_parser::ast::{ImplBlock, TraitDef};

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
        let module_name = self
            .module_name
            .clone()
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
            return Err(crate::error::factory::function_not_verify_marked(&func.name));
        }

        let mut emitter = LeanEmitter::new();
        let type_translator = TypeTranslator::new(&module.types);
        let func_translator = FunctionTranslator::new(&type_translator);

        let lean_func = func_translator.translate_function(func)?;
        emitter.emit_function(&lean_func);

        Ok(emitter.finish())
    }

    /// Generate Lean type class from a Simple trait definition
    pub fn generate_trait(&self, trait_def: &TraitDef, module: &HirModule) -> Result<String, CompileError> {
        let mut emitter = LeanEmitter::new();
        let type_translator = TypeTranslator::new(&module.types);
        let trait_translator = TraitTranslator::new(&type_translator);

        let lean_class = trait_translator.translate_trait(trait_def)?;
        emitter.emit_class(&lean_class);

        Ok(emitter.finish())
    }

    /// Generate Lean instance from a Simple impl block
    pub fn generate_impl(&self, impl_block: &ImplBlock, module: &HirModule) -> Result<String, CompileError> {
        let mut emitter = LeanEmitter::new();
        let type_translator = TypeTranslator::new(&module.types);
        let trait_translator = TraitTranslator::new(&type_translator);

        let lean_instance = trait_translator.translate_impl(impl_block)?;
        emitter.emit_instance(&lean_instance, self.generate_stubs);

        Ok(emitter.finish())
    }

    /// Generate Lean binding for static dispatch
    pub fn generate_binding(&self, interface_name: &str, impl_type: LeanType) -> Result<String, CompileError> {
        let mut emitter = LeanEmitter::new();

        let binding = LeanBinding {
            interface_name: interface_name.to_string(),
            impl_type,
            doc: None,
        };

        emitter.emit_binding(&binding);
        emitter.emit_binding_theorem(&binding);

        Ok(emitter.finish())
    }

    /// Generate complete module with traits, impls, and bindings from AST
    pub fn generate_module_with_traits(
        &self,
        module: &HirModule,
        traits: &[TraitDef],
        impls: &[ImplBlock],
        bindings: &[(String, LeanType)],
    ) -> Result<String, CompileError> {
        let mut emitter = LeanEmitter::new();

        // Generate module header
        let module_name = self
            .module_name
            .clone()
            .or_else(|| module.name.clone())
            .unwrap_or_else(|| "Main".to_string());

        emitter.emit_header(&module_name);

        // Generate type definitions from structs and enums
        let type_translator = TypeTranslator::new(&module.types);
        let trait_translator = TraitTranslator::new(&type_translator);

        // Emit type classes from traits
        if !traits.is_empty() {
            emitter.emit_comment("Type classes (from traits)");
            for trait_def in traits {
                let lean_class = trait_translator.translate_trait(trait_def)?;
                emitter.emit_class(&lean_class);
            }
            emitter.emit_blank();
        }

        // Emit instances from impls
        if !impls.is_empty() {
            emitter.emit_comment("Instances (from impl blocks)");
            for impl_block in impls {
                let lean_instance = trait_translator.translate_impl(impl_block)?;
                emitter.emit_instance(&lean_instance, self.generate_stubs);
            }
            emitter.emit_blank();
        }

        // Emit interface bindings for static dispatch
        if !bindings.is_empty() {
            emitter.emit_comment("Interface bindings (static dispatch)");
            for (interface_name, impl_type) in bindings {
                let binding = LeanBinding {
                    interface_name: interface_name.clone(),
                    impl_type: impl_type.clone(),
                    doc: None,
                };
                emitter.emit_binding(&binding);
                emitter.emit_binding_theorem(&binding);
            }
            emitter.emit_blank();
        }

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

        // Emit static polymorphism verification theorems
        if !traits.is_empty() && !impls.is_empty() {
            emitter.emit_blank();
            emitter.emit_comment("Static polymorphism verification theorems");

            // Generate coherence theorem for each trait
            for trait_def in traits {
                let impl_types: Vec<&str> = impls
                    .iter()
                    .filter(|i| i.trait_name.as_ref() == Some(&trait_def.name))
                    .filter_map(|i| {
                        if let simple_parser::ast::Type::Simple(name) = &i.target_type {
                            Some(name.as_str())
                        } else {
                            None
                        }
                    })
                    .collect();

                if !impl_types.is_empty() {
                    let coherence = StaticPolyTheorems::coherence_theorem(&trait_def.name, &impl_types);
                    emitter.emit_raw(&coherence);
                }
            }
        }

        emitter.emit_footer(&module_name);
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

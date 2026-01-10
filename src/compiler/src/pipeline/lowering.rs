//! AST → HIR → MIR lowering and type checking.

use simple_type::check as type_check;
use std::path::Path;

use super::core::CompilerPipeline;
use crate::hir;
use crate::mir;
use crate::verification_checker::VerificationChecker;
use crate::CompileError;

impl CompilerPipeline {
    /// Type check and lower AST to MIR.
    ///
    /// This is a common pipeline step extracted from compile_source_to_memory_native
    /// and compile_source_to_memory_native_for_target.
    pub(super) fn type_check_and_lower(
        &mut self,
        ast_module: &simple_parser::ast::Module,
    ) -> Result<mir::MirModule, CompileError> {
        // Clear previous verification violations
        self.verification_violations.clear();

        // Type check
        type_check(&ast_module.items).map_err(|e| CompileError::Semantic(format!("{:?}", e)))?;

        // Lower AST to HIR
        let hir_module = hir::lower(ast_module)
            .map_err(|e| CompileError::Semantic(format!("HIR lowering: {e}")))?;

        // Emit HIR if requested (LLM-friendly #886)
        if let Some(path) = &self.emit_hir {
            crate::ir_export::export_hir(&hir_module, path.as_deref())
                .map_err(|e| CompileError::Semantic(e))?;
        }

        // Check architecture rules if any are defined (#1026-1035)
        if !hir_module.arch_rules.is_empty() {
            let arch_config =
                crate::arch_rules::ArchRulesConfig::from_hir_rules(&hir_module.arch_rules);
            let checker = crate::arch_rules::ArchRulesChecker::new(arch_config);
            let violations = checker.check_module(&hir_module);

            if !violations.is_empty() {
                let msg = violations
                    .iter()
                    .map(|v| format!("Architecture violation: {}", v.message))
                    .collect::<Vec<_>>()
                    .join("\n");
                return Err(CompileError::Semantic(msg));
            }
        }

        // Check verification constraints (#1840-1909)
        let mut verifier = VerificationChecker::new(self.verification_strict);
        verifier.check_module(&hir_module);

        if verifier.has_violations() {
            self.verification_violations = verifier.violations().to_vec();

            if self.verification_strict {
                let msg = verifier.error_messages().join("\n");
                return Err(CompileError::Semantic(format!(
                    "Verification errors:\n{}",
                    msg
                )));
            } else {
                // Log warnings but continue
                for violation in verifier.violations() {
                    tracing::warn!("{}", violation);
                }
            }
        }

        // Lower HIR to MIR with contract mode (and DI config if available)
        let di_config = self.project.as_ref().and_then(|p| p.di_config.clone());
        let mut mir_module =
            mir::lower_to_mir_with_mode_and_di(&hir_module, self.contract_mode, di_config)
                .map_err(|e| CompileError::Semantic(format!("MIR lowering: {e}")))?;

        // Ghost erasure pass: remove ghost variables before codegen
        let (ghost_stats, ghost_errors) = mir::erase_ghost_from_module(&mut mir_module);

        if !ghost_errors.is_empty() {
            let msg = ghost_errors
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join("\n");
            return Err(CompileError::Semantic(format!(
                "Ghost erasure errors:\n{}",
                msg
            )));
        }

        if ghost_stats.ghost_params_erased > 0 || ghost_stats.ghost_locals_erased > 0 {
            tracing::debug!(
                "Ghost erasure: {} params, {} locals, {} instructions erased",
                ghost_stats.ghost_params_erased,
                ghost_stats.ghost_locals_erased,
                ghost_stats.instructions_erased
            );
        }

        // Emit MIR if requested (LLM-friendly #887)
        if let Some(path) = &self.emit_mir {
            crate::ir_export::export_mir(&mir_module, path.as_deref())
                .map_err(|e| CompileError::Semantic(e))?;
        }

        Ok(mir_module)
    }

    /// Type check and lower AST to MIR with module resolution support.
    ///
    /// This variant enables compile-time type checking for imports by loading
    /// type definitions from imported modules.
    ///
    /// # Arguments
    /// * `ast_module` - The AST module to lower
    /// * `source_file` - Path to the source file (for resolving relative imports)
    pub(super) fn type_check_and_lower_with_context(
        &mut self,
        ast_module: &simple_parser::ast::Module,
        source_file: &Path,
    ) -> Result<mir::MirModule, CompileError> {
        // Clear previous verification violations
        self.verification_violations.clear();

        // Type check
        type_check(&ast_module.items).map_err(|e| CompileError::Semantic(format!("{:?}", e)))?;

        // Lower AST to HIR with module resolution support
        let hir_module = hir::lower_with_context(ast_module, source_file)
            .map_err(|e| CompileError::Semantic(format!("HIR lowering: {e}")))?;

        // Emit HIR if requested (LLM-friendly #886)
        if let Some(path) = &self.emit_hir {
            crate::ir_export::export_hir(&hir_module, path.as_deref())
                .map_err(|e| CompileError::Semantic(e))?;
        }

        // Check architecture rules if any are defined (#1026-1035)
        if !hir_module.arch_rules.is_empty() {
            let arch_config =
                crate::arch_rules::ArchRulesConfig::from_hir_rules(&hir_module.arch_rules);
            let checker = crate::arch_rules::ArchRulesChecker::new(arch_config);
            let violations = checker.check_module(&hir_module);

            if !violations.is_empty() {
                let msg = violations
                    .iter()
                    .map(|v| format!("Architecture violation: {}", v.message))
                    .collect::<Vec<_>>()
                    .join("\n");
                return Err(CompileError::Semantic(msg));
            }
        }

        // Check verification constraints (#1840-1909)
        let mut verifier = VerificationChecker::new(self.verification_strict);
        verifier.check_module(&hir_module);

        if verifier.has_violations() {
            self.verification_violations = verifier.violations().to_vec();

            if self.verification_strict {
                let msg = verifier.error_messages().join("\n");
                return Err(CompileError::Semantic(format!(
                    "Verification errors:\n{}",
                    msg
                )));
            } else {
                // Log warnings but continue
                for violation in verifier.violations() {
                    tracing::warn!("{}", violation);
                }
            }
        }

        // Lower HIR to MIR with contract mode (and DI config if available)
        let di_config = self.project.as_ref().and_then(|p| p.di_config.clone());
        let mut mir_module =
            mir::lower_to_mir_with_mode_and_di(&hir_module, self.contract_mode, di_config)
                .map_err(|e| CompileError::Semantic(format!("MIR lowering: {e}")))?;

        // Ghost erasure pass: remove ghost variables before codegen
        let (ghost_stats, ghost_errors) = mir::erase_ghost_from_module(&mut mir_module);

        if !ghost_errors.is_empty() {
            let msg = ghost_errors
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join("\n");
            return Err(CompileError::Semantic(format!(
                "Ghost erasure errors:\n{}",
                msg
            )));
        }

        if ghost_stats.ghost_params_erased > 0 || ghost_stats.ghost_locals_erased > 0 {
            tracing::debug!(
                "Ghost erasure: {} params, {} locals, {} instructions erased",
                ghost_stats.ghost_params_erased,
                ghost_stats.ghost_locals_erased,
                ghost_stats.instructions_erased
            );
        }

        // Emit MIR if requested (LLM-friendly #887)
        if let Some(path) = &self.emit_mir {
            crate::ir_export::export_mir(&mir_module, path.as_deref())
                .map_err(|e| CompileError::Semantic(e))?;
        }

        Ok(mir_module)
    }
}

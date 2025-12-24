//! AST → HIR → MIR lowering and type checking.

use simple_type::check as type_check;

use super::core::CompilerPipeline;
use crate::hir;
use crate::mir;
use crate::CompileError;

impl CompilerPipeline {
    /// Type check and lower AST to MIR.
    ///
    /// This is a common pipeline step extracted from compile_source_to_memory_native
    /// and compile_source_to_memory_native_for_target.
    pub(super) fn type_check_and_lower(
        &self,
        ast_module: &simple_parser::ast::Module,
    ) -> Result<mir::MirModule, CompileError> {
        // Type check
        type_check(&ast_module.items)
            .map_err(|e| CompileError::Semantic(format!("{:?}", e)))?;

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

        // Lower HIR to MIR with contract mode (and DI config if available)
        let di_config = self.project.as_ref().and_then(|p| p.di_config.clone());
        let mir_module = mir::lower_to_mir_with_mode_and_di(&hir_module, self.contract_mode, di_config)
            .map_err(|e| CompileError::Semantic(format!("MIR lowering: {e}")))?;

        // Emit MIR if requested (LLM-friendly #887)
        if let Some(path) = &self.emit_mir {
            crate::ir_export::export_mir(&mir_module, path.as_deref())
                .map_err(|e| CompileError::Semantic(e))?;
        }

        Ok(mir_module)
    }
}

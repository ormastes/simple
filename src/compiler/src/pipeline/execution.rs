//! Interpreter fallback, runtime setup, and execution management.

use std::collections::HashSet;
use std::fs;
use std::path::Path;
use std::sync::Arc;

use simple_common::gc::GcAllocator;
use simple_common::target::Target;
use simple_parser::ast::Node;
use simple_type::check as type_check;
use tracing::instrument;

use super::core::CompilerPipeline;
use crate::compilability::analyze_module;
use crate::import_loader::{has_script_statements, load_module_with_imports};
use crate::interpreter::evaluate_module_with_di_and_aop;
use crate::mir;
use crate::monomorphize::monomorphize_module;
use crate::value::FUNC_MAIN;
use crate::CompileError;

// Re-export SMF generation functions for backward compatibility
pub use crate::smf_builder::{
    generate_smf_bytes, generate_smf_bytes_for_target, generate_smf_from_object_for_target,
};

// Provide the old generate_smf_from_object function for compatibility
pub fn generate_smf_from_object(object_code: &[u8], gc: Option<&Arc<dyn GcAllocator>>) -> Vec<u8> {
    crate::smf_builder::generate_smf_from_object(object_code, gc)
}

impl CompilerPipeline {
    pub(super) fn evaluate_module_with_project(&self, items: &[Node]) -> Result<i32, CompileError> {
        let di_config = self.project.as_ref().and_then(|p| p.di_config.as_ref());
        let aop_config = self.project.as_ref().and_then(|p| p.aop_config.as_ref());
        evaluate_module_with_di_and_aop(items, di_config, aop_config)
    }

    /// Compile a Simple source file to an SMF at `out`.
    ///
    /// Currently supports `main = <integer>` which returns the integer value.
    #[instrument(skip(self, source_path, out))]
    pub fn compile(&mut self, source_path: &Path, out: &Path) -> Result<(), CompileError> {
        let module = load_module_with_imports(source_path, &mut HashSet::new())?;
        let smf_bytes = self.compile_module_to_memory(module)?;
        fs::write(out, smf_bytes).map_err(|e| CompileError::Io(format!("{e}")))
    }

    /// Compile a Simple source file with automatic project detection.
    ///
    /// This method searches parent directories for simple.toml and
    /// sets up the project context for module resolution.
    #[instrument(skip(self, source_path, out))]
    pub fn compile_with_project_detection(
        &mut self,
        source_path: &Path,
        out: &Path,
    ) -> Result<(), CompileError> {
        // Detect project context if not already set
        if self.project.is_none() {
            let project = crate::project::ProjectContext::detect(source_path)?;
            self.project = Some(project);
        }

        self.compile(source_path, out)
    }

    /// Compile source string to SMF bytes in memory (no disk I/O).
    ///
    /// This uses the interpreter mode which supports all language features.
    /// Lint diagnostics are stored and can be retrieved via `lint_diagnostics()`.
    #[instrument(skip(self, source))]
    pub fn compile_source_to_memory(&mut self, source: &str) -> Result<Vec<u8>, CompileError> {
        let mut parser = simple_parser::Parser::new(source);
        let module = parser
            .parse()
            .map_err(|e| CompileError::Parse(format!("{e}")))?;
        
        // Emit AST if requested (LLM-friendly #885)
        if let Some(path) = &self.emit_ast {
            crate::ir_export::export_ast(&module, path.as_deref())
                .map_err(|e| CompileError::Semantic(e))?;
        }
        
        self.compile_module_to_memory(module)
    }

    pub(super) fn compile_module_to_memory(
        &mut self,
        module: simple_parser::ast::Module,
    ) -> Result<Vec<u8>, CompileError> {
        // Clear previous lint diagnostics
        self.lint_diagnostics.clear();

        // Validate release mode configuration (#1034-1035)
        self.validate_release_config()?;

        // Monomorphization: specialize generic functions for concrete types
        let module = monomorphize_module(&module);

        // Run lint checks
        self.run_lint_checks(&module.items)?;

        // Validate function effects against module capabilities
        self.validate_capabilities(&module.items)?;

        // Check trait coherence (orphan rule, overlap, associated types, blanket conflicts)
        self.check_trait_coherence(&module.items)?;

        // If the module has script-style statements, skip type_check and interpret directly.
        if !has_script_statements(&module.items) {
            // Type inference/checking (features #13/#14 scaffolding)
            type_check(&module.items)
                .map_err(|e| CompileError::Semantic(format!("{:?}", e)))?;
        }

        // Extract the main function's return value
        let main_value = self.evaluate_module_with_project(&module.items)?;

        Ok(generate_smf_bytes(main_value, self.gc.as_ref()))
    }

    /// Compile a Simple source file to an SMF at `out` using native codegen.
    ///
    /// This uses the native compilation pipeline: HIR → MIR → native backend.
    /// Faster execution but supports fewer language features than interpreter mode.
    #[instrument(skip(self, source_path, out))]
    pub fn compile_native(&mut self, source_path: &Path, out: &Path) -> Result<(), CompileError> {
        let module = load_module_with_imports(source_path, &mut HashSet::new())?;
        let smf_bytes = self.compile_module_to_memory_native(module)?;
        fs::write(out, smf_bytes).map_err(|e| CompileError::Io(format!("{e}")))
    }

    /// Compile source string to SMF bytes using native codegen (HIR → MIR → backend).
    ///
    /// This generates actual machine code rather than using the interpreter.
    /// The resulting SMF can be executed directly.
    /// Lint diagnostics are stored and can be retrieved via `lint_diagnostics()`.
    #[instrument(skip(self, source))]
    pub fn compile_source_to_memory_native(
        &mut self,
        source: &str,
    ) -> Result<Vec<u8>, CompileError> {
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser
            .parse()
            .map_err(|e| CompileError::Parse(format!("{e}")))?;
        
        // Emit AST if requested (LLM-friendly #885)
        if let Some(path) = &self.emit_ast {
            crate::ir_export::export_ast(&ast_module, path.as_deref())
                .map_err(|e| CompileError::Semantic(e))?;
        }
        
        self.compile_module_to_memory_native(ast_module)
    }

    pub(super) fn compile_module_to_memory_native(
        &mut self,
        ast_module: simple_parser::ast::Module,
    ) -> Result<Vec<u8>, CompileError> {
        // Clear previous lint diagnostics
        self.lint_diagnostics.clear();

        // Validate release mode configuration (#1034-1035)
        self.validate_release_config()?;

        // 2. Monomorphization: specialize generic functions for concrete types
        let ast_module = monomorphize_module(&ast_module);

        // 3. Run lint checks
        self.run_lint_checks(&ast_module.items)?;

        // 4. Validate capabilities
        self.validate_capabilities(&ast_module.items)?;

        // 5. Check trait coherence
        self.check_trait_coherence(&ast_module.items)?;

        // If script-style statements exist, interpret directly and wrap result.
        if has_script_statements(&ast_module.items) {
            let main_value = self.evaluate_module_with_project(&ast_module.items)?;
            return Ok(generate_smf_bytes(main_value, self.gc.as_ref()));
        }

        // 4. Compilability analysis for hybrid execution
        let compilability = analyze_module(&ast_module.items);
        let non_compilable: HashSet<String> = compilability
            .iter()
            .filter(|(_, status)| !status.is_compilable())
            .map(|(name, _)| name.clone())
            .collect();

        // 5-7. Type check and lower to MIR
        let mut mir_module = self.type_check_and_lower(&ast_module)?;

        // Check if we have a main function. If not, fall back to interpreter mode.
        // This handles cases like `main = 42` which are module-level constants,
        // not function declarations.
        let has_main_function = mir_module.functions.iter().any(|f| f.name == FUNC_MAIN);

        if !has_main_function {
            // Fallback: evaluate via interpreter and wrap result
            let main_value = self.evaluate_module_with_project(&ast_module.items)?;
            return Ok(generate_smf_bytes(main_value, self.gc.as_ref()));
        }

        // 8. Apply hybrid transformation if needed
        if !non_compilable.is_empty() {
            mir::apply_hybrid_transform(&mut mir_module, &non_compilable);
            tracing::debug!(
                "Hybrid execution: {} functions require interpreter fallback",
                non_compilable.len()
            );
        }

        // 9. Generate machine code via selected backend
        let object_code = self.compile_mir_to_object(&mir_module, Target::host())?;

        // 10. Wrap object code in SMF format
        Ok(generate_smf_from_object(&object_code, self.gc.as_ref()))
    }

    /// Compile source code to SMF bytes for a specific target architecture.
    ///
    /// This enables cross-compilation to different architectures (x86_64, aarch64, etc.).
    /// Uses native codegen (HIR → MIR → backend) with the specified target.
    #[instrument(skip(self, source))]
    pub fn compile_source_to_memory_for_target(
        &mut self,
        source: &str,
        target: Target,
    ) -> Result<Vec<u8>, CompileError> {
        // Clear previous lint diagnostics
        self.lint_diagnostics.clear();

        // Validate release mode configuration (#1034-1035)
        self.validate_release_config()?;

        // 1. Parse source to AST
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser
            .parse()
            .map_err(|e| CompileError::Parse(format!("{e}")))?;

        // 2. Monomorphization: specialize generic functions for concrete types
        let ast_module = monomorphize_module(&ast_module);

        // 3. Run lint checks
        self.run_lint_checks(&ast_module.items)?;

        // 4. Validate capabilities
        self.validate_capabilities(&ast_module.items)?;

        // 5. Check trait coherence
        self.check_trait_coherence(&ast_module.items)?;

        // If script-style statements exist, interpret directly and wrap result.
        if has_script_statements(&ast_module.items) {
            let main_value = self.evaluate_module_with_project(&ast_module.items)?;
            return Ok(generate_smf_bytes_for_target(
                main_value,
                self.gc.as_ref(),
                target,
            ));
        }

        // 4. Compilability analysis for hybrid execution
        let compilability = analyze_module(&ast_module.items);
        let non_compilable: HashSet<String> = compilability
            .iter()
            .filter(|(_, status)| !status.is_compilable())
            .map(|(name, _)| name.clone())
            .collect();

        // 5-7. Type check and lower to MIR
        let mut mir_module = self.type_check_and_lower(&ast_module)?;

        // Check if we have a main function. If not, fall back to interpreter mode.
        let has_main_function = mir_module.functions.iter().any(|f| f.name == FUNC_MAIN);

        if !has_main_function {
            // Fallback: evaluate via interpreter and wrap result
            // Note: Interpreter result is architecture-neutral (just an i32)
            let main_value = self.evaluate_module_with_project(&ast_module.items)?;
            return Ok(generate_smf_bytes_for_target(
                main_value,
                self.gc.as_ref(),
                target,
            ));
        }

        // 8. Apply hybrid transformation if needed
        if !non_compilable.is_empty() {
            mir::apply_hybrid_transform(&mut mir_module, &non_compilable);
            tracing::debug!(
                "Hybrid execution (target {:?}): {} functions require interpreter fallback",
                target,
                non_compilable.len()
            );
        }

        // 9. Generate machine code via selected backend for the target architecture
        let object_code = self.compile_mir_to_object(&mir_module, target)?;

        // 10. Wrap object code in SMF format for the target
        Ok(generate_smf_from_object_for_target(
            &object_code,
            self.gc.as_ref(),
            target,
        ))
    }
}

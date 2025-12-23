//! Compiler pipeline and SMF generation.
//!
//! This module contains the main compilation pipeline that transforms
//! source code into SMF (Simple Module Format) binaries.
//!
//! ## Compilation Modes
//!
//! The pipeline supports two compilation modes:
//!
//! 1. **Interpreter mode** (default): Uses the tree-walking interpreter to
//!    evaluate the program, then wraps the result in a minimal SMF binary.
//!    This mode supports all language features.
//!
//! 2. **Native mode**: Compiles through HIR → MIR → native backend to generate
//!    actual machine code. This mode is faster but supports fewer features.
//!    Use `compile_native()` or `compile_source_to_memory_native()` for this mode.

pub mod module_loader;
pub mod script_detection;

use std::collections::HashSet;
use std::fs;
use std::path::Path;
use std::sync::Arc;

use simple_common::gc::GcAllocator;
use simple_common::target::Target;
use simple_type::check as type_check;
use tracing::instrument;

use simple_parser::ast::{Capability, Node};

use crate::build_mode::BuildMode;
use crate::codegen::{backend_trait::NativeBackend, BackendKind, Codegen};
use crate::codegen::llvm::LlvmBackend;
use crate::compilability::analyze_module;
use crate::hir;
use crate::import_loader::{has_script_statements, load_module_with_imports};
use crate::interpreter::evaluate_module_with_di_and_aop;
use crate::lint::{LintChecker, LintConfig, LintDiagnostic};
use crate::mir::{self, ContractMode};
use crate::monomorphize::monomorphize_module;
use crate::project::ProjectContext;
use crate::trait_coherence::CoherenceChecker;
use crate::value::FUNC_MAIN;
use crate::CompileError;

/// Minimal compiler pipeline that validates syntax then emits a runnable SMF.
pub struct CompilerPipeline {
    gc: Option<Arc<dyn GcAllocator>>,
    /// Optional project context for multi-file compilation
    project: Option<ProjectContext>,
    /// Lint configuration (can be set independently of project)
    lint_config: Option<LintConfig>,
    /// Lint diagnostics from the last compilation
    lint_diagnostics: Vec<LintDiagnostic>,
    /// Contract checking mode (CTR-040 to CTR-043)
    contract_mode: ContractMode,
    /// Build mode (debug/release) for validation and optimization (#1034-1035)
    build_mode: BuildMode,
}

impl CompilerPipeline {
    pub fn new() -> Result<Self, CompileError> {
        Ok(Self {
            gc: None,
            project: None,
            lint_config: None,
            lint_diagnostics: Vec::new(),
            contract_mode: ContractMode::All,
            build_mode: BuildMode::default(),
        })
    }

    pub fn with_gc(gc: Arc<dyn GcAllocator>) -> Result<Self, CompileError> {
        Ok(Self {
            gc: Some(gc),
            project: None,
            lint_config: None,
            lint_diagnostics: Vec::new(),
            contract_mode: ContractMode::All,
            build_mode: BuildMode::default(),
        })
    }

    /// Create a pipeline with a project context
    pub fn with_project(project: ProjectContext) -> Result<Self, CompileError> {
        let lint_config = Some(project.lint_config.clone());
        Ok(Self {
            gc: None,
            project: Some(project),
            lint_config,
            lint_diagnostics: Vec::new(),
            contract_mode: ContractMode::All,
            build_mode: BuildMode::default(),
        })
    }

    /// Create a pipeline with both GC and project context
    pub fn with_gc_and_project(
        gc: Arc<dyn GcAllocator>,
        project: ProjectContext,
    ) -> Result<Self, CompileError> {
        let lint_config = Some(project.lint_config.clone());
        Ok(Self {
            gc: Some(gc),
            project: Some(project),
            lint_config,
            lint_diagnostics: Vec::new(),
            contract_mode: ContractMode::All,
            build_mode: BuildMode::default(),
        })
    }

    /// Set the project context
    pub fn set_project(&mut self, project: ProjectContext) {
        self.lint_config = Some(project.lint_config.clone());
        self.project = Some(project);
    }

    /// Get the project context if set
    pub fn project(&self) -> Option<&ProjectContext> {
        self.project.as_ref()
    }

    /// Set the lint configuration explicitly
    pub fn set_lint_config(&mut self, config: LintConfig) {
        self.lint_config = Some(config);
    }

    /// Get the lint configuration
    pub fn lint_config(&self) -> Option<&LintConfig> {
        self.lint_config.as_ref()
    }

    /// Get lint diagnostics from the last compilation
    pub fn lint_diagnostics(&self) -> &[LintDiagnostic] {
        &self.lint_diagnostics
    }

    /// Take lint diagnostics (clears internal storage)
    pub fn take_lint_diagnostics(&mut self) -> Vec<LintDiagnostic> {
        std::mem::take(&mut self.lint_diagnostics)
    }

    /// Check if the last compilation had lint errors
    pub fn has_lint_errors(&self) -> bool {
        self.lint_diagnostics.iter().any(|d| d.is_error())
    }

    /// Check if the last compilation had lint warnings
    pub fn has_lint_warnings(&self) -> bool {
        self.lint_diagnostics.iter().any(|d| d.is_warning())
    }

    /// Set the contract checking mode
    ///
    /// This controls when contract checks (preconditions, postconditions, invariants)
    /// are emitted during native compilation:
    /// - `Off`: No contract checks emitted
    /// - `Boundary`: Only check contracts at public API boundaries
    /// - `All`: Check all contracts (default)
    pub fn set_contract_mode(&mut self, mode: ContractMode) {
        self.contract_mode = mode;
    }

    /// Get the current contract checking mode
    pub fn contract_mode(&self) -> ContractMode {
        self.contract_mode
    }

    /// Set the build mode (debug/release)
    ///
    /// This controls optimizations and validation rules:
    /// - `Debug`: Full diagnostics, minimal optimizations (default)
    /// - `Release`: Optimizations enabled, production validations (#1034-1035)
    pub fn set_build_mode(&mut self, mode: BuildMode) {
        self.build_mode = mode;
    }

    /// Get the current build mode
    pub fn build_mode(&self) -> BuildMode {
        self.build_mode
    }

    /// Validate AOP/DI configuration for release builds (#1034-1035).
    ///
    /// In release mode:
    /// - #1034: DI profile must not be "test"
    /// - #1035: AOP runtime interceptors must not be enabled
    fn validate_release_config(&self) -> Result<(), CompileError> {
        if !self.build_mode.is_release() {
            return Ok(());
        }

        // #1034: Release MUST NOT select test profile
        if let Some(ref project) = self.project {
            if let Some(ref di_config) = project.di_config {
                if di_config.profiles.contains_key("test") {
                    // Check if any active profile is "test"
                    // For now, we check if "test" profile exists and has bindings
                    if let Some(test_profile) = di_config.profiles.get("test") {
                        if !test_profile.bindings.is_empty() {
                            return Err(CompileError::Semantic(
                                "Release build must not select test DI profile (#1034). \
                                 Found test profile with bindings. \
                                 Either remove the test profile or use debug mode."
                                    .to_string(),
                            ));
                        }
                    }
                }
            }

            // #1035: Release MUST NOT enable runtime interceptors
            if let Some(ref aop_config) = project.aop_config {
                if aop_config.runtime_enabled {
                    return Err(CompileError::Semantic(
                        "Release build must not enable runtime AOP interceptors (#1035). \
                         Set runtime_enabled=false in AOP config or use debug mode."
                            .to_string(),
                    ));
                }
            }
        }

        Ok(())
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
            let project = ProjectContext::detect(source_path)?;
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
        self.compile_module_to_memory(module)
    }

    fn compile_module_to_memory(
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
            type_check(&module.items).map_err(|e| CompileError::Semantic(format!("{:?}", e)))?;
        }

        // Extract the main function's return value
        let main_value = self.evaluate_module_with_project(&module.items)?;

        Ok(generate_smf_bytes(main_value, self.gc.as_ref()))
    }

    /// Run lint checks on AST items.
    ///
    /// Stores diagnostics in `self.lint_diagnostics`.
    /// Returns an error if any lint is set to deny level.
    fn run_lint_checks(&mut self, items: &[simple_parser::ast::Node]) -> Result<(), CompileError> {
        let mut checker = if let Some(ref config) = self.lint_config {
            LintChecker::with_config(config.clone())
        } else {
            LintChecker::new()
        };

        checker.check_module(items);
        self.lint_diagnostics = checker.take_diagnostics();

        // If any lint has deny level, return an error
        if self.has_lint_errors() {
            let errors: Vec<String> = self
                .lint_diagnostics
                .iter()
                .filter(|d| d.is_error())
                .map(|d| d.format())
                .collect();
            return Err(CompileError::Lint(errors.join("\n")));
        }

        Ok(())
    }

    /// Check trait coherence rules (orphan rule, overlap, associated types, blanket conflicts).
    ///
    /// This validates trait implementations to ensure:
    /// - Orphan rule: At least one of trait or type is local
    /// - No overlap: Implementations don't conflict
    /// - Associated type coherence: Consistent associated types
    /// - Blanket impl conflicts: Blanket impls don't conflict with specific ones
    fn check_trait_coherence(&self, items: &[Node]) -> Result<(), CompileError> {
        let mut checker = CoherenceChecker::new();
        let errors = checker.check_module(items);

        if !errors.is_empty() {
            let error_messages: Vec<String> = errors
                .iter()
                .map(|e| format!("{:?}", e))
                .collect();
            return Err(CompileError::Semantic(format!(
                "Trait coherence errors:\n{}",
                error_messages.join("\n")
            )));
        }

        Ok(())
    }

    fn evaluate_module_with_project(
        &self,
        items: &[simple_parser::ast::Node],
    ) -> Result<i32, CompileError> {
        let di_config = self.project.as_ref().and_then(|p| p.di_config.as_ref());
        let aop_config = self.project.as_ref().and_then(|p| p.aop_config.as_ref());
        evaluate_module_with_di_and_aop(items, di_config, aop_config)
    }

    /// Validate function effects against module capabilities.
    ///
    /// If a module declares `requires [pure, io]`, all functions with effects
    /// must only use effects that correspond to those capabilities.
    ///
    /// Effects map to capabilities as follows:
    /// - @pure → Pure capability
    /// - @io → Io capability
    /// - @net → Net capability
    /// - @fs → Fs capability
    /// - @unsafe → Unsafe capability
    /// - @async → Always allowed (execution model, not capability)
    fn validate_capabilities(&self, items: &[Node]) -> Result<(), CompileError> {
        // Extract module capabilities from RequiresCapabilities statement
        let mut capabilities: Vec<Capability> = Vec::new();
        for item in items {
            if let Node::RequiresCapabilities(stmt) = item {
                capabilities = stmt.capabilities.clone();
                break; // Only one requires statement per module
            }
        }

        // If no capabilities declared, module is unrestricted
        if capabilities.is_empty() {
            return Ok(());
        }

        // Validate each function's effects against capabilities
        for item in items {
            if let Node::Function(func) = item {
                for effect in &func.effects {
                    let cap = Capability::from_effect(effect);

                    // Async is always allowed (execution model, not capability)
                    if cap.is_none() {
                        continue;
                    }

                    let cap = cap.unwrap();
                    if !capabilities.contains(&cap) {
                        return Err(CompileError::Semantic(format!(
                            "function '{}' has @{} effect but module only allows capabilities: [{}]",
                            func.name,
                            effect.decorator_name(),
                            capabilities.iter().map(|c| c.name()).collect::<Vec<_>>().join(", ")
                        )));
                    }
                }
            }
        }

        Ok(())
    }

    /// Type check and lower AST to MIR.
    /// 
    /// This is a common pipeline step extracted from compile_source_to_memory_native
    /// and compile_source_to_memory_native_for_target.
    fn type_check_and_lower(&self, ast_module: &simple_parser::ast::Module) -> Result<mir::MirModule, CompileError> {
        // Type check
        type_check(&ast_module.items).map_err(|e| CompileError::Semantic(format!("{:?}", e)))?;

        // Lower AST to HIR
        let hir_module = hir::lower(ast_module)
            .map_err(|e| CompileError::Semantic(format!("HIR lowering: {e}")))?;

        // Check architecture rules if any are defined (#1026-1035)
        if !hir_module.arch_rules.is_empty() {
            let arch_config = crate::arch_rules::ArchRulesConfig::from_hir_rules(&hir_module.arch_rules);
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
        mir::lower_to_mir_with_mode_and_di(&hir_module, self.contract_mode, di_config)
            .map_err(|e| CompileError::Semantic(format!("MIR lowering: {e}")))
    }

    fn compile_mir_to_object(
        &self,
        mir_module: &mir::MirModule,
        target: Target,
    ) -> Result<Vec<u8>, CompileError> {
        if target.arch.is_32bit() && cfg!(not(feature = "llvm")) {
            return Err(CompileError::Codegen(
                "32-bit targets require the LLVM backend; build with --features llvm".to_string(),
            ));
        }

        let coverage_enabled = crate::coverage::is_coverage_enabled();

        match BackendKind::for_target(&target) {
            BackendKind::Cranelift => {
                let codegen =
                    Codegen::for_target(target).map_err(|e| CompileError::Codegen(format!("{e}")))?;
                codegen
                    .compile_module(mir_module)
                    .map_err(|e| CompileError::Codegen(format!("{e}")))
            }
            BackendKind::Llvm => {
                let backend = LlvmBackend::new(target)
                    .map_err(|e| CompileError::Codegen(format!("{e}")))?;
                backend
                    .with_coverage(coverage_enabled)
                    .compile(mir_module)
                    .map_err(|e| CompileError::Codegen(format!("{e}")))
            }
        }
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
        self.compile_module_to_memory_native(ast_module)
    }

    fn compile_module_to_memory_native(
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

// Re-export SMF generation functions for backward compatibility
pub use crate::smf_builder::{generate_smf_bytes, generate_smf_bytes_for_target, generate_smf_from_object_for_target};

// Provide the old generate_smf_from_object function for compatibility
pub fn generate_smf_from_object(object_code: &[u8], gc: Option<&Arc<dyn GcAllocator>>) -> Vec<u8> {
    crate::smf_builder::generate_smf_from_object(object_code, gc)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::elf_utils::{extract_elf_text_section, get_section_name};
    use simple_common::target::{TargetArch, TargetOS};

    /// Debug helper to list ELF sections
    fn list_elf_sections(elf_data: &[u8]) -> Vec<String> {
        let mut sections = Vec::new();

        if elf_data.len() < 64 || &elf_data[0..4] != b"\x7fELF" {
            return sections;
        }

        let e_shoff = u64::from_le_bytes(elf_data[40..48].try_into().unwrap()) as usize;
        let e_shentsize = u16::from_le_bytes(elf_data[58..60].try_into().unwrap()) as usize;
        let e_shnum = u16::from_le_bytes(elf_data[60..62].try_into().unwrap()) as usize;
        let e_shstrndx = u16::from_le_bytes(elf_data[62..64].try_into().unwrap()) as usize;

        if e_shoff == 0 || e_shnum == 0 {
            sections.push(format!("e_shoff={}, e_shnum={}", e_shoff, e_shnum));
            return sections;
        }

        // Get string table
        let shstrtab_hdr_offset = e_shoff + e_shstrndx * e_shentsize;
        if shstrtab_hdr_offset + e_shentsize > elf_data.len() {
            sections.push("shstrtab header out of bounds".to_string());
            return sections;
        }
        let shstrtab_offset = u64::from_le_bytes(
            elf_data[shstrtab_hdr_offset + 24..shstrtab_hdr_offset + 32]
                .try_into()
                .unwrap(),
        ) as usize;
        let shstrtab_size = u64::from_le_bytes(
            elf_data[shstrtab_hdr_offset + 32..shstrtab_hdr_offset + 40]
                .try_into()
                .unwrap(),
        ) as usize;

        if shstrtab_offset + shstrtab_size > elf_data.len() {
            sections.push(format!(
                "shstrtab out of bounds: offset={}, size={}",
                shstrtab_offset, shstrtab_size
            ));
            return sections;
        }
        let shstrtab = &elf_data[shstrtab_offset..shstrtab_offset + shstrtab_size];

        for i in 0..e_shnum {
            let sh_offset = e_shoff + i * e_shentsize;
            if sh_offset + e_shentsize > elf_data.len() {
                continue;
            }

            let sh_name =
                u32::from_le_bytes(elf_data[sh_offset..sh_offset + 4].try_into().unwrap()) as usize;

            if let Some(name) = get_section_name(shstrtab, sh_name) {
                let sec_offset = u64::from_le_bytes(
                    elf_data[sh_offset + 24..sh_offset + 32].try_into().unwrap(),
                ) as usize;
                let sec_size = u64::from_le_bytes(
                    elf_data[sh_offset + 32..sh_offset + 40].try_into().unwrap(),
                ) as usize;

                sections.push(format!(
                    "Section[{}]: '{}' offset={} size={}",
                    i, name, sec_offset, sec_size
                ));
            }
        }

        sections
    }

    #[test]
    fn test_elf_extraction_from_codegen() {
        // Compile a simple function through Cranelift
        // Note: "main = 42" is a module-level constant, not a function
        // We need an actual function for codegen
        let source = "fn main() -> i64:\n    return 42";
        let mut parser = simple_parser::Parser::new(source);
        let ast_module = parser.parse().expect("parse ok");

        let hir_module = hir::lower(&ast_module).expect("hir lower");

        // Debug: print HIR
        eprintln!("HIR module: {} functions", hir_module.functions.len());
        for func in &hir_module.functions {
            eprintln!("  HIR func: {} (public={})", func.name, func.is_public());
        }

        let mir_module = mir::lower_to_mir(&hir_module).expect("mir lower");

        // Debug: print MIR functions
        eprintln!("MIR functions ({}):", mir_module.functions.len());
        for func in &mir_module.functions {
            eprintln!(
                "  {} (public={}, entry={:?}, blocks={}, params={}, ret={:?})",
                func.name,
                func.is_public(),
                func.entry_block,
                func.blocks.len(),
                func.params.len(),
                func.return_type
            );
            for block in &func.blocks {
                eprintln!(
                    "    Block {:?}: {} instructions",
                    block.id,
                    block.instructions.len()
                );
                for inst in &block.instructions {
                    eprintln!("      {:?}", inst);
                }
                eprintln!("      Terminator: {:?}", block.terminator);
            }
        }

        let codegen = crate::codegen::Codegen::new().expect("codegen new");
        let object_code = codegen.compile_module(&mir_module).expect("compile ok");

        // Check if it's ELF
        assert!(
            object_code.len() > 4 && &object_code[0..4] == b"\x7fELF",
            "Expected ELF format, got first 4 bytes: {:?}",
            &object_code[0..4.min(object_code.len())]
        );

        // List all sections for debugging
        let sections = list_elf_sections(&object_code);
        eprintln!("ELF sections:");
        for s in &sections {
            eprintln!("  {}", s);
        }

        // Try to extract .text section
        let text_section = extract_elf_text_section(&object_code);
        assert!(
            text_section.is_some(),
            "Failed to extract .text section from ELF. Sections: {:?}",
            sections
        );

        let text = text_section.unwrap();
        assert!(!text.is_empty(), "Extracted .text section is empty");
        eprintln!("Extracted .text section size: {} bytes", text.len());
        eprintln!("First 16 bytes: {:02x?}", &text[0..16.min(text.len())]);
    }

    #[cfg(not(feature = "llvm"))]
    #[test]
    fn test_pipeline_32bit_target_requires_llvm() {
        let source = "fn main() -> i64:\n    return 42";
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let target = Target::new(TargetArch::X86, TargetOS::Linux);
        let result = pipeline.compile_source_to_memory_for_target(source, target);

        assert!(result.is_err());
        match result {
            Err(CompileError::Codegen(msg)) => {
                assert!(msg.contains("LLVM backend"));
            }
            other => panic!("Expected codegen error, got {other:?}"),
        }
    }

    #[cfg(feature = "llvm")]
    #[test]
    fn test_pipeline_32bit_target_with_llvm() {
        let source = "fn main() -> i64:\n    return 42";
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let target = Target::new(TargetArch::X86, TargetOS::Linux);
        let result = pipeline.compile_source_to_memory_for_target(source, target);

        assert!(result.is_ok());
    }

    // ============== Lint Integration Tests ==============

    /// Test helper for running source with a specific lint configuration
    fn run_with_lint_config(source: &str, config: LintConfig) -> Result<Vec<u8>, CompileError> {
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        pipeline.set_lint_config(config);
        pipeline.compile_source_to_memory(source)
    }

    #[test]
    fn test_pipeline_lint_warnings_collected() {
        // Public function with primitive param should generate warning
        let source = r#"
pub fn get_value(x: i64) -> i64:
    return x

main = 0
"#;
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let _ = pipeline.compile_source_to_memory(source);

        // Should have lint warnings (default level is Warn)
        assert!(pipeline.has_lint_warnings());
        assert!(!pipeline.has_lint_errors());

        let diagnostics = pipeline.lint_diagnostics();
        assert!(!diagnostics.is_empty());
        // Should warn about primitive_api for both param and return type
        assert!(diagnostics.iter().any(|d| d.message.contains("i64")));
    }

    #[test]
    fn test_pipeline_lint_deny_fails_compilation() {
        // Public function with primitive param + deny level should fail
        let source = r#"
pub fn get_value(x: i64) -> i64:
    return x

main = 0
"#;
        let mut config = LintConfig::new();
        config.set_level(
            crate::lint::LintName::PrimitiveApi,
            crate::lint::LintLevel::Deny,
        );

        let result = run_with_lint_config(source, config);
        assert!(result.is_err());

        match result {
            Err(CompileError::Lint(msg)) => {
                assert!(msg.contains("primitive"));
            }
            _ => panic!("Expected Lint error"),
        }
    }

    #[test]
    fn test_pipeline_lint_allow_suppresses() {
        // With allow level, no warnings/errors should be generated
        let source = r#"
pub fn get_value(x: i64) -> i64:
    return x

main = 0
"#;
        let mut config = LintConfig::new();
        config.set_level(
            crate::lint::LintName::PrimitiveApi,
            crate::lint::LintLevel::Allow,
        );

        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        pipeline.set_lint_config(config);
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_ok());

        // No warnings or errors
        assert!(!pipeline.has_lint_warnings());
        assert!(!pipeline.has_lint_errors());
    }

    #[test]
    fn test_pipeline_private_function_no_lint() {
        // Private functions don't trigger primitive_api lint
        let source = r#"
fn internal_compute(x: i64) -> i64:
    return x

main = 0
"#;
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_ok());

        // No warnings for private functions
        assert!(!pipeline.has_lint_warnings());
    }

    #[test]
    fn test_pipeline_diagnostics_cleared_on_recompile() {
        let source_with_warning = r#"
pub fn get_value(x: i64) -> i64:
    return x

main = 0
"#;
        let source_clean = r#"
main = 42
"#;

        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");

        // First compile - should have warnings
        let _ = pipeline.compile_source_to_memory(source_with_warning);
        assert!(pipeline.has_lint_warnings());

        // Second compile - should clear previous diagnostics
        let _ = pipeline.compile_source_to_memory(source_clean);
        assert!(!pipeline.has_lint_warnings());
    }

    #[test]
    fn test_pipeline_native_lint_integration() {
        // Native compilation should also run lint checks
        let source = r#"
pub fn compute(x: i64) -> i64:
    return x * 2

main = 0
"#;
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let _ = pipeline.compile_source_to_memory_native(source);

        // Should have lint warnings
        assert!(pipeline.has_lint_warnings());
    }

    #[test]
    fn script_detection_handles_top_level_match() {
        let mut parser = simple_parser::Parser::new(
            "let x: i32 = 2\nmatch x:\n    2 =>\n        main = 20\n    _ =>\n        main = 0",
        );
        let module = parser.parse().expect("parse ok");
        assert!(
            has_script_statements(&module.items),
            "script statements should be detected for match + let"
        );
    }

    #[test]
    fn interpreter_pipeline_executes_top_level_match() {
        let source =
            "let x: i32 = 2\nmatch x:\n    2 =>\n        main = 20\n    _ =>\n        main = 0";
        let mut parser = simple_parser::Parser::new(source);
        let ast = parser.parse().expect("parse ok");
        let module = monomorphize_module(&ast);
        let item_kinds: Vec<&str> = module
            .items
            .iter()
            .map(|n| match n {
                simple_parser::ast::Node::Let(_) => "Let",
                simple_parser::ast::Node::Match(_) => "Match",
                simple_parser::ast::Node::Function(_) => "Function",
                _ => "Other",
            })
            .collect();
        assert_eq!(item_kinds, vec!["Let", "Match"]);

        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");
        let result = pipeline.compile_source_to_memory(source);
        assert!(
            result.is_ok(),
            "script match should fall back to interpreter, got {result:?}"
        );
    }

    // ============== Contract Mode Integration Tests ==============

    #[test]
    fn test_pipeline_contract_mode_default() {
        let pipeline = CompilerPipeline::new().expect("pipeline ok");
        assert_eq!(pipeline.contract_mode(), ContractMode::All);
    }

    #[test]
    fn test_pipeline_contract_mode_set() {
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");

        pipeline.set_contract_mode(ContractMode::Off);
        assert_eq!(pipeline.contract_mode(), ContractMode::Off);

        pipeline.set_contract_mode(ContractMode::Boundary);
        assert_eq!(pipeline.contract_mode(), ContractMode::Boundary);

        pipeline.set_contract_mode(ContractMode::All);
        assert_eq!(pipeline.contract_mode(), ContractMode::All);
    }

    #[test]
    fn test_pipeline_coherence_detects_errors_in_ast() {
        // Verify that coherence checker catches errors when manually constructed AST is invalid
        use simple_parser::ast::*;
        
        let impl_block = ImplBlock {
            span: simple_parser::token::Span::new(0, 0, 0, 0),
            attributes: vec![],
            generic_params: vec![],
            where_clause: vec![],
            target_type: Type::Simple("String".to_string()),
            trait_name: Some("Display".to_string()),
            associated_types: vec![],
            methods: vec![],
        };
        
        let nodes = vec![Node::Impl(impl_block)];
        
        let checker = crate::trait_coherence::CoherenceChecker::new();
        let mut checker_mut = checker;
        let errors = checker_mut.check_module(&nodes);
        
        // Should detect orphan rule violation
        assert!(!errors.is_empty(), "Should detect orphan rule violation");
        assert!(matches!(errors[0], crate::trait_coherence::CoherenceError::OrphanImpl { .. }));
    }

    // ============== Build Mode and Release Validation Tests (#1034-1035) ==============

    #[test]
    fn test_build_mode_default() {
        let pipeline = CompilerPipeline::new().expect("pipeline ok");
        assert_eq!(pipeline.build_mode(), BuildMode::Debug);
    }

    #[test]
    fn test_build_mode_set() {
        let mut pipeline = CompilerPipeline::new().expect("pipeline ok");

        pipeline.set_build_mode(BuildMode::Debug);
        assert_eq!(pipeline.build_mode(), BuildMode::Debug);

        pipeline.set_build_mode(BuildMode::Release);
        assert_eq!(pipeline.build_mode(), BuildMode::Release);
    }

    #[test]
    fn test_debug_mode_allows_test_profile() {
        // Debug mode should allow test DI profile
        let source = "main = 42";

        // Create a project context with test DI profile
        use std::path::PathBuf;
        use crate::di::{DiConfig, DiProfile, DiMode};
        use std::collections::HashMap;

        let mut profiles = HashMap::new();
        let mut test_profile = DiProfile::default();
        // Add a test binding to simulate active test profile
        test_profile.bindings.push(crate::di::DiBindingRule {
            predicate: crate::predicate::Predicate::Selector(
                crate::predicate::Selector::Within("*".to_string())
            ),
            impl_type: "TestLogger".to_string(),
            scope: crate::di::DiScope::Singleton,
            priority: 0,
            order: 0,
            raw_predicate: "*".to_string(),
        });
        profiles.insert("test".to_string(), test_profile);

        let di_config = DiConfig {
            mode: DiMode::Hybrid,
            profiles,
        };

        let mut project = ProjectContext::single_file(Path::new("."));
        project.di_config = Some(di_config);

        let mut pipeline = CompilerPipeline::with_project(project).expect("pipeline ok");
        pipeline.set_build_mode(BuildMode::Debug);

        // Should succeed in debug mode
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_ok(), "Debug mode should allow test profile");
    }

    #[test]
    fn test_release_mode_rejects_test_profile() {
        // Release mode should reject test DI profile (#1034)
        let source = "main = 42";

        // Create a project context with test DI profile
        use std::path::PathBuf;
        use crate::di::{DiConfig, DiProfile, DiMode};
        use std::collections::HashMap;

        let mut profiles = HashMap::new();
        let mut test_profile = DiProfile::default();
        // Add a test binding to simulate active test profile
        test_profile.bindings.push(crate::di::DiBindingRule {
            predicate: crate::predicate::Predicate::Selector(
                crate::predicate::Selector::Within("*".to_string())
            ),
            impl_type: "TestLogger".to_string(),
            scope: crate::di::DiScope::Singleton,
            priority: 0,
            order: 0,
            raw_predicate: "*".to_string(),
        });
        profiles.insert("test".to_string(), test_profile);

        let di_config = DiConfig {
            mode: DiMode::Hybrid,
            profiles,
        };

        let mut project = ProjectContext::single_file(Path::new("."));
        project.di_config = Some(di_config);

        let mut pipeline = CompilerPipeline::with_project(project).expect("pipeline ok");
        pipeline.set_build_mode(BuildMode::Release);

        // Should fail in release mode
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_err(), "Release mode should reject test profile");

        match result {
            Err(CompileError::Semantic(msg)) => {
                assert!(msg.contains("#1034"), "Error should reference #1034");
                assert!(msg.contains("test"), "Error should mention test profile");
            }
            _ => panic!("Expected semantic error with #1034 reference"),
        }
    }

    #[test]
    fn test_debug_mode_allows_runtime_aop() {
        // Debug mode should allow runtime AOP interceptors
        let source = "main = 42";

        // Create a project context with runtime AOP enabled
        use std::path::PathBuf;
        use crate::aop_config::AopConfig;

        let aop_config = AopConfig {
            runtime_enabled: true,
            around: vec![],
        };

        let mut project = ProjectContext::single_file(Path::new("."));
        project.aop_config = Some(aop_config);

        let mut pipeline = CompilerPipeline::with_project(project).expect("pipeline ok");
        pipeline.set_build_mode(BuildMode::Debug);

        // Should succeed in debug mode
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_ok(), "Debug mode should allow runtime AOP");
    }

    #[test]
    fn test_release_mode_rejects_runtime_aop() {
        // Release mode should reject runtime AOP interceptors (#1035)
        let source = "main = 42";

        // Create a project context with runtime AOP enabled
        use std::path::PathBuf;
        use crate::aop_config::AopConfig;

        let aop_config = AopConfig {
            runtime_enabled: true,
            around: vec![],
        };

        let mut project = ProjectContext::single_file(Path::new("."));
        project.aop_config = Some(aop_config);

        let mut pipeline = CompilerPipeline::with_project(project).expect("pipeline ok");
        pipeline.set_build_mode(BuildMode::Release);

        // Should fail in release mode
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_err(), "Release mode should reject runtime AOP");

        match result {
            Err(CompileError::Semantic(msg)) => {
                assert!(msg.contains("#1035"), "Error should reference #1035");
                assert!(msg.contains("runtime"), "Error should mention runtime interceptors");
            }
            _ => panic!("Expected semantic error with #1035 reference"),
        }
    }

    #[test]
    fn test_release_mode_allows_disabled_runtime_aop() {
        // Release mode should allow runtime_enabled=false
        let source = "main = 42";

        // Create a project context with runtime AOP disabled
        use std::path::PathBuf;
        use crate::aop_config::AopConfig;

        let aop_config = AopConfig {
            runtime_enabled: false,
            around: vec![],
        };

        let mut project = ProjectContext::single_file(Path::new("."));
        project.aop_config = Some(aop_config);

        let mut pipeline = CompilerPipeline::with_project(project).expect("pipeline ok");
        pipeline.set_build_mode(BuildMode::Release);

        // Should succeed when runtime AOP is disabled
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_ok(), "Release mode should allow disabled runtime AOP");
    }

    #[test]
    fn test_release_mode_allows_empty_test_profile() {
        // Release mode should allow empty test profile (no active bindings)
        let source = "main = 42";

        // Create a project context with empty test DI profile
        use std::path::PathBuf;
        use crate::di::{DiConfig, DiProfile, DiMode};
        use std::collections::HashMap;

        let mut profiles = HashMap::new();
        profiles.insert("test".to_string(), DiProfile::default()); // Empty profile

        let di_config = DiConfig {
            mode: DiMode::Hybrid,
            profiles,
        };

        let mut project = ProjectContext::single_file(Path::new("."));
        project.di_config = Some(di_config);

        let mut pipeline = CompilerPipeline::with_project(project).expect("pipeline ok");
        pipeline.set_build_mode(BuildMode::Release);

        // Should succeed when test profile has no bindings
        let result = pipeline.compile_source_to_memory(source);
        assert!(result.is_ok(), "Release mode should allow empty test profile");
    }
}

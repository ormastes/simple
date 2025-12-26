//! Core CompilerPipeline struct and configuration management.

use std::path::PathBuf;
use std::sync::Arc;

use simple_common::gc::GcAllocator;

use crate::build_mode::BuildMode;
use crate::lint::{LintConfig, LintDiagnostic};
use crate::mir::ContractMode;
use crate::project::ProjectContext;
use crate::CompileError;

/// Minimal compiler pipeline that validates syntax then emits a runnable SMF.
pub struct CompilerPipeline {
    pub(super) gc: Option<Arc<dyn GcAllocator>>,
    /// Optional project context for multi-file compilation
    pub(super) project: Option<ProjectContext>,
    /// Lint configuration (can be set independently of project)
    pub(super) lint_config: Option<LintConfig>,
    /// Lint diagnostics from the last compilation
    pub(super) lint_diagnostics: Vec<LintDiagnostic>,
    /// Contract checking mode (CTR-040 to CTR-043)
    pub(super) contract_mode: ContractMode,
    /// Build mode (debug/release) for validation and optimization (#1034-1035)
    pub(super) build_mode: BuildMode,
    /// Emit AST as JSON to file or stdout (LLM-friendly #885)
    pub(super) emit_ast: Option<Option<PathBuf>>,
    /// Emit HIR as JSON to file or stdout (LLM-friendly #886)
    pub(super) emit_hir: Option<Option<PathBuf>>,
    /// Emit MIR as JSON to file or stdout (LLM-friendly #887)
    pub(super) emit_mir: Option<Option<PathBuf>>,
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
            emit_ast: None,
            emit_hir: None,
            emit_mir: None,
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
            emit_ast: None,
            emit_hir: None,
            emit_mir: None,
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
            emit_ast: None,
            emit_hir: None,
            emit_mir: None,
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
            emit_ast: None,
            emit_hir: None,
            emit_mir: None,
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

    /// Set emit AST option (LLM-friendly #885)
    pub fn set_emit_ast(&mut self, path: Option<PathBuf>) {
        self.emit_ast = Some(path);
    }

    /// Set emit HIR option (LLM-friendly #886)
    pub fn set_emit_hir(&mut self, path: Option<PathBuf>) {
        self.emit_hir = Some(path);
    }

    /// Set emit MIR option (LLM-friendly #887)
    pub fn set_emit_mir(&mut self, path: Option<PathBuf>) {
        self.emit_mir = Some(path);
    }

    /// Validate AOP/DI configuration for release builds (#1034-1035).
    ///
    /// In release mode:
    /// - #1034: DI profile must not be "test"
    /// - #1035: AOP runtime interceptors must not be enabled
    pub(super) fn validate_release_config(&self) -> Result<(), CompileError> {
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
}

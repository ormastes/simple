//! Source parsing, module resolution, and import handling.

use std::path::Path;

use simple_parser::ast::{Capability, Node};
use tracing::instrument;

use super::core::CompilerPipeline;
use crate::lint::LintChecker;
use crate::trait_coherence::CoherenceChecker;
use crate::CompileError;

impl CompilerPipeline {
    /// Run lint checks on AST items.
    ///
    /// Stores diagnostics in `self.lint_diagnostics`.
    /// Returns an error if any lint is set to deny level.
    pub(super) fn run_lint_checks(&mut self, items: &[Node], source_file: Option<&Path>) -> Result<(), CompileError> {
        let mut checker = if let Some(ref config) = self.lint_config {
            LintChecker::with_config(config.clone())
        } else {
            LintChecker::new()
        };

        // Set source file for file-based lints
        checker = checker.with_source_file(source_file.map(|p| p.to_path_buf()));

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
    pub(super) fn check_trait_coherence(&self, items: &[Node]) -> Result<(), CompileError> {
        let mut checker = CoherenceChecker::new();
        let errors = checker.check_module(items);

        if !errors.is_empty() {
            let error_messages: Vec<String> = errors.iter().map(|e| format!("{:?}", e)).collect();
            return Err(CompileError::Semantic(format!(
                "Trait coherence errors:\n{}",
                error_messages.join("\n")
            )));
        }

        Ok(())
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
    pub(super) fn validate_capabilities(&self, items: &[Node]) -> Result<(), CompileError> {
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
                            "function '{}' has @{} effect but module only allows capabilities: [{}]\n\
                             help: add '{}' to module's 'requires [...]' statement or remove @{} from function",
                            func.name,
                            effect.decorator_name(),
                            capabilities.iter().map(|c| c.name()).collect::<Vec<_>>().join(", "),
                            cap.name(),
                            effect.decorator_name()
                        )));
                    }
                }
            }
        }

        Ok(())
    }

    /// Validate that sync-annotated functions don't contain suspension operators.
    ///
    /// This implements the async-by-default semantics check (#44):
    /// - Functions marked with `sync fn` cannot contain await, ~=, if~, while~, for~ operators
    /// - This ensures sync functions are truly non-suspending
    pub(super) fn validate_sync_constraints(&self, items: &[Node]) -> Result<(), CompileError> {
        for item in items {
            if let Node::Function(func) = item {
                // Use the type checker's validation function
                if let Err(err_msg) = simple_type::validate_sync_constraint(func) {
                    return Err(CompileError::Semantic(err_msg));
                }
            }
        }
        Ok(())
    }
}

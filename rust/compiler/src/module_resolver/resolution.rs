//! Module path resolution logic.
//!
//! This module handles resolving module paths to filesystem locations,
//! including support for both absolute (crate.*) and relative paths.

use super::types::{DirectoryManifest, ModuleResolver, ResolveResult, ResolvedModule};
use simple_dependency_tracker::{
    graph::ImportKind,
    macro_import::{MacroExports, MacroSymbol},
    resolution::ModPath,
    visibility::Visibility as TrackerVisibility,
};
use simple_parser::ast::{CommonUseStmt, ImportTarget, ModulePath, Visibility};
use std::path::Path;

use crate::error::{codes, CompileError, ErrorContext};

impl ModuleResolver {
    /// Resolve a module path to a filesystem path
    ///
    /// # Arguments
    /// * `path` - The module path to resolve (e.g., crate.sys.http.router)
    /// * `from_file` - The file making the import (for relative resolution)
    ///
    /// # Returns
    /// The resolved module information including filesystem path
    pub fn resolve(&self, path: &ModulePath, from_file: &Path) -> ResolveResult<ResolvedModule> {
        let segments = &path.segments;
        if segments.is_empty() {
            let ctx = ErrorContext::new()
                .with_code(codes::MODULE_NOT_FOUND)
                .with_help("provide at least one module path segment");
            return Err(CompileError::semantic_with_context(
                "empty module path".to_string(),
                ctx,
            ));
        }

        // Determine base directory
        let (base_dir, remaining) = if segments[0] == "crate" {
            // Absolute path from project root
            (self.source_root.clone(), &segments[1..])
        } else {
            // Relative path from current file's directory
            let parent = from_file.parent().unwrap_or(Path::new("."));
            (parent.to_path_buf(), &segments[..])
        };

        // Try resolving from the base directory first
        match self.resolve_from_base(&base_dir, remaining, path) {
            Ok(resolved) => Ok(resolved),
            Err(err) => {
                // If relative resolution failed and stdlib is available, try stdlib
                if segments[0] != "crate" {
                    if let Some(ref stdlib_root) = self.stdlib_root {
                        // If path starts with "std_lib", strip that prefix since stdlib_root
                        // already points to the std_lib directory
                        let stdlib_segments = if !segments.is_empty() && segments[0] == "std_lib" {
                            &segments[1..]
                        } else {
                            segments
                        };

                        if !stdlib_segments.is_empty() {
                            match self.resolve_from_base(stdlib_root, stdlib_segments, path) {
                                Ok(resolved) => return Ok(resolved),
                                Err(_) => {
                                    // Stdlib resolution also failed, return original error
                                    return Err(err);
                                }
                            }
                        }
                    }
                }
                Err(err)
            }
        }
    }

    /// Resolve from a base directory with remaining path segments
    pub(super) fn resolve_from_base(
        &self,
        base: &Path,
        segments: &[String],
        original_path: &ModulePath,
    ) -> ResolveResult<ResolvedModule> {
        if segments.is_empty() {
            let ctx = ErrorContext::new()
                .with_code(codes::MODULE_NOT_FOUND)
                .with_help("module path must contain at least one segment");
            return Err(CompileError::semantic_with_context(
                "empty module path segments".to_string(),
                ctx,
            ));
        }

        let mut current = base.to_path_buf();

        // Navigate through all but the last segment
        for segment in &segments[..segments.len() - 1] {
            current = current.join(segment);

            // Check for __init__.spl in each directory
            let init_path = current.join("__init__.spl");
            if init_path.exists() && init_path.is_file() {
                // Directory module - continue navigation
            } else if !current.exists() {
                // E1034 - Unresolved Import
                let ctx = ErrorContext::new()
                    .with_code(codes::UNRESOLVED_IMPORT)
                    .with_help(format!("check that the module exists at {:?}", current))
                    .with_note("ensure the module file or __init__.spl exists");

                return Err(CompileError::semantic_with_context(
                    format!("cannot resolve import: module path segment `{}` not found", segment),
                    ctx,
                ));
            }
        }

        // Resolve the last segment
        let last = &segments[segments.len() - 1];

        // Try directory with __init__.spl first
        let dir_path = current.join(last);
        let init_path = dir_path.join("__init__.spl");
        if init_path.exists() && init_path.is_file() {
            return Ok(ResolvedModule {
                path: init_path,
                module_path: original_path.clone(),
                is_directory: true,
                manifest: None, // Will be loaded on demand
            });
        }

        // Try .spl file
        let file_path = current.join(format!("{}.spl", last));
        if file_path.exists() && file_path.is_file() {
            return Ok(ResolvedModule {
                path: file_path,
                module_path: original_path.clone(),
                is_directory: false,
                manifest: None,
            });
        }

        // Try .ssh file (Simple shell scripts)
        let ssh_path = current.join(format!("{}.ssh", last));
        if ssh_path.exists() && ssh_path.is_file() {
            return Ok(ResolvedModule {
                path: ssh_path,
                module_path: original_path.clone(),
                is_directory: false,
                manifest: None,
            });
        }

        // E1034 - Unresolved Import
        let ctx = ErrorContext::new()
            .with_code(codes::UNRESOLVED_IMPORT)
            .with_help(format!("create either {:?} or {:?}", file_path, init_path))
            .with_note("check for typos in the import path");

        Err(CompileError::semantic_with_context(
            format!("cannot resolve import: module `{}` not found", last),
            ctx,
        ))
    }

    /// Get all symbols exported by a module
    pub fn get_exports(&self, resolved: &ResolvedModule) -> ResolveResult<Vec<String>> {
        if let Some(manifest) = &resolved.manifest {
            let mut exports = Vec::new();

            // Add re-exported symbols
            for export in &manifest.exports {
                match &export.target {
                    ImportTarget::Single(name) => exports.push(name.clone()),
                    ImportTarget::Aliased { alias, .. } => exports.push(alias.clone()),
                    ImportTarget::Group(targets) => {
                        for target in targets {
                            match target {
                                ImportTarget::Single(name) => exports.push(name.clone()),
                                ImportTarget::Aliased { alias, .. } => exports.push(alias.clone()),
                                _ => {}
                            }
                        }
                    }
                    ImportTarget::Glob => {
                        // Glob exports - would need to resolve the target module
                        // For now, this is a placeholder
                    }
                }
            }

            // Add public child modules
            for child in &manifest.child_modules {
                if child.visibility == Visibility::Public {
                    exports.push(child.name.clone());
                }
            }

            Ok(exports)
        } else {
            // Non-directory module - would need to parse and extract pub items
            Ok(Vec::new())
        }
    }

    /// Get common use imports that apply to a file
    pub fn get_common_uses(&self, file_path: &Path) -> Vec<CommonUseStmt> {
        let mut uses = Vec::new();

        // Walk up the directory tree collecting common uses
        let mut current = file_path.parent();
        while let Some(dir) = current {
            if let Some(manifest) = self.manifests.get(&dir.join("__init__.spl")) {
                uses.extend(manifest.common_uses.iter().cloned());
            }
            if dir == self.source_root {
                break;
            }
            current = dir.parent();
        }

        uses
    }

    /// Get auto-import macros that apply to glob imports from a module
    pub fn get_auto_imports(&self, _module_path: &ModulePath) -> Vec<String> {
        // Would resolve the module and check its manifest
        // For now, return empty
        Vec::new()
    }

    /// Record an import in the import graph.
    pub fn record_import(&mut self, from_module: &str, to_module: &str, kind: ImportKind) {
        self.import_graph.add_import(from_module, to_module, kind);
    }

    /// Record an import from HIR representation.
    /// Automatically determines the ImportKind based on whether the import is type-only.
    pub fn record_import_from_hir(&mut self, from_module: &str, import: &crate::hir::HirImport) {
        let to_module = import.from_path.join(".");
        let kind = if import.is_type_only {
            ImportKind::TypeUse
        } else {
            ImportKind::Use
        };
        self.import_graph.add_import(from_module, &to_module, kind);
    }

    /// Check for circular dependencies in the import graph.
    pub fn check_circular_dependencies(&self) -> ResolveResult<()> {
        self.import_graph
            .check_cycles()
            .map_err(|e| crate::error::factory::circular_dependency(&e.to_string()))
    }

    /// Convert a parser ModulePath to a tracker ModPath.
    pub fn to_tracker_mod_path(path: &ModulePath) -> Option<ModPath> {
        ModPath::parse(&path.segments.join("."))
    }

    /// Filter glob imports to only include auto-imported macros.
    ///
    /// This implements the formal model's `globImport` function.
    pub fn filter_glob_import(&self, dir_manifest: &DirectoryManifest, exports: &MacroExports) -> Vec<MacroSymbol> {
        use simple_dependency_tracker as tracker;
        let macro_manifest = dir_manifest.to_tracker_macro_manifest();
        tracker::macro_import::glob_import(&macro_manifest, exports)
    }

    /// Calculate effective visibility using the formal model.
    ///
    /// This implements the formal model's `effectiveVisibility` function.
    pub fn effective_visibility(
        &self,
        manifest: &DirectoryManifest,
        module_name: &str,
        symbol_name: &str,
        symbol_visibility: Visibility,
    ) -> TrackerVisibility {
        use simple_dependency_tracker as tracker;
        let tracker_manifest = manifest.to_tracker_visibility_manifest();
        let sym_id = tracker::visibility::SymbolId::new(symbol_name);

        // Create a minimal module contents with just this symbol
        let mut mc = tracker::visibility::ModuleContents::new();
        mc.add_symbol(tracker::visibility::Symbol::new(
            symbol_name,
            if symbol_visibility == Visibility::Public {
                TrackerVisibility::Public
            } else {
                TrackerVisibility::Private
            },
        ));

        tracker::visibility::effective_visibility(&tracker_manifest, module_name, &mc, &sym_id)
    }

    /// Calculate ancestor visibility using the formal model.
    ///
    /// This implements the formal model's `ancestorVisibility` function.
    pub fn ancestor_visibility(&self, path: &[TrackerVisibility]) -> TrackerVisibility {
        use simple_dependency_tracker as tracker;
        tracker::visibility::ancestor_visibility(path)
    }
}

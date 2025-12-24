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

use crate::error::CompileError;

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
            return Err(CompileError::Semantic("empty module path".into()));
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

        self.resolve_from_base(&base_dir, remaining, path)
    }

    /// Resolve from a base directory with remaining path segments
    pub(super) fn resolve_from_base(
        &self,
        base: &Path,
        segments: &[String],
        original_path: &ModulePath,
    ) -> ResolveResult<ResolvedModule> {
        if segments.is_empty() {
            return Err(CompileError::Semantic("empty module path segments".into()));
        }

        let mut current = base.to_path_buf();

        // Navigate through all but the last segment
        for segment in &segments[..segments.len() - 1] {
            current = current.join(segment);

            // Check for __init__.spl in each directory
            let init_path = current.join("__init__.spl");
            if init_path.exists() {
                // Directory module - continue navigation
            } else if !current.exists() {
                return Err(CompileError::Semantic(format!(
                    "module path segment '{}' not found at {:?}",
                    segment, current
                )));
            }
        }

        // Resolve the last segment
        let last = &segments[segments.len() - 1];

        // Try directory with __init__.spl first
        let dir_path = current.join(last);
        let init_path = dir_path.join("__init__.spl");
        if init_path.exists() {
            return Ok(ResolvedModule {
                path: init_path,
                module_path: original_path.clone(),
                is_directory: true,
                manifest: None, // Will be loaded on demand
            });
        }

        // Try .spl file
        let file_path = current.join(format!("{}.spl", last));
        if file_path.exists() {
            return Ok(ResolvedModule {
                path: file_path,
                module_path: original_path.clone(),
                is_directory: false,
                manifest: None,
            });
        }

        Err(CompileError::Semantic(format!(
            "module '{}' not found (tried {:?} and {:?})",
            last, file_path, init_path
        )))
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

    /// Check for circular dependencies in the import graph.
    pub fn check_circular_dependencies(&self) -> ResolveResult<()> {
        self.import_graph
            .check_cycles()
            .map_err(|e| CompileError::Semantic(format!("Circular dependency detected: {}", e)))
    }

    /// Convert a parser ModulePath to a tracker ModPath.
    pub fn to_tracker_mod_path(path: &ModulePath) -> Option<ModPath> {
        ModPath::parse(&path.segments.join("."))
    }

    /// Filter glob imports to only include auto-imported macros.
    ///
    /// This implements the formal model's `globImport` function.
    pub fn filter_glob_import(
        &self,
        dir_manifest: &DirectoryManifest,
        exports: &MacroExports,
    ) -> Vec<MacroSymbol> {
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

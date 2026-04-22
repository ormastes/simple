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
use std::path::{Path, PathBuf};

use crate::error::{codes, CompileError, ErrorContext};

/// Find a numbered directory matching the pattern `NN.name` or `NNN.name`.
///
/// The Simple compiler organizes source into numbered layers like:
///   src/compiler/00.common/
///   src/compiler/10.frontend/
///   src/compiler/70.backend/
///
/// When resolving `compiler.frontend`, this function finds `10.frontend` for segment `frontend`.
fn find_numbered_dir(parent: &Path, segment: &str) -> Option<PathBuf> {
    let entries = std::fs::read_dir(parent).ok()?;
    for entry in entries.flatten() {
        let name = entry.file_name();
        let name_str = name.to_string_lossy();
        // Match pattern: 1-3 digits, dot, then the segment name
        if let Some(after_dot) = name_str.find('.') {
            let prefix = &name_str[..after_dot];
            let suffix = &name_str[after_dot + 1..];
            if suffix == segment && prefix.len() <= 3 && prefix.chars().all(|c| c.is_ascii_digit()) {
                let path = parent.join(&*name_str);
                if path.is_dir() {
                    return Some(path);
                }
            }
        }
    }
    None
}

fn find_dotted_dir(current: &Path, segment: &str) -> Option<PathBuf> {
    let parent = current.parent()?;
    let current_name = current.file_name()?.to_str()?;
    let dotted_dir = parent.join(format!("{}.{}", current_name, segment));
    if dotted_dir.is_dir() {
        Some(dotted_dir)
    } else {
        None
    }
}

fn domain_to_dir(domain: &str) -> String {
    domain.replace('-', "_")
}

fn normalize_type_segments(resolver: &ModuleResolver, segments: &[String]) -> Option<Vec<String>> {
    if segments.is_empty() || segments[0] == "crate" {
        return None;
    }

    if segments.len() >= 2 && segments[0].contains('-') {
        let mut normalized = vec!["type".to_string(), domain_to_dir(&segments[0])];
        normalized.extend(segments[1..].iter().cloned());
        return Some(normalized);
    }

    if segments.len() == 1 {
        return Some(vec![
            "type".to_string(),
            domain_to_dir(&resolver.default_type_domain),
            segments[0].clone(),
        ]);
    }

    None
}

fn resolve_stdlib_from_root(
    resolver: &ModuleResolver,
    root: &Path,
    segments: &[String],
    original_path: &ModulePath,
) -> ResolveResult<ResolvedModule> {
    if let Ok(resolved) = resolver.resolve_from_base(root, segments, original_path) {
        return Ok(resolved);
    }

    for subdir in &[
        "nogc_async_mut",
        "nogc_sync_mut",
        "nogc_async_immut",
        "common",
        "gc_async_mut",
        "nogc_async_mut_noalloc",
    ] {
        let candidate = root.join(subdir);
        if candidate.is_dir() {
            if let Ok(resolved) = resolver.resolve_from_base(&candidate, segments, original_path) {
                return Ok(resolved);
            }
        }
    }

    Err(CompileError::semantic("stdlib module not found".to_string()))
}

fn ordered_source_roots(resolver: &ModuleResolver) -> Vec<PathBuf> {
    let mut roots = Vec::new();
    roots.push(resolver.source_root.clone());
    for root in &resolver.extra_source_roots {
        if !roots.iter().any(|existing| existing == root) {
            roots.push(root.clone());
        }
    }
    roots
}

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
                if let Some(type_segments) = normalize_type_segments(self, segments) {
                    if let Ok(resolved) = self.resolve_from_base(&self.type_root, &type_segments[1..], path) {
                        return Ok(resolved);
                    }
                }

                // If relative resolution failed, try alternative resolution strategies

                // Strategy 1: Try stdlib
                if segments[0] != "crate" {
                    let stdlib_segments = if !segments.is_empty() && segments[0] == "std_lib" {
                        &segments[1..]
                    } else if !segments.is_empty() && (segments[0] == "std" || segments[0] == "lib") {
                        &segments[1..]
                    } else {
                        segments
                    };

                    if !stdlib_segments.is_empty() {
                        let mut stdlib_roots =
                            vec![self.project_root.join("src/lib"), self.project_root.join("src/std")];
                        if let Some(ref stdlib_root) = self.stdlib_root {
                            stdlib_roots.push(stdlib_root.clone());
                        }

                        for root in stdlib_roots {
                            if root.is_dir() {
                                if stdlib_segments.len() == 1 && stdlib_segments[0] == "io" {
                                    let compat_root = root.join("nogc_sync_mut");
                                    if compat_root.is_dir() {
                                        if let Ok(resolved) =
                                            self.resolve_from_base(&compat_root, stdlib_segments, path)
                                        {
                                            return Ok(resolved);
                                        }
                                    }
                                }
                                if let Ok(resolved) = resolve_stdlib_from_root(self, &root, stdlib_segments, path) {
                                    return Ok(resolved);
                                }
                            }
                        }
                    }
                }

                // Strategy 2: Try "compiler.*" → source_root/compiler/ with numbered prefix support
                if segments[0] == "compiler" && segments.len() > 1 {
                    for root in ordered_source_roots(self) {
                        let compiler_dir = root.join("compiler");
                        if compiler_dir.is_dir() {
                            if let Ok(resolved) = self.resolve_from_base(&compiler_dir, &segments[1..], path) {
                                return Ok(resolved);
                            }
                        }
                    }
                    // Also try project_root/src/compiler/
                    let alt_compiler_dir = self.project_root.join("src").join("compiler");
                    if alt_compiler_dir.is_dir() {
                        if let Ok(resolved) = self.resolve_from_base(&alt_compiler_dir, &segments[1..], path) {
                            return Ok(resolved);
                        }
                    }
                }

                // Strategy 3: Try numbered directory at source root level
                if segments[0] != "crate" && !segments.is_empty() {
                    for root in ordered_source_roots(self) {
                        if let Some(numbered) = find_numbered_dir(&root, &segments[0]) {
                            if segments.len() > 1 {
                                if let Ok(resolved) = self.resolve_from_base(&numbered, &segments[1..], path) {
                                    return Ok(resolved);
                                }
                            }
                        }
                    }
                }

                // Strategy 4: Try source_root as base for top-level module names
                // e.g., "use app.ffi_gen.parser" → source_root/app/ffi_gen/parser.spl
                // This handles cross-project imports declared in simple.sdn
                if segments[0] != "crate" && segments.len() > 1 {
                    for root in ordered_source_roots(self) {
                        let top_dir = root.join(&segments[0]);
                        if top_dir.is_dir() {
                            if let Ok(resolved) = self.resolve_from_base(&top_dir, &segments[1..], path) {
                                return Ok(resolved);
                            }
                        }
                    }
                }

                // Strategy 5: Try project_root for top-level dirs not under source_root
                // e.g., "use examples.browser.*" → project_root/examples/browser/
                if segments[0] != "crate" && segments.len() > 1 {
                    let proj_dir = self.project_root.join(&segments[0]);
                    if proj_dir.is_dir() {
                        if let Ok(resolved) = self.resolve_from_base(&proj_dir, &segments[1..], path) {
                            return Ok(resolved);
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
            let direct = current.join(segment);

            if direct.exists() {
                current = direct;
            } else if let Some(numbered) = find_numbered_dir(&current, segment) {
                // Found numbered directory (e.g., 10.frontend for segment "frontend")
                current = numbered;
            } else if let Some(dotted) = find_dotted_dir(&current, segment) {
                // Supports dotted backend directories such as src/app/ui.web/
                current = dotted;
            } else {
                // E1034 - Unresolved Import
                let ctx = ErrorContext::new()
                    .with_code(codes::UNRESOLVED_IMPORT)
                    .with_help(format!("check that the module exists at {:?}", direct))
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
        let mod_path = dir_path.join("mod.spl");
        if mod_path.exists() && mod_path.is_file() {
            return Ok(ResolvedModule {
                path: mod_path,
                module_path: original_path.clone(),
                is_directory: true,
                manifest: None,
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

        // Try .shs file (Simple shell scripts)
        let shs_path = current.join(format!("{}.shs", last));
        if shs_path.exists() && shs_path.is_file() {
            return Ok(ResolvedModule {
                path: shs_path,
                module_path: original_path.clone(),
                is_directory: false,
                manifest: None,
            });
        }

        // Try numbered directory fallback for the last segment
        // e.g., "backend" → "70.backend/__init__.spl" or "70.backend/backend.spl"
        if let Some(numbered_dir) = find_numbered_dir(&current, last) {
            let numbered_init = numbered_dir.join("__init__.spl");
            if numbered_init.exists() && numbered_init.is_file() {
                return Ok(ResolvedModule {
                    path: numbered_init,
                    module_path: original_path.clone(),
                    is_directory: true,
                    manifest: None,
                });
            }
            let numbered_mod = numbered_dir.join("mod.spl");
            if numbered_mod.exists() && numbered_mod.is_file() {
                return Ok(ResolvedModule {
                    path: numbered_mod,
                    module_path: original_path.clone(),
                    is_directory: true,
                    manifest: None,
                });
            }
            // Try NN.name/name.spl (e.g., 70.backend/backend.spl)
            let numbered_file = numbered_dir.join(format!("{}.spl", last));
            if numbered_file.exists() && numbered_file.is_file() {
                return Ok(ResolvedModule {
                    path: numbered_file,
                    module_path: original_path.clone(),
                    is_directory: false,
                    manifest: None,
                });
            }
        }

        // Try dotted directory fallback for the last segment
        // e.g. app.ui.web -> src/app/ui.web/__init__.spl
        if let Some(dotted_dir) = find_dotted_dir(&current, last) {
            let dotted_init = dotted_dir.join("__init__.spl");
            if dotted_init.exists() && dotted_init.is_file() {
                return Ok(ResolvedModule {
                    path: dotted_init,
                    module_path: original_path.clone(),
                    is_directory: true,
                    manifest: None,
                });
            }
            let dotted_mod = dotted_dir.join("mod.spl");
            if dotted_mod.exists() && dotted_mod.is_file() {
                return Ok(ResolvedModule {
                    path: dotted_mod,
                    module_path: original_path.clone(),
                    is_directory: true,
                    manifest: None,
                });
            }

            let dotted_file = dotted_dir.join(format!("{}.spl", last));
            if dotted_file.exists() && dotted_file.is_file() {
                return Ok(ResolvedModule {
                    path: dotted_file,
                    module_path: original_path.clone(),
                    is_directory: false,
                    manifest: None,
                });
            }
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
                        // export * — re-export all public child modules (sibling .spl files)
                        for child in &manifest.child_modules {
                            if child.visibility == Visibility::Public {
                                exports.push(child.name.clone());
                            }
                        }
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

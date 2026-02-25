//! Module resolver for the Simple language module system.
//!
//! This module handles resolving module paths to filesystem locations
//! and managing directory manifests (__init__.spl files).
//!
//! ## Integration with dependency_tracker
//!
//! This module bridges the parser's AST types with the formally-verified
//! types in `simple_dependency_tracker`. The formal models ensure:
//!
//! - Module resolution is unambiguous (no foo.spl + foo/__init__.spl conflicts)
//! - Visibility is the intersection of item and ancestor visibility
//! - Glob imports only include macros listed in `auto import`

use simple_dependency_tracker::{
    self as tracker,
    graph::{ImportGraph, ImportKind},
    macro_import::{AutoImport, MacroDirManifest, MacroExports, MacroSymbol},
    resolution::ModPath,
    symbol::ProjectSymbols,
    visibility::{
        DirManifest as TrackerDirManifest, ModDecl as TrackerModDecl,
        Visibility as TrackerVisibility,
    },
};
use simple_parser::ast::{
    Attribute, AutoImportStmt, CommonUseStmt, ExportUseStmt, ImportTarget, Module, ModulePath,
    Node, Visibility,
};
use simple_parser::Parser;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::error::CompileError;

/// Result type for module resolution operations
pub type ResolveResult<T> = Result<T, CompileError>;

/// Represents a parsed __init__.spl directory manifest
#[derive(Debug, Clone, Default)]
pub struct DirectoryManifest {
    /// Directory name (must match directory)
    pub name: String,
    /// Directory-level attributes (#[no_gc], #[async], etc.)
    pub attributes: Vec<Attribute>,
    /// Child module declarations (mod name, pub mod name)
    pub child_modules: Vec<ChildModule>,
    /// Directory prelude imports (common use)
    pub common_uses: Vec<CommonUseStmt>,
    /// Public re-exports (export use)
    pub exports: Vec<ExportUseStmt>,
    /// Macro auto-imports (auto import)
    pub auto_imports: Vec<AutoImportStmt>,
}

impl DirectoryManifest {
    /// Convert to tracker's visibility DirManifest for formal model operations.
    pub fn to_tracker_visibility_manifest(&self) -> TrackerDirManifest {
        let mut manifest = TrackerDirManifest::new(&self.name);
        for child in &self.child_modules {
            manifest.add_child(TrackerModDecl::new(
                &child.name,
                child.visibility == Visibility::Public,
            ));
        }
        // Add exports from export use statements
        for export in &self.exports {
            match &export.target {
                ImportTarget::Single(name) => {
                    manifest.add_export(tracker::visibility::SymbolId::new(name));
                }
                ImportTarget::Aliased { name, .. } => {
                    manifest.add_export(tracker::visibility::SymbolId::new(name));
                }
                ImportTarget::Group(targets) => {
                    for target in targets {
                        if let ImportTarget::Single(name) = target {
                            manifest.add_export(tracker::visibility::SymbolId::new(name));
                        }
                    }
                }
                ImportTarget::Glob => {
                    // Glob exports are handled separately
                }
            }
        }
        manifest
    }

    /// Convert to tracker's macro DirManifest for formal model operations.
    pub fn to_tracker_macro_manifest(&self) -> MacroDirManifest {
        let mut manifest = MacroDirManifest::new(&self.name);
        for auto_import in &self.auto_imports {
            let module_path = auto_import.path.segments.join(".");
            manifest.add_auto_import(AutoImport::new(&module_path, &auto_import.macro_name));
        }
        manifest
    }

    /// Check if a child module is public.
    pub fn is_child_public(&self, name: &str) -> bool {
        self.child_modules
            .iter()
            .any(|c| c.name == name && c.visibility == Visibility::Public)
    }
}

/// A child module declaration from __init__.spl
#[derive(Debug, Clone)]
pub struct ChildModule {
    /// Module name
    pub name: String,
    /// Visibility (pub mod vs mod)
    pub visibility: Visibility,
    /// Module-specific attributes
    pub attributes: Vec<Attribute>,
}

/// Resolved module information
#[derive(Debug, Clone)]
pub struct ResolvedModule {
    /// Filesystem path to the module
    pub path: PathBuf,
    /// The module path used to reference it
    pub module_path: ModulePath,
    /// Whether this is a directory module (__init__.spl)
    pub is_directory: bool,
    /// Directory manifest if this is a directory module
    pub manifest: Option<DirectoryManifest>,
}

/// Module resolver that maps module paths to filesystem locations
#[derive(Debug)]
pub struct ModuleResolver {
    /// Project root directory (where simple.toml lives)
    project_root: PathBuf,
    /// Source root directory (from simple.toml [project].root)
    source_root: PathBuf,
    /// Cached directory manifests
    manifests: HashMap<PathBuf, DirectoryManifest>,
    /// Enabled features
    features: HashSet<String>,
    /// Profile definitions (name -> (attributes, imports))
    profiles: HashMap<String, (Vec<String>, Vec<String>)>,
    /// Import graph for cycle detection
    import_graph: ImportGraph,
    /// Project-wide symbol tables
    project_symbols: ProjectSymbols,
}

impl ModuleResolver {
    /// Create a new module resolver for a project
    pub fn new(project_root: PathBuf, source_root: PathBuf) -> Self {
        Self {
            project_root,
            source_root,
            manifests: HashMap::new(),
            features: HashSet::new(),
            profiles: HashMap::new(),
            import_graph: ImportGraph::new(),
            project_symbols: ProjectSymbols::new(),
        }
    }

    /// Create a resolver for single-file mode (no project)
    pub fn single_file(file_path: &Path) -> Self {
        let parent = file_path.parent().unwrap_or(Path::new(".")).to_path_buf();
        Self {
            project_root: parent.clone(),
            source_root: parent,
            manifests: HashMap::new(),
            features: HashSet::new(),
            profiles: HashMap::new(),
            import_graph: ImportGraph::new(),
            project_symbols: ProjectSymbols::new(),
        }
    }

    /// Set enabled features
    pub fn with_features(mut self, features: HashSet<String>) -> Self {
        self.features = features;
        self
    }

    /// Set profile definitions
    pub fn with_profiles(mut self, profiles: HashMap<String, (Vec<String>, Vec<String>)>) -> Self {
        self.profiles = profiles;
        self
    }

    /// Get the project root
    pub fn project_root(&self) -> &Path {
        &self.project_root
    }

    /// Get the source root
    pub fn source_root(&self) -> &Path {
        &self.source_root
    }

    /// Check if a feature is enabled
    pub fn is_feature_enabled(&self, name: &str) -> bool {
        self.features.contains(name)
    }

    /// Get profile definition
    pub fn get_profile(&self, name: &str) -> Option<&(Vec<String>, Vec<String>)> {
        self.profiles.get(name)
    }

    /// Resolve a module path to a filesystem path
    ///
    /// # Arguments
    /// * `path` - The module path to resolve (e.g., crate.sys.http.router)
    /// * `from_file` - The file making the import (for relative resolution)
    ///
    /// # Returns
    /// The resolved module information including filesystem path
    ///
    /// # Top-level module rewriting
    /// - `std.X` and `lib.X` → resolves from `src/lib/` (searches subdirectories)
    /// - `compiler.X` → resolves from `src/compiler/` (with numbered prefix stripping)
    /// - `app.X` → resolves from `src/app/`
    /// - `crate.X` → resolves from the configured source root
    pub fn resolve(&self, path: &ModulePath, from_file: &Path) -> ResolveResult<ResolvedModule> {
        let segments = &path.segments;
        if segments.is_empty() {
            return Err(CompileError::Semantic("empty module path".into()));
        }

        // Determine base directory and remaining segments based on first segment
        let first = &segments[0];
        let (base_dir, remaining) = match first.as_str() {
            "crate" => {
                // Absolute path from project root
                (self.source_root.clone(), &segments[1..])
            }
            "std" | "lib" => {
                // Standard library: std.X / lib.X → src/lib/X
                let lib_dir = self.source_root.join("lib");
                return self.resolve_std_import(&lib_dir, &segments[1..], path);
            }
            "compiler" => {
                // Compiler modules: compiler.common → src/compiler/00.common
                let compiler_dir = self.source_root.join("compiler");
                return self.resolve_from_base(&compiler_dir, &segments[1..], path);
            }
            "app" => {
                // Application modules: app.X → src/app/X
                let app_dir = self.source_root.join("app");
                return self.resolve_from_base(&app_dir, &segments[1..], path);
            }
            _ => {
                // Relative path from current file's directory
                let parent = from_file.parent().unwrap_or(Path::new("."));
                (parent.to_path_buf(), &segments[..])
            }
        };

        self.resolve_from_base(&base_dir, remaining, path)
    }

    /// Resolve from a base directory with remaining path segments.
    ///
    /// Supports numbered directory prefixes: when a segment `foo` is not found
    /// as a direct subdirectory, tries matching directories named `NN.foo`
    /// (e.g., `00.common`, `10.frontend`).
    fn resolve_from_base(
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
            current = match Self::resolve_dir_segment(&current, segment) {
                Some(dir) => dir,
                None => {
                    return Err(CompileError::Semantic(format!(
                        "module path segment '{}' not found under {:?}",
                        segment, current
                    )));
                }
            };
        }

        // Resolve the last segment
        let last = &segments[segments.len() - 1];
        self.resolve_last_segment(&current, last, original_path)
    }

    /// Resolve a directory segment, trying exact match first, then numbered prefix.
    ///
    /// Given parent `/src/compiler` and segment `common`, tries:
    /// 1. `/src/compiler/common/` (exact)
    /// 2. `/src/compiler/00.common/` (numbered prefix pattern `\d+\.{segment}`)
    fn resolve_dir_segment(parent: &Path, segment: &str) -> Option<PathBuf> {
        // Try exact match first
        let exact = parent.join(segment);
        if exact.is_dir() {
            return Some(exact);
        }

        // Try numbered prefix match: scan parent for directories matching NN.segment
        Self::find_numbered_dir(parent, segment)
    }

    /// Scan a parent directory for a subdirectory matching the pattern `\d+\.{name}`.
    ///
    /// Returns the first match found (directories are not guaranteed to be in any
    /// particular order, but numbered prefixes should be unique per logical name).
    fn find_numbered_dir(parent: &Path, name: &str) -> Option<PathBuf> {
        let entries = std::fs::read_dir(parent).ok()?;
        for entry in entries.flatten() {
            if !entry.file_type().map_or(false, |ft| ft.is_dir()) {
                continue;
            }
            let dir_name = entry.file_name();
            let dir_name_str = dir_name.to_string_lossy();
            if let Some(dot_pos) = dir_name_str.find('.') {
                let prefix = &dir_name_str[..dot_pos];
                let suffix = &dir_name_str[dot_pos + 1..];
                if prefix.chars().all(|c| c.is_ascii_digit()) && suffix == name {
                    return Some(entry.path());
                }
            }
        }
        None
    }

    /// Resolve the last path segment to either a directory module or a file.
    ///
    /// Tries in order:
    /// 1. Directory with `__init__.spl`
    /// 2. Directory with `mod.spl`
    /// 3. `{name}.spl` file
    /// 4. Numbered directory variants of the above (e.g., `00.common/__init__.spl`)
    fn resolve_last_segment(
        &self,
        current: &Path,
        last: &str,
        original_path: &ModulePath,
    ) -> ResolveResult<ResolvedModule> {
        // Try exact directory with __init__.spl
        let dir_path = current.join(last);
        if dir_path.is_dir() {
            let init_path = dir_path.join("__init__.spl");
            if init_path.exists() {
                return Ok(ResolvedModule {
                    path: init_path,
                    module_path: original_path.clone(),
                    is_directory: true,
                    manifest: None,
                });
            }
            // Try mod.spl
            let mod_path = dir_path.join("mod.spl");
            if mod_path.exists() {
                return Ok(ResolvedModule {
                    path: mod_path,
                    module_path: original_path.clone(),
                    is_directory: true,
                    manifest: None,
                });
            }
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

        // Try numbered directory prefix variants
        if let Some(numbered_dir) = Self::find_numbered_dir(current, last) {
            let init_path = numbered_dir.join("__init__.spl");
            if init_path.exists() {
                return Ok(ResolvedModule {
                    path: init_path,
                    module_path: original_path.clone(),
                    is_directory: true,
                    manifest: None,
                });
            }
            let mod_path = numbered_dir.join("mod.spl");
            if mod_path.exists() {
                return Ok(ResolvedModule {
                    path: mod_path,
                    module_path: original_path.clone(),
                    is_directory: true,
                    manifest: None,
                });
            }
        }

        Err(CompileError::Semantic(format!(
            "module '{}' not found (tried {:?} and {:?})",
            last,
            current.join(format!("{}.spl", last)),
            current.join(last).join("__init__.spl")
        )))
    }

    /// Resolve a `std` or `lib` import by searching through `src/lib/` subdirectories.
    ///
    /// The lib directory has multiple subdirectories (common/, nogc_sync_mut/, etc.)
    /// that contain the actual modules. So `std.common.text` tries:
    /// 1. Direct: `src/lib/common/text.spl`
    /// 2. Subdirectory search: `src/lib/*/common/text.spl`
    fn resolve_std_import(
        &self,
        lib_dir: &Path,
        segments: &[String],
        original_path: &ModulePath,
    ) -> ResolveResult<ResolvedModule> {
        if segments.is_empty() {
            return Err(CompileError::Semantic(
                "empty module path after 'std'/'lib'".into(),
            ));
        }

        // Try direct resolution from lib_dir
        if let Ok(resolved) = self.resolve_from_base(lib_dir, segments, original_path) {
            return Ok(resolved);
        }

        // Search through lib subdirectories (common/, nogc_sync_mut/, etc.)
        if let Ok(entries) = std::fs::read_dir(lib_dir) {
            for entry in entries.flatten() {
                if entry.file_type().map_or(false, |ft| ft.is_dir()) {
                    let subdir = entry.path();
                    if let Ok(resolved) = self.resolve_from_base(&subdir, segments, original_path)
                    {
                        return Ok(resolved);
                    }
                }
            }
        }

        Err(CompileError::Semantic(format!(
            "standard library module '{}' not found under {:?}",
            segments.join("."),
            lib_dir
        )))
    }

    /// Load and parse a directory manifest (__init__.spl)
    pub fn load_manifest(&mut self, dir_path: &Path) -> ResolveResult<DirectoryManifest> {
        let init_path = dir_path.join("__init__.spl");

        if let Some(cached) = self.manifests.get(&init_path) {
            return Ok(cached.clone());
        }

        if !init_path.exists() {
            return Ok(DirectoryManifest::default());
        }

        let source = std::fs::read_to_string(&init_path).map_err(|e| {
            CompileError::Semantic(format!("failed to read {:?}: {}", init_path, e))
        })?;

        let manifest = self.parse_manifest(&source, dir_path)?;
        self.manifests.insert(init_path, manifest.clone());

        Ok(manifest)
    }

    /// Parse a directory manifest from source
    fn parse_manifest(&self, source: &str, dir_path: &Path) -> ResolveResult<DirectoryManifest> {
        let mut parser = Parser::new(source);
        let module = parser.parse().map_err(|e| {
            CompileError::Semantic(format!("failed to parse __init__.spl: {:?}", e))
        })?;

        self.extract_manifest(&module, dir_path)
    }

    /// Extract manifest information from parsed AST
    fn extract_manifest(
        &self,
        module: &Module,
        dir_path: &Path,
    ) -> ResolveResult<DirectoryManifest> {
        let dir_name = dir_path
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("unknown")
            .to_string();

        let mut manifest = DirectoryManifest {
            name: dir_name,
            ..Default::default()
        };

        for item in &module.items {
            match item {
                Node::ModDecl(decl) => {
                    // Check if this is the directory header (mod <dirname>)
                    if manifest.child_modules.is_empty() && decl.name == manifest.name {
                        // This is the directory header - extract attributes
                        manifest.attributes = decl.attributes.clone();
                    } else {
                        // This is a child module declaration
                        manifest.child_modules.push(ChildModule {
                            name: decl.name.clone(),
                            visibility: decl.visibility,
                            attributes: decl.attributes.clone(),
                        });
                    }
                }
                Node::CommonUseStmt(stmt) => {
                    manifest.common_uses.push(stmt.clone());
                }
                Node::ExportUseStmt(stmt) => {
                    manifest.exports.push(stmt.clone());
                }
                Node::AutoImportStmt(stmt) => {
                    manifest.auto_imports.push(stmt.clone());
                }
                Node::UseStmt(_) => {
                    // Regular use statements in __init__.spl are allowed but
                    // don't affect the manifest structure
                }
                _ => {
                    // Other nodes in __init__.spl are not part of the manifest
                    // (functions, types, etc. should not be in __init__.spl per spec)
                }
            }
        }

        Ok(manifest)
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

    /// Get the import graph.
    pub fn import_graph(&self) -> &ImportGraph {
        &self.import_graph
    }

    /// Get mutable access to project symbols.
    pub fn project_symbols_mut(&mut self) -> &mut ProjectSymbols {
        &mut self.project_symbols
    }

    /// Get project symbols.
    pub fn project_symbols(&self) -> &ProjectSymbols {
        &self.project_symbols
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
        tracker::visibility::ancestor_visibility(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_helpers::create_test_project;
    use std::fs;

    #[test]
    fn test_resolver_creation() {
        let dir = create_test_project();
        let resolver = ModuleResolver::new(dir.path().to_path_buf(), dir.path().join("src"));
        assert_eq!(resolver.project_root(), dir.path());
        assert_eq!(resolver.source_root(), dir.path().join("src"));
    }

    #[test]
    fn test_single_file_mode() {
        let resolver = ModuleResolver::single_file(Path::new("/tmp/test.spl"));
        assert_eq!(resolver.project_root(), Path::new("/tmp"));
        assert_eq!(resolver.source_root(), Path::new("/tmp"));
    }

    #[test]
    fn test_resolve_file_module() {
        let dir = create_test_project();
        let src = dir.path().join("src");

        // Create a module file
        fs::write(src.join("utils.spl"), "fn helper(): 42").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["crate".into(), "utils".into()]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();

        assert_eq!(resolved.path, src.join("utils.spl"));
        assert!(!resolved.is_directory);
    }

    #[test]
    fn test_resolve_directory_module() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let http = src.join("http");
        fs::create_dir_all(&http).unwrap();

        // Create __init__.spl
        fs::write(http.join("__init__.spl"), "mod http\npub mod router").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["crate".into(), "http".into()]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();

        assert_eq!(resolved.path, http.join("__init__.spl"));
        assert!(resolved.is_directory);
    }

    #[test]
    fn test_resolve_nested_module() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let http = src.join("sys").join("http");
        fs::create_dir_all(&http).unwrap();

        fs::write(http.join("router.spl"), "struct Router:").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec![
            "crate".into(),
            "sys".into(),
            "http".into(),
            "router".into(),
        ]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();

        assert_eq!(resolved.path, http.join("router.spl"));
    }

    #[test]
    fn test_resolve_module_not_found() {
        let dir = create_test_project();
        let src = dir.path().join("src");

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["crate".into(), "nonexistent".into()]);
        let result = resolver.resolve(&path, &src.join("main.spl"));

        assert!(result.is_err());
    }

    #[test]
    fn test_parse_manifest() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let http = src.join("http");
        fs::create_dir_all(&http).unwrap();

        let manifest_source = r#"
#[no_gc]
mod http

pub mod router
mod internal

common use crate.core.base.*

export use router.Router
export use router.route

auto import router.route
"#;
        fs::write(http.join("__init__.spl"), manifest_source).unwrap();

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);

        let manifest = resolver.load_manifest(&http).unwrap();

        assert_eq!(manifest.name, "http");
        assert_eq!(manifest.child_modules.len(), 2);
        assert_eq!(manifest.child_modules[0].name, "router");
        assert_eq!(manifest.child_modules[0].visibility, Visibility::Public);
        assert_eq!(manifest.child_modules[1].name, "internal");
        assert_eq!(manifest.child_modules[1].visibility, Visibility::Private);
        assert_eq!(manifest.common_uses.len(), 1);
        assert_eq!(manifest.exports.len(), 2);
        assert_eq!(manifest.auto_imports.len(), 1);
    }

    #[test]
    fn test_features() {
        let dir = create_test_project();
        let mut features = HashSet::new();
        features.insert("strict_null".into());

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), dir.path().join("src"))
            .with_features(features);

        assert!(resolver.is_feature_enabled("strict_null"));
        assert!(!resolver.is_feature_enabled("other_feature"));
    }

    #[test]
    fn test_effective_visibility_formal_model() {
        // This test demonstrates the integration with the formal verification model
        // from verification/visibility_export/
        let dir = create_test_project();
        let src = dir.path().join("src");
        let http = src.join("http");
        fs::create_dir_all(&http).unwrap();

        let manifest_source = r#"
mod http
pub mod router
mod internal
export use router.Router
"#;
        fs::write(http.join("__init__.spl"), manifest_source).unwrap();

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);

        let manifest = resolver.load_manifest(&http).unwrap();

        // Public module + exported symbol = public effective visibility
        let vis = resolver.effective_visibility(&manifest, "router", "Router", Visibility::Public);
        assert_eq!(vis, TrackerVisibility::Public);

        // Public module + unexported symbol = private effective visibility
        let vis = resolver.effective_visibility(&manifest, "router", "helper", Visibility::Public);
        assert_eq!(vis, TrackerVisibility::Private);

        // Private module = private effective visibility
        let vis = resolver.effective_visibility(&manifest, "internal", "Foo", Visibility::Public);
        assert_eq!(vis, TrackerVisibility::Private);

        // Private symbol = private effective visibility
        let vis = resolver.effective_visibility(&manifest, "router", "Router", Visibility::Private);
        assert_eq!(vis, TrackerVisibility::Private);
    }

    #[test]
    fn test_macro_auto_import_formal_model() {
        // This test demonstrates the integration with the formal verification model
        // from verification/macro_auto_import/
        use simple_dependency_tracker::macro_import::{MacroSymbol, SymKind};

        let dir = create_test_project();
        let src = dir.path().join("src");
        let http = src.join("http");
        fs::create_dir_all(&http).unwrap();

        let manifest_source = r#"
mod http
pub mod router
auto import router.route
"#;
        fs::write(http.join("__init__.spl"), manifest_source).unwrap();

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);

        let manifest = resolver.load_manifest(&http).unwrap();

        // Create mock exports
        let mut exports = MacroExports::new();
        exports.add_non_macro(MacroSymbol::value("router", "Router"));
        exports.add_macro(MacroSymbol::macro_def("router", "route"));
        exports.add_macro(MacroSymbol::macro_def("router", "get"));

        // Glob import should include:
        // - All non-macros (Router)
        // - Only auto-imported macros (route, not get)
        let result = resolver.filter_glob_import(&manifest, &exports);

        assert_eq!(result.len(), 2); // Router + route
        assert!(result
            .iter()
            .any(|s| s.name == "Router" && s.kind == SymKind::ValueOrType));
        assert!(result
            .iter()
            .any(|s| s.name == "route" && s.kind == SymKind::Macro));
        assert!(!result.iter().any(|s| s.name == "get")); // Not in auto import
    }

    #[test]
    fn test_circular_dependency_detection() {
        let dir = create_test_project();
        let src = dir.path().join("src");

        let mut resolver = ModuleResolver::new(dir.path().to_path_buf(), src);

        // Create a cycle: a -> b -> c -> a
        resolver.record_import("crate.a", "crate.b", ImportKind::Use);
        resolver.record_import("crate.b", "crate.c", ImportKind::Use);
        resolver.record_import("crate.c", "crate.a", ImportKind::Use);

        let result = resolver.check_circular_dependencies();
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("Circular dependency"));
    }

    // ========== Numbered directory prefix tests ==========

    #[test]
    fn test_numbered_prefix_resolve_compiler_common() {
        // compiler.common.di -> src/compiler/00.common/di.spl
        let dir = create_test_project();
        let src = dir.path().join("src");
        let common_dir = src.join("compiler").join("00.common");
        fs::create_dir_all(&common_dir).unwrap();
        fs::write(common_dir.join("di.spl"), "# di module").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec![
            "compiler".into(),
            "common".into(),
            "di".into(),
        ]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();
        assert_eq!(resolved.path, common_dir.join("di.spl"));
        assert!(!resolved.is_directory);
    }

    #[test]
    fn test_numbered_prefix_resolve_compiler_frontend_nested() {
        // compiler.frontend.core.lexer -> src/compiler/10.frontend/core/lexer.spl
        let dir = create_test_project();
        let src = dir.path().join("src");
        let frontend_dir = src.join("compiler").join("10.frontend").join("core");
        fs::create_dir_all(&frontend_dir).unwrap();
        fs::write(frontend_dir.join("lexer.spl"), "# lexer module").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec![
            "compiler".into(),
            "frontend".into(),
            "core".into(),
            "lexer".into(),
        ]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();
        assert_eq!(resolved.path, frontend_dir.join("lexer.spl"));
    }

    #[test]
    fn test_numbered_prefix_directory_with_init() {
        // compiler.common -> src/compiler/00.common/__init__.spl
        let dir = create_test_project();
        let src = dir.path().join("src");
        let common_dir = src.join("compiler").join("00.common");
        fs::create_dir_all(&common_dir).unwrap();
        fs::write(common_dir.join("__init__.spl"), "mod common").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["compiler".into(), "common".into()]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();
        assert_eq!(resolved.path, common_dir.join("__init__.spl"));
        assert!(resolved.is_directory);
    }

    #[test]
    fn test_numbered_prefix_directory_with_mod_spl() {
        // compiler.backend -> src/compiler/70.backend/mod.spl
        let dir = create_test_project();
        let src = dir.path().join("src");
        let backend_dir = src.join("compiler").join("70.backend");
        fs::create_dir_all(&backend_dir).unwrap();
        fs::write(backend_dir.join("mod.spl"), "mod backend").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["compiler".into(), "backend".into()]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();
        assert_eq!(resolved.path, backend_dir.join("mod.spl"));
        assert!(resolved.is_directory);
    }

    #[test]
    fn test_exact_match_preferred_over_numbered() {
        // If both "common" and "00.common" exist, exact match wins
        let dir = create_test_project();
        let src = dir.path().join("src");
        let exact_dir = src.join("compiler").join("common");
        let numbered_dir = src.join("compiler").join("00.common");
        fs::create_dir_all(&exact_dir).unwrap();
        fs::create_dir_all(&numbered_dir).unwrap();
        fs::write(exact_dir.join("di.spl"), "# exact match").unwrap();
        fs::write(numbered_dir.join("di.spl"), "# numbered match").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec![
            "compiler".into(),
            "common".into(),
            "di".into(),
        ]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();
        // Exact directory match should be preferred
        assert_eq!(resolved.path, exact_dir.join("di.spl"));
    }

    #[test]
    fn test_non_numbered_directories_still_work() {
        // Regular directories without numbered prefixes should still resolve
        let dir = create_test_project();
        let src = dir.path().join("src");
        let regular_dir = src.join("compiler").join("utils");
        fs::create_dir_all(&regular_dir).unwrap();
        fs::write(regular_dir.join("helper.spl"), "# helper").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec![
            "compiler".into(),
            "utils".into(),
            "helper".into(),
        ]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();
        assert_eq!(resolved.path, regular_dir.join("helper.spl"));
    }

    // ========== std -> lib rewrite tests ==========

    #[test]
    fn test_std_resolves_to_lib_directory() {
        // std.common.text -> src/lib/common/text.spl
        let dir = create_test_project();
        let src = dir.path().join("src");
        let lib_common = src.join("lib").join("common");
        fs::create_dir_all(&lib_common).unwrap();
        fs::write(lib_common.join("text.spl"), "# text module").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["std".into(), "common".into(), "text".into()]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();
        assert_eq!(resolved.path, lib_common.join("text.spl"));
    }

    #[test]
    fn test_lib_resolves_to_lib_directory() {
        // lib.common.text -> src/lib/common/text.spl (same as std)
        let dir = create_test_project();
        let src = dir.path().join("src");
        let lib_common = src.join("lib").join("common");
        fs::create_dir_all(&lib_common).unwrap();
        fs::write(lib_common.join("text.spl"), "# text module").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["lib".into(), "common".into(), "text".into()]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();
        assert_eq!(resolved.path, lib_common.join("text.spl"));
    }

    #[test]
    fn test_std_searches_lib_subdirectories() {
        // std.text -> src/lib/common/text.spl (searched through subdirs)
        let dir = create_test_project();
        let src = dir.path().join("src");
        let lib_common = src.join("lib").join("common");
        fs::create_dir_all(&lib_common).unwrap();
        fs::write(lib_common.join("text.spl"), "# text module").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["std".into(), "text".into()]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();
        assert_eq!(resolved.path, lib_common.join("text.spl"));
    }

    #[test]
    fn test_std_not_found() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let lib_dir = src.join("lib");
        fs::create_dir_all(&lib_dir).unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["std".into(), "nonexistent".into()]);
        let result = resolver.resolve(&path, &src.join("main.spl"));
        assert!(result.is_err());
    }

    // ========== app prefix tests ==========

    #[test]
    fn test_app_prefix_resolves() {
        // app.mcp.main_lazy -> src/app/mcp/main_lazy.spl
        let dir = create_test_project();
        let src = dir.path().join("src");
        let app_mcp = src.join("app").join("mcp");
        fs::create_dir_all(&app_mcp).unwrap();
        fs::write(app_mcp.join("main_lazy.spl"), "# mcp main").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["app".into(), "mcp".into(), "main_lazy".into()]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();
        assert_eq!(resolved.path, app_mcp.join("main_lazy.spl"));
    }

    // ========== find_numbered_dir unit tests ==========

    #[test]
    fn test_find_numbered_dir_found() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let compiler = src.join("compiler");
        fs::create_dir_all(compiler.join("00.common")).unwrap();
        fs::create_dir_all(compiler.join("10.frontend")).unwrap();
        fs::create_dir_all(compiler.join("70.backend")).unwrap();

        assert_eq!(
            ModuleResolver::find_numbered_dir(&compiler, "common"),
            Some(compiler.join("00.common"))
        );
        assert_eq!(
            ModuleResolver::find_numbered_dir(&compiler, "frontend"),
            Some(compiler.join("10.frontend"))
        );
        assert_eq!(
            ModuleResolver::find_numbered_dir(&compiler, "backend"),
            Some(compiler.join("70.backend"))
        );
    }

    #[test]
    fn test_find_numbered_dir_not_found() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let compiler = src.join("compiler");
        fs::create_dir_all(compiler.join("00.common")).unwrap();

        assert_eq!(
            ModuleResolver::find_numbered_dir(&compiler, "nonexistent"),
            None
        );
    }

    #[test]
    fn test_find_numbered_dir_ignores_non_numeric_prefix() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let compiler = src.join("compiler");
        // Directory with a non-numeric prefix should NOT match
        fs::create_dir_all(compiler.join("abc.common")).unwrap();

        assert_eq!(
            ModuleResolver::find_numbered_dir(&compiler, "common"),
            None
        );
    }

    #[test]
    fn test_resolve_dir_segment_exact_preferred() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let compiler = src.join("compiler");
        fs::create_dir_all(compiler.join("common")).unwrap();
        fs::create_dir_all(compiler.join("00.common")).unwrap();

        // Exact match should be preferred
        let result = ModuleResolver::resolve_dir_segment(&compiler, "common");
        assert_eq!(result, Some(compiler.join("common")));
    }

    #[test]
    fn test_resolve_dir_segment_numbered_fallback() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let compiler = src.join("compiler");
        // Only numbered directory exists
        fs::create_dir_all(compiler.join("10.frontend")).unwrap();

        let result = ModuleResolver::resolve_dir_segment(&compiler, "frontend");
        assert_eq!(result, Some(compiler.join("10.frontend")));
    }

    #[test]
    fn test_resolve_dir_segment_no_match() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let compiler = src.join("compiler");
        fs::create_dir_all(&compiler).unwrap();

        let result = ModuleResolver::resolve_dir_segment(&compiler, "missing");
        assert_eq!(result, None);
    }

    // ========== End-to-end resolution tests mimicking real project layout ==========

    #[test]
    fn test_full_compiler_tree_resolution() {
        // Simulate the real project layout with multiple numbered directories
        let dir = create_test_project();
        let src = dir.path().join("src");

        // Create numbered compiler directories
        let dirs = vec![
            "00.common",
            "10.frontend",
            "30.types",
            "70.backend",
            "95.interp",
        ];
        for d in &dirs {
            fs::create_dir_all(src.join("compiler").join(d)).unwrap();
        }

        // Create test files in various places
        fs::write(
            src.join("compiler").join("00.common").join("di_config.spl"),
            "# DI config",
        )
        .unwrap();
        fs::create_dir_all(
            src.join("compiler")
                .join("10.frontend")
                .join("core"),
        )
        .unwrap();
        fs::write(
            src.join("compiler")
                .join("10.frontend")
                .join("core")
                .join("lexer.spl"),
            "# lexer",
        )
        .unwrap();
        fs::write(
            src.join("compiler")
                .join("95.interp")
                .join("interpreter.spl"),
            "# interpreter",
        )
        .unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
        let from = src.join("main.spl");

        // compiler.common.di_config
        let path = ModulePath::new(vec![
            "compiler".into(),
            "common".into(),
            "di_config".into(),
        ]);
        let resolved = resolver.resolve(&path, &from).unwrap();
        assert_eq!(
            resolved.path,
            src.join("compiler/00.common/di_config.spl")
        );

        // compiler.frontend.core.lexer
        let path = ModulePath::new(vec![
            "compiler".into(),
            "frontend".into(),
            "core".into(),
            "lexer".into(),
        ]);
        let resolved = resolver.resolve(&path, &from).unwrap();
        assert_eq!(
            resolved.path,
            src.join("compiler/10.frontend/core/lexer.spl")
        );

        // compiler.interp.interpreter
        let path = ModulePath::new(vec![
            "compiler".into(),
            "interp".into(),
            "interpreter".into(),
        ]);
        let resolved = resolver.resolve(&path, &from).unwrap();
        assert_eq!(
            resolved.path,
            src.join("compiler/95.interp/interpreter.spl")
        );
    }

    #[test]
    fn test_std_with_nogc_sync_mut_subdir() {
        // std.spec.matchers -> src/lib/nogc_sync_mut/spec/matchers.spl
        let dir = create_test_project();
        let src = dir.path().join("src");
        let spec_dir = src.join("lib").join("nogc_sync_mut").join("spec");
        fs::create_dir_all(&spec_dir).unwrap();
        fs::write(spec_dir.join("matchers.spl"), "# matchers").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["std".into(), "spec".into(), "matchers".into()]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();
        assert_eq!(resolved.path, spec_dir.join("matchers.spl"));
    }

    #[test]
    fn test_std_directory_module_with_mod_spl() {
        // std.common -> src/lib/common/mod.spl
        let dir = create_test_project();
        let src = dir.path().join("src");
        let lib_common = src.join("lib").join("common");
        fs::create_dir_all(&lib_common).unwrap();
        fs::write(lib_common.join("mod.spl"), "mod common").unwrap();

        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());

        let path = ModulePath::new(vec!["std".into(), "common".into()]);
        let resolved = resolver.resolve(&path, &src.join("main.spl")).unwrap();
        assert_eq!(resolved.path, lib_common.join("mod.spl"));
        assert!(resolved.is_directory);
    }
}

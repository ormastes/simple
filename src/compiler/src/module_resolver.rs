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
}

//! Type definitions for module resolution.
//!
//! This module contains the core types used in module resolution:
//! - DirectoryManifest: Parsed __init__.spl structure
//! - ChildModule: Child module declaration
//! - ResolvedModule: Resolved module information
//! - ModuleResolver: Main resolver struct

use simple_dependency_tracker::{graph::ImportGraph, symbol::ProjectSymbols};
use simple_parser::ast::{Attribute, AutoImportStmt, Capability, CommonUseStmt, ExportUseStmt, Visibility};
use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

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
    /// Required capabilities (from `requires [pure, io, ...]`)
    /// Empty means unrestricted (all effects allowed)
    pub capabilities: Vec<Capability>,
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
    pub module_path: simple_parser::ast::ModulePath,
    /// Whether this is a directory module (__init__.spl)
    pub is_directory: bool,
    /// Directory manifest if this is a directory module
    pub manifest: Option<DirectoryManifest>,
}

/// Module resolver that maps module paths to filesystem locations
#[derive(Debug)]
pub struct ModuleResolver {
    /// Project root directory (where simple.toml lives)
    pub(super) project_root: PathBuf,
    /// Source root directory (from simple.toml [project].root)
    pub(super) source_root: PathBuf,
    /// Standard library root directory (src/lib/std/src)
    pub(super) stdlib_root: Option<PathBuf>,
    /// Cached directory manifests
    pub(super) manifests: HashMap<PathBuf, DirectoryManifest>,
    /// Enabled features
    pub(super) features: HashSet<String>,
    /// Profile definitions (name -> (attributes, imports))
    pub(super) profiles: HashMap<String, (Vec<String>, Vec<String>)>,
    /// Import graph for cycle detection
    pub(super) import_graph: ImportGraph,
    /// Project-wide symbol tables
    pub(super) project_symbols: ProjectSymbols,
}

impl ModuleResolver {
    /// Create a new module resolver for a project
    pub fn new(project_root: PathBuf, source_root: PathBuf) -> Self {
        // Auto-detect stdlib location
        let stdlib_root = project_root.join("src/lib/std/src");
        let stdlib_root = if stdlib_root.exists() { Some(stdlib_root) } else { None };

        Self {
            project_root,
            source_root,
            stdlib_root,
            manifests: HashMap::new(),
            features: HashSet::new(),
            profiles: HashMap::new(),
            import_graph: ImportGraph::new(),
            project_symbols: ProjectSymbols::new(),
        }
    }

    /// Create a resolver for single-file mode (no project)
    pub fn single_file(file_path: &std::path::Path) -> Self {
        let parent = file_path.parent().unwrap_or(std::path::Path::new(".")).to_path_buf();

        // Try to detect stdlib even in single-file mode
        // Check multiple possible stdlib locations
        let stdlib_candidates = ["src/lib/std/src", "simple/std_lib/src", "std_lib/src"];

        let stdlib_root = {
            // First try relative to current file
            let mut found = None;
            for candidate_path in &stdlib_candidates {
                let candidate = parent.join(candidate_path);
                if candidate.exists() {
                    found = Some(candidate);
                    break;
                }
            }

            // If not found, try parent directories
            if found.is_none() {
                let mut current = parent.clone();
                'outer: for _ in 0..5 {
                    for candidate_path in &stdlib_candidates {
                        let candidate = current.join(candidate_path);
                        if candidate.exists() {
                            found = Some(candidate);
                            break 'outer;
                        }
                    }
                    if let Some(p) = current.parent() {
                        current = p.to_path_buf();
                    } else {
                        break;
                    }
                }
            }
            found
        };

        Self {
            project_root: parent.clone(),
            source_root: parent,
            stdlib_root,
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
    pub fn project_root(&self) -> &std::path::Path {
        &self.project_root
    }

    /// Get the source root
    pub fn source_root(&self) -> &std::path::Path {
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
}

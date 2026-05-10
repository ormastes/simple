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
use std::path::{Path, PathBuf};

use crate::error::CompileError;

/// Compiler backend for a file extension
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompilerBackend {
    /// Full interpreter pipeline
    Interpreted,
    /// Cranelift JIT compilation
    Cranelift,
}

/// File mode determines auto-imports and default behavior
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileMode {
    /// Standard Simple code
    Standard,
    /// Shell scripting mode (auto-imports std.shell.*)
    Shell,
    /// Data notation (SDN)
    Data,
}

/// Configuration for a file extension
#[derive(Debug, Clone)]
pub struct ExtensionConfig {
    /// File extension (without dot)
    pub extension: &'static str,
    /// Compiler backend
    pub backend: CompilerBackend,
    /// File mode
    pub mode: FileMode,
    /// Description
    pub description: &'static str,
}

/// Known extension configurations
pub static EXTENSION_CONFIGS: &[ExtensionConfig] = &[
    ExtensionConfig {
        extension: "spl",
        backend: CompilerBackend::Interpreted,
        mode: FileMode::Standard,
        description: "Simple language source",
    },
    ExtensionConfig {
        extension: "simple",
        backend: CompilerBackend::Interpreted,
        mode: FileMode::Standard,
        description: "Simple language source (alt extension)",
    },
    ExtensionConfig {
        extension: "sscript",
        backend: CompilerBackend::Interpreted,
        mode: FileMode::Standard,
        description: "Simple script",
    },
    ExtensionConfig {
        extension: "shs",
        backend: CompilerBackend::Interpreted,
        mode: FileMode::Shell,
        description: "Simple shell script",
    },
    ExtensionConfig {
        extension: "sdn",
        backend: CompilerBackend::Interpreted,
        mode: FileMode::Data,
        description: "Simple data notation",
    },
];

/// Look up extension config by extension string
pub fn get_extension_config(ext: &str) -> Option<&'static ExtensionConfig> {
    EXTENSION_CONFIGS.iter().find(|c| c.extension == ext)
}

/// Get the file mode for an extension
pub fn get_file_mode(ext: &str) -> FileMode {
    get_extension_config(ext).map(|c| c.mode).unwrap_or(FileMode::Standard)
}

/// Get the compiler backend for an extension
pub fn get_compiler_backend(ext: &str) -> CompilerBackend {
    get_extension_config(ext)
        .map(|c| c.backend)
        .unwrap_or(CompilerBackend::Interpreted)
}

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
    /// Whether this directory has the #[bypass] attribute.
    /// Bypass directories are transparent for access control — they act as if
    /// no __init__.spl exists. Only valid for directories with no .spl code files.
    pub is_bypass: bool,
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

//==============================================================================
// Module Lifecycle Management (FR-COMPILER-010)
//==============================================================================

/// Lifecycle state of a module in the compilation pipeline.
///
/// States advance monotonically: Unloaded → Loading → Parsed → TypeChecked
/// → Lowered → Compiled.  The `Loading` state guards against circular imports.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ModuleState {
    /// Module has not been encountered yet.
    Unloaded,
    /// Module is currently being parsed/lowered (cycle guard).
    Loading,
    /// Source file has been parsed into an AST.
    Parsed,
    /// Types have been resolved and checked.
    TypeChecked,
    /// HIR has been lowered from the AST.
    Lowered,
    /// Machine code / bytecode has been emitted.
    Compiled,
}

impl ModuleState {
    /// Returns `true` if the module has progressed at least to `Lowered`.
    pub fn is_lowered(&self) -> bool {
        *self >= ModuleState::Lowered
    }

    /// Returns `true` while the module is actively being processed (cycle guard).
    pub fn is_loading(&self) -> bool {
        *self == ModuleState::Loading
    }
}

/// Tracks the lifecycle state for each module seen during a compilation run.
///
/// Wraps the raw `loaded_modules: HashSet<PathBuf>` already stored in
/// `Lowerer` by recording the fine-grained state instead of a boolean.
/// The `Lowerer` can delegate its duplicate-loading checks to this tracker.
#[derive(Debug, Default)]
pub struct ModuleLifecycle {
    states: HashMap<PathBuf, ModuleState>,
}

impl ModuleLifecycle {
    /// Create an empty lifecycle tracker.
    pub fn new() -> Self {
        Self { states: HashMap::new() }
    }

    /// Return the current state of a module, defaulting to `Unloaded`.
    pub fn state(&self, path: &Path) -> ModuleState {
        self.states.get(path).copied().unwrap_or(ModuleState::Unloaded)
    }

    /// Advance a module to the given state.  Silently ignores regressions
    /// (a state can never move backwards).
    pub fn advance(&mut self, path: PathBuf, new_state: ModuleState) {
        let entry = self.states.entry(path).or_insert(ModuleState::Unloaded);
        if new_state > *entry {
            *entry = new_state;
        }
    }

    /// Returns `true` if the module is already loaded (at or past `Lowered`).
    pub fn is_loaded(&self, path: &Path) -> bool {
        self.state(path).is_lowered()
    }

    /// Returns `true` if the module is currently mid-load (cycle guard).
    pub fn is_loading(&self, path: &Path) -> bool {
        self.state(path).is_loading()
    }

    /// Mark a module as `Loading` to begin processing it.  Returns `false`
    /// if the module is already being loaded (circular import detected).
    pub fn begin_loading(&mut self, path: PathBuf) -> bool {
        let current = self.state(&path);
        if current == ModuleState::Loading || current.is_lowered() {
            return false;
        }
        self.advance(path, ModuleState::Loading);
        true
    }
}

/// Module resolver that maps module paths to filesystem locations
#[derive(Debug)]
pub struct ModuleResolver {
    /// Project root directory (where simple.toml lives)
    pub(super) project_root: PathBuf,
    /// Source root directory (from simple.toml [project].root)
    pub(super) source_root: PathBuf,
    /// Additional source roots available for native multi-root builds.
    pub(super) extra_source_roots: Vec<PathBuf>,
    /// Project-scoped logical type root (project_root/src/type)
    pub(super) type_root: PathBuf,
    /// Default owned domain used for bare type imports
    pub(super) default_type_domain: String,
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
            type_root: project_root.join("src").join("type"),
            project_root,
            source_root,
            extra_source_roots: Vec::new(),
            default_type_domain: "simple-lang".to_string(),
            stdlib_root,
            manifests: HashMap::new(),
            features: HashSet::new(),
            profiles: HashMap::new(),
            import_graph: ImportGraph::new(),
            project_symbols: ProjectSymbols::new(),
        }
    }

    /// Create a resolver for single-file mode (no project)
    pub fn single_file(file_path: &Path) -> Self {
        Self::single_file_with_project_hint(file_path, None)
    }

    /// Create a resolver for single-file mode, optionally borrowing project context
    /// from a separate hint path when the source file itself lives outside the project tree.
    pub fn single_file_with_project_hint(file_path: &Path, project_hint: Option<&Path>) -> Self {
        let normalized_file_path = normalize_input_path(file_path);
        let parent = normalized_file_path.parent().unwrap_or(Path::new(".")).to_path_buf();
        let project_root = find_project_root(&normalized_file_path)
            .or_else(|| project_hint.and_then(find_project_root))
            .unwrap_or_else(|| parent.clone());
        let source_root = if project_root.join("src").is_dir() {
            project_root.join("src")
        } else {
            parent.clone()
        };
        let stdlib_root = detect_stdlib_root(&project_root, &parent);

        Self {
            type_root: project_root.join("src").join("type"),
            project_root,
            source_root,
            extra_source_roots: Vec::new(),
            default_type_domain: "simple-lang".to_string(),
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

    /// Set additional source roots searched for top-level imports.
    pub fn with_extra_source_roots(mut self, roots: Vec<PathBuf>) -> Self {
        self.extra_source_roots = roots;
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

fn normalize_input_path(path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .map(|cwd| cwd.join(path))
            .unwrap_or_else(|_| path.to_path_buf())
    }
}

fn find_project_root(path: &Path) -> Option<PathBuf> {
    let normalized = normalize_input_path(path);
    let mut current = if normalized.is_dir() {
        normalized
    } else {
        normalized.parent()?.to_path_buf()
    };

    loop {
        if current.join("src").is_dir() || current.join("Cargo.toml").is_file() {
            return Some(current);
        }
        if !current.pop() {
            return None;
        }
    }
}

fn detect_stdlib_root(project_root: &Path, file_parent: &Path) -> Option<PathBuf> {
    let stdlib_candidates = [
        "src/lib",
        "src/std",
        "src/std/src",
        "src/lib/std/src",
        "simple/std_lib/src",
        "std_lib/src",
    ];

    for candidate_path in &stdlib_candidates {
        let candidate = project_root.join(candidate_path);
        if candidate.exists() {
            return Some(candidate);
        }
    }

    let mut current = file_parent.to_path_buf();
    for _ in 0..5 {
        for candidate_path in &stdlib_candidates {
            let candidate = current.join(candidate_path);
            if candidate.exists() {
                return Some(candidate);
            }
        }
        if let Some(parent) = current.parent() {
            current = parent.to_path_buf();
        } else {
            break;
        }
    }

    None
}

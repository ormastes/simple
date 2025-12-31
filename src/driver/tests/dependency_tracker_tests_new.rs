//! System tests for dependency tracker (Features #112-117)
//!
//! These tests verify the formally-verified dependency tracking system works
//! correctly with actual filesystem operations and multi-file projects.
//!
//! ## Formal Verification Coverage
//!
//! The tests verify properties proven in the Lean 4 models:
//! - module_resolution: Module paths are unambiguous in well-formed filesystems
//! - visibility_export: Effective visibility is intersection of item and ancestor visibility
//! - macro_auto_import: Glob imports only include macros listed in auto import
//!
//! ## Test Categories
//!
//! 1. Module Resolution - file vs directory module detection
//! 2. Visibility Rules - pub/priv and export filtering
//! 3. Macro Auto-Import - glob import macro filtering
//! 4. Circular Dependency - import cycle detection
//! 5. Symbol Resolution - cross-module symbol lookup
//!
//! Split into 5 files by feature:
//! - dependency_tracker_tests_module_resolution.rs: Feature #113
//! - dependency_tracker_tests_visibility.rs: Feature #114
//! - dependency_tracker_tests_macro.rs: Feature #115
//! - dependency_tracker_tests_circular.rs: Feature #117
//! - dependency_tracker_tests_symbol.rs: Feature #116

use simple_dependency_tracker::{
    graph::ImportGraph,
    macro_import::{
        auto_imported_macros, explicit_import, glob_import, is_auto_imported, AutoImport,
        MacroDirManifest, MacroExports, MacroSymbol, SymKind,
    },
    resolution::{resolve, well_formed, FileKind, FileSystem, ModPath, ResolutionResult},
    symbol::{ProjectSymbols, SymbolEntry, SymbolKind, SymbolTable},
    visibility::{
        ancestor_visibility, effective_visibility, visibility_meet, DirManifest, ModDecl,
        Visibility,
    },
};

include!("dependency_tracker_tests_module_resolution.rs");
include!("dependency_tracker_tests_visibility.rs");
include!("dependency_tracker_tests_macro.rs");
include!("dependency_tracker_tests_circular.rs");
include!("dependency_tracker_tests_symbol.rs");

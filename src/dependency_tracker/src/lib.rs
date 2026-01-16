//! # Simple Dependency Tracker
//!
//! This crate implements module resolution, visibility control, and macro auto-import
//! semantics for the Simple language. The implementation follows formally verified
//! Lean 4 models in `verification/`.
//!
//! ## Formal Verification Models
//!
//! - `module_resolution/` - Module path resolution (4 theorems)
//! - `visibility_export/` - Visibility and export rules (7 theorems)
//! - `macro_auto_import/` - Macro auto-import semantics (6 theorems)
//!
//! ## Key Properties (proven in Lean)
//!
//! 1. **Module Resolution**: Paths are unambiguous in well-formed filesystems
//! 2. **Visibility**: Effective visibility is intersection of item and ancestor visibility
//! 3. **Macro Import**: Glob imports only include macros listed in `auto import`

pub mod graph;
pub mod macro_import;
pub mod resolution;
pub mod symbol;
pub mod visibility;

// Re-export main types
pub use graph::{CyclicDependencyError, ImportEdge, ImportGraph};
pub use macro_import::{
    auto_imported_macros, explicit_import, glob_import, is_auto_imported, AutoImport, MacroExports, SymKind,
};
pub use resolution::{
    resolve, to_dir_path, to_file_path, well_formed, FileKind, FileSystem, ModPath, ResolutionResult, Segment,
};
pub use symbol::{SymbolEntry, SymbolKind, SymbolTable};
pub use visibility::{
    ancestor_visibility, effective_visibility, visibility_meet, DirManifest, EffectiveVisibility, ModDecl,
    ModuleContents, Symbol, SymbolId, Visibility,
};

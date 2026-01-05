//! Module system AST nodes (mod, use, export, auto import, etc.)

use crate::token::Span;
use super::super::enums::*;
use super::core::*;

//==============================================================================
// Module System (Features #104-111)
//==============================================================================

/// Module path for imports: crate.sys.http.router
#[derive(Debug, Clone, PartialEq)]
pub struct ModulePath {
    /// Path segments separated by dots: ["crate", "sys", "http", "router"]
    pub segments: Vec<String>,
}

impl ModulePath {
    pub fn new(segments: Vec<String>) -> Self {
        Self { segments }
    }
}

/// Import target: what to import from a module
#[derive(Debug, Clone, PartialEq)]
pub enum ImportTarget {
    /// Single item: use crate.core.Option
    Single(String),
    /// Aliased import: use crate.core.Option as Opt
    Aliased { name: String, alias: String },
    /// Group import: use crate.core.{Option, Result, Vec}
    Group(Vec<ImportTarget>),
    /// Glob import: use crate.core.*
    Glob,
}

/// Module declaration: mod name or pub mod name
/// #[no_gc]
/// pub mod router
#[derive(Debug, Clone, PartialEq)]
pub struct ModDecl {
    pub span: Span,
    pub name: String,
    pub visibility: Visibility,
    pub attributes: Vec<Attribute>,
}

/// Use statement: use module.path.{items}
/// use crate.core.Option
/// use crate.core.{Option, Result}
/// use crate.core.*
/// use crate.core.Option as Opt
///
/// Type-only imports (don't create runtime dependency, only for type checking):
/// use type crate.core.Option
/// use type crate.core.{Option, Result}
/// use type crate.core.*
#[derive(Debug, Clone, PartialEq)]
pub struct UseStmt {
    pub span: Span,
    pub path: ModulePath,
    pub target: ImportTarget,
    /// If true, this is a type-only import that doesn't create a runtime dependency.
    /// Type-only imports are excluded from circular dependency detection.
    /// Syntax: `use type module.Type`
    pub is_type_only: bool,
}

/// Common use statement: common use module.path.*
/// Directory prelude - applies to all files in directory
/// common use crate.core.base.*
#[derive(Debug, Clone, PartialEq)]
pub struct CommonUseStmt {
    pub span: Span,
    pub path: ModulePath,
    pub target: ImportTarget,
}

/// Export use statement: export use module.path.{items}
/// Re-export from child modules
/// export use router.Router
/// export use router.{Client, Request}
/// export use router.*
#[derive(Debug, Clone, PartialEq)]
pub struct ExportUseStmt {
    pub span: Span,
    pub path: ModulePath,
    pub target: ImportTarget,
}

/// Auto import statement: auto import module.macro_name
/// Makes macros available in glob imports
/// auto import router.route
#[derive(Debug, Clone, PartialEq)]
pub struct AutoImportStmt {
    pub span: Span,
    pub path: ModulePath,
    pub macro_name: String,
}

/// Module capability requirements statement.
///
/// Declared in `__init__.spl` to restrict what effects functions in this
/// module (and child modules) can use.
///
/// Syntax: `requires [pure, io, net]`
///
/// Example:
/// ```simple
/// # In std_lib/src/core/__init__.spl
/// requires [pure]
///
/// # All functions in core/ must be @pure
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct RequiresCapabilitiesStmt {
    pub span: Span,
    pub capabilities: Vec<Capability>,
}

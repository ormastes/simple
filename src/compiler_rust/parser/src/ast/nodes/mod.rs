//! AST node type definitions organized by category
//!
//! This module contains all AST node types split into focused submodules:
//! - `core`: Main Node enum, Decorator, Attribute, DocComment, Block, Parameter, Type, Expr, Pattern, etc.
//! - `definitions`: Function, Struct, Class, Enum, Trait, Impl, Actor, TypeAlias, Extern, Macro definitions
//! - `statements`: Let, Const, Static, Assignment, Return, If, Match, For, While, Loop, Break, Continue, Context, With
//! - `modules`: Module system nodes (ModDecl, UseStmt, CommonUseStmt, ExportUseStmt, AutoImportStmt, RequiresCapabilitiesStmt)
//! - `contracts`: Contract blocks, invariants, refinement types
//! - `effects`: Effect and Capability types for effect system
//! - `const_meta`: Compile-time metadata system for partial const support
//! - `test_meta`: Static test metadata for compile-time test analysis

// Module declarations
pub mod const_meta;
pub mod contracts;
pub mod core;
pub mod definitions;
pub mod effects;
pub mod modules;
pub mod statements;
pub mod test_meta;

// Re-export all public types from each module for convenience
pub use const_meta::*;
pub use contracts::*;
pub use core::*;
pub use definitions::*;
pub use effects::*;
pub use modules::*;
pub use statements::*;
pub use test_meta::*;

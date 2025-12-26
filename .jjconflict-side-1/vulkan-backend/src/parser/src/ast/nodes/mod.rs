//! AST node type definitions organized by category
//!
//! This module contains all AST node types split into focused submodules:
//! - `core`: Main Node enum, Decorator, Attribute, DocComment, Block, Parameter, Type, Expr, Pattern, etc.
//! - `definitions`: Function, Struct, Class, Enum, Trait, Impl, Actor, TypeAlias, Extern, Macro definitions
//! - `statements`: Let, Const, Static, Assignment, Return, If, Match, For, While, Loop, Break, Continue, Context, With
//! - `modules`: Module system nodes (ModDecl, UseStmt, CommonUseStmt, ExportUseStmt, AutoImportStmt, RequiresCapabilitiesStmt)
//! - `contracts`: Contract blocks, invariants, refinement types

// Module declarations
pub mod core;
pub mod definitions;
pub mod statements;
pub mod modules;
pub mod contracts;

// Re-export all public types from each module for convenience
pub use core::*;
pub use definitions::*;
pub use statements::*;
pub use modules::*;
pub use contracts::*;

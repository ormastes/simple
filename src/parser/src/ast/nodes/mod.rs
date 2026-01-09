//! AST node type definitions organized by category
//!
//! This module contains all AST node types split into focused submodules:
//! - `core`: Main Node enum, Decorator, Attribute, DocComment, Block, Parameter, Type, Expr, Pattern, etc.
//! - `definitions`: Function, Struct, Class, Enum, Trait, Impl, Actor, TypeAlias, Extern, Macro definitions
//! - `statements`: Let, Const, Static, Assignment, Return, If, Match, For, While, Loop, Break, Continue, Context, With
//! - `modules`: Module system nodes (ModDecl, UseStmt, CommonUseStmt, ExportUseStmt, AutoImportStmt, RequiresCapabilitiesStmt)
//! - `contracts`: Contract blocks, invariants, refinement types
//! - `effects`: Effect and Capability types for effect system

// Module declarations
pub mod contracts;
pub mod core;
pub mod definitions;
pub mod effects;
pub mod modules;
pub mod statements;

// Re-export all public types from each module for convenience
pub use contracts::*;
pub use core::*;
pub use definitions::*;
pub use effects::*;
pub use modules::*;
pub use statements::*;

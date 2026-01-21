//! Shared semantic definitions for interpreter and codegen.
//!
//! This module provides a single source of truth for language semantics
//! that must be consistent between the interpreter and compiled code.
//!
//! # Motivation
//!
//! Previously, the interpreter and codegen independently implemented:
//! - Type coercion rules
//! - Truthiness evaluation
//! - Binary/unary operation semantics
//! - Method dispatch logic
//!
//! This led to ~2,600 lines of duplicated logic. This module unifies these
//! definitions to ensure semantic consistency and reduce maintenance burden.

mod binary_ops;
pub mod cast_rules;
mod truthiness;
mod type_coercion;

pub use binary_ops::{BinaryOpResult, BinaryOpSemantics};
pub use cast_rules::{
    bool_cast, cast_bool_to_numeric, cast_float_to_numeric, cast_int_to_numeric, string_cast, CastNumericResult,
    NumericType,
};
pub use truthiness::TruthinessRules;
pub use type_coercion::{CoercionResult, TypeCoercion};

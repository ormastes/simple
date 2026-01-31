//! Unified method registry for interpreter and codegen dispatch.
//!
//! This module provides a single source of truth for built-in method dispatch,
//! eliminating semantic duplication between interpreter and codegen paths.
//!
//! # Architecture
//!
//! Both interpreter and codegen need to know:
//! 1. Which methods are available on each type
//! 2. How to call the corresponding runtime function
//! 3. Parameter and return type information
//!
//! The `MethodRegistry` centralizes this information so both paths can
//! query the same source of truth.

mod builtins;
mod registry;

pub use builtins::{ARRAY_METHODS, DICT_METHODS, STRING_METHODS, BUILTIN_METHODS};
pub use registry::{MethodRegistry, MethodInfo, RuntimeFn, GLOBAL_REGISTRY};

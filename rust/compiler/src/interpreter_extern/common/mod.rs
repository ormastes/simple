//! Common utilities for extern function implementations
//!
//! This module provides shared utilities used across all extern function
//! modules to reduce code duplication and maintain consistency:
//!
//! - **Effect checking**: Consolidated effect violation checking
//! - **Argument extraction**: Type-safe argument access with clear error messages
//! - **Error handling**: Standardized error construction

pub mod arg_extract;
pub mod effect_check;
pub mod error_utils;

// Re-export commonly used items for convenience
pub use arg_extract::{
    get_arg, get_bool, get_first, get_first_bool, get_first_int, get_first_string, get_int, get_string, require_args,
    require_at_least,
};
pub use effect_check::check_effect;
pub use error_utils::{
    deprecated_function, runtime_error, semantic_error, unknown_function, wrong_arg_count, wrong_arg_type,
};

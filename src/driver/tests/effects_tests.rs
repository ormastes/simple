//! Effect system tests (Features #401-402)
//!
//! This module tests:
//! - @pure effect - no side effects allowed
//! - @io effect - console I/O allowed
//! - @net effect - network operations allowed
//! - @fs effect - filesystem operations allowed
//! - @unsafe effect - unchecked operations allowed
//! - Stacked effects - multiple effects on one function
//!
//! Split into 4 files for better organization:
//! - effects_tests_basic.rs: Basic effect tests (@pure, @io, stacked, @fs, @net, @unsafe)
//! - effects_tests_parsing.rs: Effect and capability parsing tests
//! - effects_tests_propagation.rs: Effect propagation tests
//! - effects_tests_validation.rs: Compile-time and import capability validation

mod test_helpers;
use test_helpers::{run_expect, run_expect_compile_error};

include!("effects_tests_basic.rs");
include!("effects_tests_parsing.rs");
include!("effects_tests_propagation.rs");
include!("effects_tests_validation.rs");

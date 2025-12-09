//! Unit Tests for Simple Language Compiler
//!
//! Test Level: Unit
//! Mock Policy: All mocks allowed
//! Coverage: Branch/Condition (100% required)
//! Coverage Data: Merged with env_test
//!
//! This module re-exports and organizes unit tests from across the workspace.
//! The actual tests are in the individual crate test directories.

use ctor::ctor;
use simple_mock_helper::{init_unit_tests, validate_test_config};

#[ctor]
fn init() {
    init_unit_tests!("simple_unit");
}

// Local unit test modules for this crate
mod lexer_tests;
mod parser_tests;
mod compiler_tests;
mod loader_tests;
mod type_tests;

#[test]
fn validate_config() {
    validate_test_config().expect_pass();
}

// Note: Most unit tests are in individual crates:
// - simple-parser: 50 inline + 65 in tests/parser_tests.rs = 115 tests
// - simple-compiler: 57 inline + 22 in tests/compile_and_run.rs = 79 tests
// - simple-common: 18 inline + 11 in tests/ = 29 tests
// - simple-type: 68 in tests/inference.rs
// - simple-loader: 21 in tests/loader_tests.rs
// - simple-runtime: 19 in tests/
// - simple_mock_helper: 37 inline
//
// Run all unit tests with: cargo test --workspace
// Run only this crate's tests with: cargo test -p simple-tests --test unit

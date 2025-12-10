//! System Tests for Simple Language Compiler
//!
//! Test Level: System
//! Mock Policy: No mocks allowed
//! Coverage: Class/struct (100% required)
//! Coverage Data: Separate

use ctor::ctor;
use simple_mock_helper::{init_system_tests, validate_test_config};

#[ctor]
fn init() {
    init_system_tests!("simple_system");
}

mod cli_tests;
mod runner_tests;

#[test]
fn validate_config() {
    validate_test_config().expect_pass();
}

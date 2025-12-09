//! Environment Tests for Simple Language Compiler
//!
//! Test Level: Environment
//! Mock Policy: HAL/External/Lib mocks allowed
//! Coverage: Branch/Condition (100% required)
//! Coverage Data: Merged with unit tests

use ctor::ctor;
use simple_mock_helper::{init_env_tests, validate_test_config};

#[ctor]
fn init() {
    init_env_tests!("simple_env");
}

mod runtime_tests;
mod io_tests;

#[test]
fn validate_config() {
    validate_test_config().expect_pass();
}

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
mod core_tests;
mod coverage_tests;
mod coverage_tests2;
mod coverage_verification_tests;
mod execution_tests;
mod feature_tests_advanced;
mod feature_tests_basic;
mod integration_tests;
mod integration_tests2;
mod memory_tests;
mod runner_tests;
mod simple_basic;
mod smf_tests;
mod struct_coverage_tests;

#[test]
fn validate_config() {
    validate_test_config().expect_pass();
}

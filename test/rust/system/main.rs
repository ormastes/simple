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
mod command_dispatch_tests;
mod core_tests;
mod coverage_tests;
mod coverage_tests2;
mod coverage_verification_tests;
mod execution_tests;
mod feature_tests_advanced;
mod feature_tests_basic;
mod integration_tests;
mod integration_tests2;
mod low_coverage_tests;
mod low_coverage_tests10;
mod low_coverage_tests11;
mod low_coverage_tests12;
mod low_coverage_tests13;
mod low_coverage_tests14;
mod low_coverage_tests15;
mod low_coverage_tests16;
mod low_coverage_tests17;
mod low_coverage_tests18;
mod low_coverage_tests19;
mod low_coverage_tests2;
mod low_coverage_tests20;
mod low_coverage_tests21;
mod low_coverage_tests22;
mod low_coverage_tests23;
mod low_coverage_tests24;
mod low_coverage_tests3;
mod low_coverage_tests4;
mod low_coverage_tests5;
mod low_coverage_tests6;
mod low_coverage_tests7;
mod low_coverage_tests8;
mod low_coverage_tests9;
mod memory_tests;
mod pkg_tests;
mod public_api_coverage_tests;
mod runner_tests;
mod simple_basic;
mod smf_tests;
mod struct_coverage_tests;

#[test]
fn validate_config() {
    validate_test_config().expect_pass();
}

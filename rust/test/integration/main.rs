//! Integration Tests for Simple Language Compiler
//!
//! Test Level: Integration
//! Mock Policy: HAL-only mocks allowed
//! Coverage: Public function (100% required)
//! Coverage Data: Separate

use ctor::ctor;
use simple_mock_helper::{init_integration_tests, validate_test_config};

#[ctor]
fn init() {
    init_integration_tests!("simple_integration");
}

mod compiler_integration;
mod compiler_integration2;
mod driver_integration;

#[cfg(feature = "vulkan")]
mod vulkan_integration;

#[test]
fn validate_config() {
    validate_test_config().expect_pass();
}

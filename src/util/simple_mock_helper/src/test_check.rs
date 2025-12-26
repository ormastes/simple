//! simple_mock_helper::test_check
//!
//! Utilities for verifying test isolation levels and mock policy compliance.
//!
//! This module provides:
//! - Test level detection (unit, integration, system)
//! - Assertions for verifying correct test configuration
//! - Helpers for test binary initialization

use std::sync::atomic::{AtomicU8, Ordering};
use std::sync::RwLock;

/// Test level classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum TestLevel {
    /// Unit tests: mocks allowed everywhere
    Unit = 1,
    /// Integration tests: mocks allowed only in HAL layers
    Integration = 2,
    /// System tests: no mocks allowed
    System = 3,
    /// Environment tests: mocks allowed for HAL, external libs, and other dependencies
    Environment = 4,
}

impl TestLevel {
    /// Returns true if this test level allows any mocks.
    pub fn allows_mocks(&self) -> bool {
        matches!(
            self,
            TestLevel::Unit | TestLevel::Integration | TestLevel::Environment
        )
    }

    /// Returns true if this test level allows mocks only in HAL layers.
    pub fn hal_only(&self) -> bool {
        matches!(self, TestLevel::Integration)
    }

    /// Returns true if this test level allows mocks for HAL, external, and lib dependencies.
    pub fn env_mocks(&self) -> bool {
        matches!(self, TestLevel::Environment)
    }

    /// Returns a human-readable name for this test level.
    pub fn name(&self) -> &'static str {
        match self {
            TestLevel::Unit => "unit",
            TestLevel::Integration => "integration",
            TestLevel::System => "system",
            TestLevel::Environment => "environment",
        }
    }
}

/// Current test level (0 = uninitialized)
static TEST_LEVEL: AtomicU8 = AtomicU8::new(0);

/// Optional custom test level name for diagnostics
static TEST_LEVEL_NAME: RwLock<Option<String>> = RwLock::new(None);

/// Initialize the test level for this test binary.
///
/// This should be called once per test binary, typically via `#[ctor::ctor]`.
///
/// # Panics
/// Panics if called more than once with different levels.
pub fn init_test_level(level: TestLevel) {
    let current = TEST_LEVEL.load(Ordering::SeqCst);
    if current == 0 {
        TEST_LEVEL.store(level as u8, Ordering::SeqCst);
    } else if current != level as u8 {
        panic!(
            "Test level already initialized to {:?}, cannot change to {:?}",
            get_test_level(),
            level
        );
    }
}

/// Initialize test level with a custom name for diagnostics.
pub fn init_test_level_named(level: TestLevel, name: &str) {
    init_test_level(level);
    let mut guard = TEST_LEVEL_NAME.write().expect("lock poisoned");
    if guard.is_none() {
        *guard = Some(name.to_string());
    }
}

/// Get the current test level.
///
/// # Panics
/// Panics if test level was never initialized.
pub fn get_test_level() -> TestLevel {
    let val = TEST_LEVEL.load(Ordering::SeqCst);
    match val {
        1 => TestLevel::Unit,
        2 => TestLevel::Integration,
        3 => TestLevel::System,
        4 => TestLevel::Environment,
        _ => panic!("Test level not initialized. Call init_test_level() first."),
    }
}

/// Get the current test level, returning None if not initialized.
pub fn try_get_test_level() -> Option<TestLevel> {
    let val = TEST_LEVEL.load(Ordering::SeqCst);
    match val {
        1 => Some(TestLevel::Unit),
        2 => Some(TestLevel::Integration),
        3 => Some(TestLevel::System),
        4 => Some(TestLevel::Environment),
        _ => None,
    }
}

/// Get the custom test level name if set.
pub fn get_test_level_name() -> Option<String> {
    TEST_LEVEL_NAME
        .read()
        .expect("lock poisoned")
        .as_ref()
        .cloned()
}

/// Assert that the current test level is as expected.
///
/// # Panics
/// Panics if test level doesn't match expected.
pub fn assert_test_level(expected: TestLevel) {
    let actual = get_test_level();
    if actual != expected {
        panic!("Expected test level {:?}, but got {:?}", expected, actual);
    }
}

/// Assert that mocks are allowed at the current test level.
///
/// # Panics
/// Panics if mocks are not allowed.
pub fn assert_mocks_allowed() {
    let level = get_test_level();
    if !level.allows_mocks() {
        panic!("Mocks are not allowed at test level {:?}", level);
    }
}

/// Assert that mocks are NOT allowed at the current test level.
///
/// # Panics
/// Panics if mocks are allowed.
pub fn assert_mocks_forbidden() {
    let level = get_test_level();
    if level.allows_mocks() {
        panic!(
            "Mocks should be forbidden at test level {:?}, but they are allowed",
            level
        );
    }
}

/// Check result for test validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TestCheckResult {
    pub passed: bool,
    pub level: Option<TestLevel>,
    pub errors: Vec<String>,
}

impl TestCheckResult {
    /// Create a passing result.
    pub fn pass(level: TestLevel) -> Self {
        Self {
            passed: true,
            level: Some(level),
            errors: vec![],
        }
    }

    /// Create a failing result.
    pub fn fail(errors: Vec<String>) -> Self {
        Self {
            passed: false,
            level: try_get_test_level(),
            errors,
        }
    }

    /// Assert this result passed, panicking with errors if not.
    pub fn expect_pass(self) {
        if !self.passed {
            panic!("Test check failed:\n{}", self.errors.join("\n"));
        }
    }
}

/// Validate test binary configuration.
///
/// Checks:
/// - Test level is initialized
/// - Mock policy is consistent with test level
pub fn validate_test_config() -> TestCheckResult {
    let mut errors = vec![];

    // Check test level
    let level = match try_get_test_level() {
        Some(l) => l,
        None => {
            errors.push("Test level not initialized".to_string());
            return TestCheckResult::fail(errors);
        }
    };

    // Check mock policy consistency
    use crate::mock_policy::{are_mocks_enabled, is_policy_initialized};

    match level {
        TestLevel::Unit => {
            // Unit tests should have mocks enabled
            if !are_mocks_enabled() {
                errors.push("Unit tests should have mocks enabled".to_string());
            }
            if !is_policy_initialized() {
                errors.push("Mock policy not initialized for unit tests".to_string());
            }
        }
        TestLevel::Integration => {
            // Integration tests should have HAL-only mocks
            if !are_mocks_enabled() {
                errors.push("Integration tests should have mocks enabled (HAL-only)".to_string());
            }
            if !is_policy_initialized() {
                errors.push("Mock policy not initialized for integration tests".to_string());
            }
        }
        TestLevel::System => {
            // System tests should have mocks disabled
            if are_mocks_enabled() {
                errors.push("System tests should have mocks disabled".to_string());
            }
            if !is_policy_initialized() {
                errors.push("Mock policy not initialized for system tests".to_string());
            }
        }
        TestLevel::Environment => {
            // Environment tests should have mocks enabled for HAL/external/lib
            if !are_mocks_enabled() {
                errors.push(
                    "Environment tests should have mocks enabled (HAL/external/lib)".to_string(),
                );
            }
            if !is_policy_initialized() {
                errors.push("Mock policy not initialized for environment tests".to_string());
            }
        }
    }

    if errors.is_empty() {
        TestCheckResult::pass(level)
    } else {
        TestCheckResult::fail(errors)
    }
}

/// Helper macro to initialize unit test policy.
///
/// Call this in your test binary's `#[ctor::ctor]` function.
#[macro_export]
macro_rules! init_unit_tests {
    () => {
        $crate::test_check::init_test_level($crate::test_check::TestLevel::Unit);
        $crate::mock_policy::init_mocks_for_only(&["*"]);
    };
    ($name:expr) => {
        $crate::test_check::init_test_level_named($crate::test_check::TestLevel::Unit, $name);
        $crate::mock_policy::init_mocks_for_only(&["*"]);
    };
}

/// Helper macro to initialize integration test policy.
///
/// Call this in your test binary's `#[ctor::ctor]` function.
#[macro_export]
macro_rules! init_integration_tests {
    () => {
        $crate::test_check::init_test_level($crate::test_check::TestLevel::Integration);
        $crate::mock_policy::init_mocks_for_only_default();
    };
    ($name:expr) => {
        $crate::test_check::init_test_level_named(
            $crate::test_check::TestLevel::Integration,
            $name,
        );
        $crate::mock_policy::init_mocks_for_only_default();
    };
    (patterns: $patterns:expr) => {
        $crate::test_check::init_test_level($crate::test_check::TestLevel::Integration);
        $crate::mock_policy::init_mocks_for_only($patterns);
    };
}

/// Helper macro to initialize system test policy.
///
/// Call this in your test binary's `#[ctor::ctor]` function.
#[macro_export]
macro_rules! init_system_tests {
    () => {
        $crate::test_check::init_test_level($crate::test_check::TestLevel::System);
        $crate::mock_policy::init_mocks_for_system();
    };
    ($name:expr) => {
        $crate::test_check::init_test_level_named($crate::test_check::TestLevel::System, $name);
        $crate::mock_policy::init_mocks_for_system();
    };
}

/// Helper macro to initialize environment test policy.
///
/// Environment tests can mock HAL, external libraries, and other dependencies.
/// Call this in your test binary's `#[ctor::ctor]` function.
#[macro_export]
macro_rules! init_env_tests {
    () => {
        $crate::test_check::init_test_level($crate::test_check::TestLevel::Environment);
        $crate::mock_policy::init_mocks_for_only($crate::mock_policy::DEFAULT_ENV_PATTERNS);
    };
    ($name:expr) => {
        $crate::test_check::init_test_level_named(
            $crate::test_check::TestLevel::Environment,
            $name,
        );
        $crate::mock_policy::init_mocks_for_only($crate::mock_policy::DEFAULT_ENV_PATTERNS);
    };
    (patterns: $patterns:expr) => {
        $crate::test_check::init_test_level($crate::test_check::TestLevel::Environment);
        $crate::mock_policy::init_mocks_for_only($patterns);
    };
}

#[cfg(test)]
pub(crate) fn reset_test_level_for_tests() {
    TEST_LEVEL.store(0, Ordering::SeqCst);
    *TEST_LEVEL_NAME.write().expect("lock poisoned") = None;
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mock_policy::reset_policy_for_tests;

    fn reset() {
        reset_test_level_for_tests();
        reset_policy_for_tests();
    }

    #[test]
    fn test_level_allows_mocks() {
        assert!(TestLevel::Unit.allows_mocks());
        assert!(TestLevel::Integration.allows_mocks());
        assert!(!TestLevel::System.allows_mocks());
        assert!(TestLevel::Environment.allows_mocks());
    }

    #[test]
    fn test_level_hal_only() {
        assert!(!TestLevel::Unit.hal_only());
        assert!(TestLevel::Integration.hal_only());
        assert!(!TestLevel::System.hal_only());
        assert!(!TestLevel::Environment.hal_only());
    }

    #[test]
    fn test_level_env_mocks() {
        assert!(!TestLevel::Unit.env_mocks());
        assert!(!TestLevel::Integration.env_mocks());
        assert!(!TestLevel::System.env_mocks());
        assert!(TestLevel::Environment.env_mocks());
    }

    #[test]
    fn test_level_names() {
        assert_eq!(TestLevel::Unit.name(), "unit");
        assert_eq!(TestLevel::Integration.name(), "integration");
        assert_eq!(TestLevel::System.name(), "system");
        assert_eq!(TestLevel::Environment.name(), "environment");
    }

    #[test]
    fn test_check_result_pass() {
        let result = TestCheckResult::pass(TestLevel::Unit);
        assert!(result.passed);
        assert_eq!(result.level, Some(TestLevel::Unit));
        assert!(result.errors.is_empty());
    }

    #[test]
    fn test_check_result_fail() {
        let result = TestCheckResult::fail(vec!["error1".to_string(), "error2".to_string()]);
        assert!(!result.passed);
        assert_eq!(result.errors.len(), 2);
    }

    #[test]
    fn validate_fails_without_init_macro() {
        reset();
        let result = validate_test_config();
        assert!(!result.passed);
        assert!(result.level.is_none());
        assert!(result
            .errors
            .iter()
            .any(|e| e.contains("Test level not initialized")));
    }

    #[test]
    fn validate_unit_config_requires_policy() {
        reset();
        init_unit_tests!("unit_resettable");
        let result = validate_test_config();
        result.clone().expect_pass();
        assert_eq!(result.level, Some(TestLevel::Unit));
        assert!(crate::mock_policy::are_mocks_enabled());
        assert_eq!(crate::mock_policy::get_allowed_patterns(), Some(vec!["*"]));
        assert_eq!(get_test_level_name().as_deref(), Some("unit_resettable"));
    }

    #[test]
    fn validate_system_config_marks_policy_initialized() {
        reset();
        init_system_tests!("system_resettable");
        let result = validate_test_config();
        result.clone().expect_pass();
        assert_eq!(result.level, Some(TestLevel::System));
        assert!(!crate::mock_policy::are_mocks_enabled());
        assert!(crate::mock_policy::is_policy_initialized());
        assert_eq!(get_test_level_name().as_deref(), Some("system_resettable"));
    }
}

//! simple_mock_helper::mock_policy
//!
//! Policy-based control of when mocks are allowed.
//!
//! Typical usage per test binary:
//!   - Unit tests:    call `init_mocks_for_only(&["*"]);` (allow all).
//!   - Integration:   call `init_mocks_for_only_default();` (HAL-only).
//!   - System tests:  call `init_mocks_for_system();` (no mocks).
//!
//! Each mock wrapper calls `check_mock_use_from(module_path!())`.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{OnceLock, RwLock};

/// Result of a mock policy check (non-panicking version).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MockCheckResult {
    /// Mock usage is allowed.
    Allowed,
    /// Mocks are disabled (system test policy).
    MocksDisabled,
    /// Policy was never initialized.
    NotInitialized,
    /// Source path doesn't match any allowed pattern.
    NotAllowed { source_path: String },
}

/// Are mocks enabled in this test binary?
static MOCKS_ENABLED: AtomicBool = AtomicBool::new(false);

/// Whether the mock policy has been initialized.
static POLICY_INITIALIZED: AtomicBool = AtomicBool::new(false);

/// Allowed module patterns.
static ALLOWED_PATTERNS: OnceLock<RwLock<Vec<&'static str>>> = OnceLock::new();

/// Default patterns: allow only modules under `::hal::` and `::sub_hal::`.
pub const DEFAULT_HAL_PATTERNS: &[&str] = &["*::hal::*", "*::sub_hal::*"];

/// Default patterns for environment tests: HAL, external libs, and other dependencies.
pub const DEFAULT_ENV_PATTERNS: &[&str] = &[
    "*::hal::*",
    "*::sub_hal::*",
    "*::external::*",
    "*::lib::*",
    "*::io::*",
];

/// Enable mocks, restricting usage to modules whose `module_path!()`
/// matches at least one of `patterns`.
///
/// Pattern rules:
/// - Use `::` as module separator.
/// - `*` is a wildcard for any sequence of characters.
pub fn init_mocks_for_only(patterns: &'static [&'static str]) {
    let lock = ALLOWED_PATTERNS.get_or_init(|| RwLock::new(Vec::new()));
    let mut guard = lock.write().expect("lock poisoned");
    guard.clear();
    guard.extend_from_slice(patterns);
    MOCKS_ENABLED.store(true, Ordering::SeqCst);
    POLICY_INITIALIZED.store(true, Ordering::SeqCst);
}

/// Convenience: enable the default HAL-only policy.
pub fn init_mocks_for_only_default() {
    init_mocks_for_only(DEFAULT_HAL_PATTERNS);
}

/// Disable all mocks for this test binary.
pub fn init_mocks_for_system() {
    let lock = ALLOWED_PATTERNS.get_or_init(|| RwLock::new(Vec::new()));
    lock.write().expect("lock poisoned").clear(); // no allowed patterns when mocks are disabled
    MOCKS_ENABLED.store(false, Ordering::SeqCst);
    POLICY_INITIALIZED.store(true, Ordering::SeqCst);
}

/// Check whether a mock from `source_path` (usually `module_path!()`)
/// is allowed under the current policy.
///
/// Panics if:
/// - Mocks are disabled, or
/// - No pattern matches `source_path`, or
/// - Policy was never initialized.
pub fn check_mock_use_from(source_path: &str) {
    match try_check_mock_use_from(source_path) {
        MockCheckResult::Allowed => {}
        MockCheckResult::MocksDisabled => {
            panic!("Mock used while mocks are disabled (system test policy)");
        }
        MockCheckResult::NotInitialized => {
            panic!(
                "Mock policy not initialized. Call init_mocks_for_only*() once per test binary."
            );
        }
        MockCheckResult::NotAllowed { source_path } => {
            panic!(
                "Mock from `{}` not allowed by current mock policy",
                source_path
            );
        }
    }
}

/// Non-panicking version of `check_mock_use_from`.
///
/// Returns a `MockCheckResult` indicating whether the mock is allowed
/// and why if not.
pub fn try_check_mock_use_from(source_path: &str) -> MockCheckResult {
    if !POLICY_INITIALIZED.load(Ordering::SeqCst) {
        return MockCheckResult::NotInitialized;
    }

    if !MOCKS_ENABLED.load(Ordering::SeqCst) {
        return MockCheckResult::MocksDisabled;
    }

    let patterns = match ALLOWED_PATTERNS.get() {
        Some(lock) => lock.read().expect("lock poisoned"),
        None => return MockCheckResult::NotInitialized,
    };

    for pat in patterns.iter() {
        if pattern_matches(source_path, pat) {
            return MockCheckResult::Allowed;
        }
    }

    MockCheckResult::NotAllowed {
        source_path: source_path.to_string(),
    }
}

/// Check if mocks are currently enabled.
pub fn are_mocks_enabled() -> bool {
    MOCKS_ENABLED.load(Ordering::SeqCst)
}

/// Check if the mock policy has been initialized.
pub fn is_policy_initialized() -> bool {
    POLICY_INITIALIZED.load(Ordering::SeqCst)
}

/// Get the current allowed patterns (if initialized).
pub fn get_allowed_patterns() -> Option<Vec<&'static str>> {
    ALLOWED_PATTERNS
        .get()
        .map(|lock| lock.read().expect("lock poisoned").clone())
}

#[cfg(test)]
pub(crate) fn reset_policy_for_tests() {
    MOCKS_ENABLED.store(false, Ordering::SeqCst);
    POLICY_INITIALIZED.store(false, Ordering::SeqCst);
    if let Some(lock) = ALLOWED_PATTERNS.get() {
        lock.write().expect("lock poisoned").clear();
    }
}

/// Simple wildcard matcher:
/// - `*` → any sequence of chars.
/// - other characters literal.
/// - No normalization: expect both `path` and `pat` to use `::`.
fn pattern_matches(path: &str, pat: &str) -> bool {
    if !pat.contains('*') {
        return path.contains(pat);
    }

    let parts: Vec<&str> = pat.split('*').filter(|p| !p.is_empty()).collect();
    if parts.is_empty() {
        return true; // pattern was "*" or only "*"
    }

    let mut idx = 0;
    for part in parts {
        if let Some(off) = path[idx..].find(part) {
            idx += off + part.len();
        } else {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pattern_matches_wildcard_only() {
        assert!(pattern_matches("foo::bar::baz", "*"));
        assert!(pattern_matches("", "*"));
        assert!(pattern_matches("anything", "*"));
    }

    #[test]
    fn test_pattern_matches_hal_pattern() {
        assert!(pattern_matches("my_crate::hal::gpio", "*::hal::*"));
        assert!(pattern_matches("crate::sub_hal::spi", "*::sub_hal::*"));
        assert!(!pattern_matches("my_crate::service::foo", "*::hal::*"));
    }

    #[test]
    fn test_pattern_matches_literal() {
        assert!(pattern_matches("foo::bar::baz", "bar"));
        assert!(!pattern_matches("foo::bar::baz", "qux"));
    }

    #[test]
    fn test_pattern_matches_multiple_wildcards() {
        assert!(pattern_matches("a::b::c::d", "*::b::*::d"));
        assert!(pattern_matches("prefix::middle::suffix", "*::middle::*"));
        assert!(!pattern_matches("a::x::c::d", "*::b::*::d"));
    }

    #[test]
    fn test_pattern_matches_prefix_suffix() {
        assert!(pattern_matches("my_crate::module", "my_crate::*"));
        assert!(pattern_matches("something::module", "*::module"));
        assert!(!pattern_matches("other_crate::module", "my_crate::*"));
    }

    #[test]
    fn test_pattern_matches_exact() {
        assert!(pattern_matches("exact::match", "exact::match"));
        assert!(!pattern_matches("exact::match", "exact::other"));
    }

    #[test]
    fn test_pattern_matches_empty_pattern() {
        // Empty string pattern matches if path contains empty string (always true for contains)
        assert!(pattern_matches("foo::bar", ""));
    }

    #[test]
    fn test_pattern_matches_nested_hal() {
        assert!(pattern_matches(
            "my_app::drivers::hal::gpio::pin",
            "*::hal::*"
        ));
        assert!(pattern_matches(
            "root::sub_hal::i2c::device",
            "*::sub_hal::*"
        ));
    }

    #[test]
    fn test_mock_check_result_variants() {
        assert_eq!(MockCheckResult::Allowed, MockCheckResult::Allowed);
        assert_eq!(
            MockCheckResult::MocksDisabled,
            MockCheckResult::MocksDisabled
        );
        assert_eq!(
            MockCheckResult::NotInitialized,
            MockCheckResult::NotInitialized
        );
        assert_eq!(
            MockCheckResult::NotAllowed {
                source_path: "test".to_string()
            },
            MockCheckResult::NotAllowed {
                source_path: "test".to_string()
            }
        );
    }

    #[test]
    fn test_default_hal_patterns() {
        assert_eq!(DEFAULT_HAL_PATTERNS.len(), 2);
        assert!(DEFAULT_HAL_PATTERNS.contains(&"*::hal::*"));
        assert!(DEFAULT_HAL_PATTERNS.contains(&"*::sub_hal::*"));
    }

    #[test]
    fn test_default_env_patterns() {
        assert_eq!(DEFAULT_ENV_PATTERNS.len(), 5);
        assert!(DEFAULT_ENV_PATTERNS.contains(&"*::hal::*"));
        assert!(DEFAULT_ENV_PATTERNS.contains(&"*::sub_hal::*"));
        assert!(DEFAULT_ENV_PATTERNS.contains(&"*::external::*"));
        assert!(DEFAULT_ENV_PATTERNS.contains(&"*::lib::*"));
        assert!(DEFAULT_ENV_PATTERNS.contains(&"*::io::*"));
    }

    #[test]
    fn test_env_patterns_match() {
        // HAL patterns
        assert!(pattern_matches("my_crate::hal::gpio", "*::hal::*"));
        assert!(pattern_matches("my_crate::sub_hal::spi", "*::sub_hal::*"));
        // External lib patterns
        assert!(pattern_matches(
            "my_crate::external::http",
            "*::external::*"
        ));
        // Lib patterns
        assert!(pattern_matches("my_crate::lib::utils", "*::lib::*"));
        // IO patterns
        assert!(pattern_matches("my_crate::io::filesystem", "*::io::*"));
        // Negative cases
        assert!(!pattern_matches("my_crate::service::foo", "*::external::*"));
    }

    #[test]
    fn try_check_requires_initialization() {
        reset_policy_for_tests();
        let result = try_check_mock_use_from("my_crate::hal::spi");
        assert_eq!(result, MockCheckResult::NotInitialized);
    }

    #[test]
    fn init_system_marks_policy_initialized() {
        reset_policy_for_tests();
        init_mocks_for_system();
        assert!(is_policy_initialized());
        assert_eq!(
            try_check_mock_use_from("any::path"),
            MockCheckResult::MocksDisabled
        );
    }
}

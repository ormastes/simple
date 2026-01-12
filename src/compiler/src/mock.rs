//! Mock system for testing using unified predicates.
//!
//! This module provides test-time mocking capabilities using the same
//! predicate system as AOP and DI. Mocks are only available in test context.
//!
//! See doc/research/aop.md section 9 for the complete specification.

use crate::predicate::{MatchContext, Predicate, PredicateContext};
use std::collections::HashMap;

/// Mock behavior specification
#[derive(Debug, Clone)]
pub enum MockBehavior {
    /// Return a constant value
    ReturnValue(String),
    /// Throw an error
    ThrowError(String),
    /// Call another function
    Delegate(String),
    /// Execute custom code
    Custom(String),
}

/// A mock rule for replacing function behavior in tests
#[derive(Debug, Clone)]
pub struct MockRule {
    /// Predicate to match functions/methods
    pub predicate: Predicate,
    /// Mock behavior to apply
    pub behavior: MockBehavior,
    /// Priority for resolution (higher wins)
    pub priority: i64,
    /// Whether this mock is verified (must be called)
    pub verify: bool,
    /// Raw predicate text for debugging
    pub raw_predicate: String,
}

/// Mock configuration for a test
#[derive(Debug, Clone)]
pub struct MockConfig {
    /// Whether mocking is enabled
    pub enabled: bool,
    /// Mock rules to apply
    pub rules: Vec<MockRule>,
    /// Profile context (must be "test")
    pub profile: String,
}

impl MockConfig {
    /// Create an empty configuration (mocking disabled)
    pub fn disabled() -> Self {
        Self {
            enabled: false,
            rules: Vec::new(),
            profile: "test".to_string(),
        }
    }

    /// Create a configuration for testing
    pub fn for_test(rules: Vec<MockRule>) -> Self {
        Self {
            enabled: !rules.is_empty(),
            rules,
            profile: "test".to_string(),
        }
    }

    /// Validate that this config is only used in test context
    pub fn validate(&self) -> Result<(), String> {
        if self.enabled && self.profile != "test" {
            return Err(format!(
                "Mock configuration can only be used in test profile, got '{}'",
                self.profile
            ));
        }
        Ok(())
    }
}

/// Matched mock for a function
#[derive(Debug, Clone)]
pub struct MatchedMock {
    pub behavior: MockBehavior,
    pub priority: i64,
    pub verify: bool,
    pub raw_predicate: String,
}

/// Mock invocation record for verification
#[derive(Debug, Clone)]
pub struct MockInvocation {
    pub function_name: String,
    pub args: Vec<String>,
    pub timestamp: std::time::SystemTime,
}

/// Mock registry for tracking calls and verification
pub struct MockRegistry {
    config: MockConfig,
    invocations: HashMap<String, Vec<MockInvocation>>,
}

impl MockRegistry {
    /// Create a new registry with the given configuration
    pub fn new(config: MockConfig) -> Result<Self, String> {
        config.validate()?;
        Ok(Self {
            config,
            invocations: HashMap::new(),
        })
    }

    /// Match a mock rule to a function/method
    pub fn match_mock(&self, function_name: &str, module_path: &str) -> Option<MatchedMock> {
        if !self.config.enabled {
            return None;
        }

        let ctx = MatchContext::new()
            .with_type_name(function_name)
            .with_module_path(module_path);

        let mut matched = Vec::new();

        for rule in &self.config.rules {
            if rule.predicate.validate(PredicateContext::Mock).is_ok()
                && rule.predicate.matches(&ctx)
            {
                matched.push((rule.priority, rule));
            }
        }

        if matched.is_empty() {
            return None;
        }

        // Sort by priority (higher first)
        matched.sort_by(|a, b| b.0.cmp(&a.0));

        let (_, winning_rule) = matched[0];
        Some(MatchedMock {
            behavior: winning_rule.behavior.clone(),
            priority: winning_rule.priority,
            verify: winning_rule.verify,
            raw_predicate: winning_rule.raw_predicate.clone(),
        })
    }

    /// Record a mock invocation
    pub fn record_invocation(&mut self, function_name: String, args: Vec<String>) {
        let invocation = MockInvocation {
            function_name: function_name.clone(),
            args,
            timestamp: std::time::SystemTime::now(),
        };

        self.invocations
            .entry(function_name)
            .or_insert_with(Vec::new)
            .push(invocation);
    }

    /// Verify that all mocks with verify=true were called
    pub fn verify_all(&self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();

        for rule in &self.config.rules {
            if rule.verify {
                // Check if any invocations match this rule
                let has_invocation = self.invocations.iter().any(|(func_name, _)| {
                    let ctx = MatchContext::new().with_type_name(func_name);
                    rule.predicate.matches(&ctx)
                });

                if !has_invocation {
                    errors.push(format!(
                        "Mock rule '{}' was never called (verify=true)",
                        rule.raw_predicate
                    ));
                }
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Get invocation count for a function
    pub fn invocation_count(&self, function_name: &str) -> usize {
        self.invocations
            .get(function_name)
            .map(|v| v.len())
            .unwrap_or(0)
    }

    /// Get all invocations for a function
    pub fn get_invocations(&self, function_name: &str) -> &[MockInvocation] {
        self.invocations
            .get(function_name)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Reset all invocation records
    pub fn reset(&mut self) {
        self.invocations.clear();
    }
}

/// Parse mock configuration from SDN-like format
///
/// NOTE: Currently returns disabled configuration. Mock rules are defined
/// programmatically via MockConfig::with_rules() or loaded from test metadata.
/// SDN file-based configuration will be implemented when needed for external
/// test configuration files.
pub fn parse_mock_config(config_str: &str) -> Result<MockConfig, String> {
    let _ = config_str;
    Ok(MockConfig::disabled())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicate_parser::parse_predicate;

    #[test]
    fn test_mock_config_validation() {
        let config = MockConfig {
            enabled: true,
            rules: vec![],
            profile: "production".to_string(),
        };

        let result = config.validate();
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .contains("can only be used in test profile"));
    }

    #[test]
    fn test_mock_config_test_profile() {
        let config = MockConfig {
            enabled: true,
            rules: vec![],
            profile: "test".to_string(),
        };

        let result = config.validate();
        assert!(result.is_ok());
    }

    #[test]
    fn test_match_mock_by_function_name() {
        let predicate = parse_predicate("pc{ init(database_connect) }").unwrap();

        let rule = MockRule {
            predicate,
            behavior: MockBehavior::ReturnValue("mock_connection".to_string()),
            priority: 10,
            verify: false,
            raw_predicate: "pc{ init(database_connect) }".to_string(),
        };

        let config = MockConfig::for_test(vec![rule]);
        let registry = MockRegistry::new(config).unwrap();

        // Should match database_connect
        let matched = registry.match_mock("database_connect", "app.db");
        assert!(matched.is_some());
        let m = matched.unwrap();
        assert_eq!(m.priority, 10);

        // Should not match other functions
        let not_matched = registry.match_mock("other_function", "app.db");
        assert!(not_matched.is_none());
    }

    #[test]
    fn test_match_mock_by_module_path() {
        let predicate = parse_predicate("pc{ within(app.external.**) }").unwrap();

        let rule = MockRule {
            predicate,
            behavior: MockBehavior::ThrowError("Network unavailable".to_string()),
            priority: 10,
            verify: false,
            raw_predicate: "pc{ within(app.external.**) }".to_string(),
        };

        let config = MockConfig::for_test(vec![rule]);
        let registry = MockRegistry::new(config).unwrap();

        // Should match functions in app.external
        let matched = registry.match_mock("fetch_data", "app.external.api");
        assert!(matched.is_some());

        // Should not match functions in other modules
        let not_matched = registry.match_mock("fetch_data", "app.internal.api");
        assert!(not_matched.is_none());
    }

    #[test]
    fn test_mock_priority_resolution() {
        let pred1 = parse_predicate("pc{ init(*) }").unwrap();
        let pred2 = parse_predicate("pc{ init(test_*) }").unwrap();

        let rule1 = MockRule {
            predicate: pred1,
            behavior: MockBehavior::ReturnValue("generic".to_string()),
            priority: 5,
            verify: false,
            raw_predicate: "pc{ init(*) }".to_string(),
        };

        let rule2 = MockRule {
            predicate: pred2,
            behavior: MockBehavior::ReturnValue("specific".to_string()),
            priority: 10,
            verify: false,
            raw_predicate: "pc{ init(test_*) }".to_string(),
        };

        let config = MockConfig::for_test(vec![rule1, rule2]);
        let registry = MockRegistry::new(config).unwrap();

        // Should match higher priority rule
        let matched = registry.match_mock("test_function", "app.test");
        assert!(matched.is_some());
        let m = matched.unwrap();
        assert_eq!(m.priority, 10);
        match m.behavior {
            MockBehavior::ReturnValue(v) => assert_eq!(v, "specific"),
            _ => panic!("Expected ReturnValue"),
        }
    }

    #[test]
    fn test_invocation_recording() {
        let config = MockConfig::for_test(vec![]);
        let mut registry = MockRegistry::new(config).unwrap();

        registry.record_invocation("test_fn".to_string(), vec!["arg1".to_string()]);
        registry.record_invocation("test_fn".to_string(), vec!["arg2".to_string()]);
        registry.record_invocation("other_fn".to_string(), vec![]);

        assert_eq!(registry.invocation_count("test_fn"), 2);
        assert_eq!(registry.invocation_count("other_fn"), 1);
        assert_eq!(registry.invocation_count("missing_fn"), 0);

        let invocations = registry.get_invocations("test_fn");
        assert_eq!(invocations.len(), 2);
        assert_eq!(invocations[0].args[0], "arg1");
        assert_eq!(invocations[1].args[0], "arg2");
    }

    #[test]
    fn test_mock_verification() {
        let pred1 = parse_predicate("pc{ init(must_be_called) }").unwrap();
        let pred2 = parse_predicate("pc{ init(optional) }").unwrap();

        let rule1 = MockRule {
            predicate: pred1,
            behavior: MockBehavior::ReturnValue("value".to_string()),
            priority: 10,
            verify: true, // Must be called
            raw_predicate: "pc{ init(must_be_called) }".to_string(),
        };

        let rule2 = MockRule {
            predicate: pred2,
            behavior: MockBehavior::ReturnValue("value".to_string()),
            priority: 10,
            verify: false, // Optional
            raw_predicate: "pc{ init(optional) }".to_string(),
        };

        let config = MockConfig::for_test(vec![rule1, rule2]);
        let mut registry = MockRegistry::new(config).unwrap();

        // Verify fails because must_be_called wasn't invoked
        let result = registry.verify_all();
        assert!(result.is_err());
        let errors = result.unwrap_err();
        assert_eq!(errors.len(), 1);
        assert!(errors[0].contains("must_be_called"));

        // Record the invocation
        registry.record_invocation("must_be_called".to_string(), vec![]);

        // Now verify should pass
        let result = registry.verify_all();
        assert!(result.is_ok());
    }

    #[test]
    fn test_reset_invocations() {
        let config = MockConfig::for_test(vec![]);
        let mut registry = MockRegistry::new(config).unwrap();

        registry.record_invocation("test_fn".to_string(), vec![]);
        assert_eq!(registry.invocation_count("test_fn"), 1);

        registry.reset();
        assert_eq!(registry.invocation_count("test_fn"), 0);
    }
}

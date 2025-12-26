//! Fluent/chainable API for mock setup and verification
//!
//! This module provides a builder-style API for configuring mocks and verifying
//! their behavior, inspired by RSpec, Mockito, and modern mocking frameworks.
//!
//! # Examples
//!
//! ```rust
//! use simple_mock_helper::fluent::{MockSetup, MockVerify};
//!
//! // Setup mock behavior
//! let mut setup = MockSetup::new("UserDao");
//! setup
//!     .when("findById")
//!     .with_args(&[123])
//!     .returns("User(id: 123)")
//!     .times(1);
//!
//! // Verify mock calls
//! let mut verify = MockVerify::new("UserDao");
//! verify
//!     .method("findById")
//!     .was_called()
//!     .with_args(&[123])
//!     .times(1);
//! ```

use std::fmt;

/// Represents an argument matcher for flexible mock setup
#[derive(Debug, Clone, PartialEq)]
pub enum ArgMatcher {
    /// Match any value
    Any,
    /// Match exact value
    Exact(String),
    /// Match value greater than
    GreaterThan(i64),
    /// Match value less than
    LessThan(i64),
    /// Match value in range
    Range(i64, i64),
    /// Match using regex pattern
    Pattern(String),
    /// Custom predicate matcher
    Predicate(String),
}

impl fmt::Display for ArgMatcher {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ArgMatcher::Any => write!(f, "any()"),
            ArgMatcher::Exact(v) => write!(f, "{}", v),
            ArgMatcher::GreaterThan(n) => write!(f, "gt({})", n),
            ArgMatcher::LessThan(n) => write!(f, "lt({})", n),
            ArgMatcher::Range(min, max) => write!(f, "range({}, {})", min, max),
            ArgMatcher::Pattern(p) => write!(f, "pattern(\"{}\")", p),
            ArgMatcher::Predicate(desc) => write!(f, "predicate({})", desc),
        }
    }
}

/// Fluent builder for mock method setup
#[derive(Debug, Clone)]
pub struct MethodSetup {
    mock_name: String,
    method_name: String,
    method_chain: Vec<String>,
    args: Vec<ArgMatcher>,
    return_value: Option<String>,
    return_values: Vec<String>,
    side_effects: Vec<String>,
    call_count: Option<usize>,
    throws: Option<String>,
}

impl MethodSetup {
    /// Create a new method setup for the given mock and method
    pub fn new(mock_name: impl Into<String>, method_name: impl Into<String>) -> Self {
        Self {
            mock_name: mock_name.into(),
            method_name: method_name.into(),
            method_chain: Vec::new(),
            args: Vec::new(),
            return_value: None,
            return_values: Vec::new(),
            side_effects: Vec::new(),
            call_count: None,
            throws: None,
        }
    }

    /// Match any arguments
    pub fn with_any_args(&mut self) -> &mut Self {
        self.args.push(ArgMatcher::Any);
        self
    }

    /// Chain another method call (for deep call chains)
    /// 
    /// Example: `setup.when("getLibrary").chain("getHead").chain("getName").returns("Jane")`
    pub fn chain(&mut self, method: impl Into<String>) -> &mut Self {
        self.method_chain.push(method.into());
        self
    }

    /// Match specific arguments
    pub fn with_args(&mut self, args: &[impl ToString]) -> &mut Self {
        self.args.extend(
            args.iter()
                .map(|a| ArgMatcher::Exact(a.to_string()))
        );
        self
    }

    /// Match arguments using matchers
    pub fn with_matchers(&mut self, matchers: Vec<ArgMatcher>) -> &mut Self {
        self.args.extend(matchers);
        self
    }

    /// Set return value for all calls
    pub fn returns(&mut self, value: impl Into<String>) -> &mut Self {
        self.return_value = Some(value.into());
        self
    }

    /// Set return value for next call only
    pub fn returns_once(&mut self, value: impl Into<String>) -> &mut Self {
        self.return_values.push(value.into());
        self
    }

    /// Set multiple return values in sequence
    pub fn returns_seq(&mut self, values: Vec<impl Into<String>>) -> &mut Self {
        self.return_values.extend(values.into_iter().map(|v| v.into()));
        self
    }

    /// Add side effect to execute on call
    pub fn does(&mut self, effect: impl Into<String>) -> &mut Self {
        self.side_effects.push(effect.into());
        self
    }

    /// Expect specific number of calls
    pub fn times(&mut self, count: usize) -> &mut Self {
        self.call_count = Some(count);
        self
    }

    /// Expect at least one call
    pub fn at_least_once(&mut self) -> &mut Self {
        self.call_count = Some(1);
        self
    }

    /// Make the method throw an exception
    pub fn throws(&mut self, error: impl Into<String>) -> &mut Self {
        self.throws = Some(error.into());
        self
    }

    /// Get the mock name
    pub fn mock_name(&self) -> &str {
        &self.mock_name
    }

    /// Get the method name
    pub fn method_name(&self) -> &str {
        &self.method_name
    }

    /// Get the method chain (for deep call chains)
    pub fn method_chain(&self) -> &[String] {
        &self.method_chain
    }

    /// Get the full method path including chain
    pub fn full_method_path(&self) -> String {
        let mut path = self.method_name.clone();
        for method in &self.method_chain {
            path.push_str("().");
            path.push_str(method);
        }
        path
    }

    /// Get the argument matchers
    pub fn matchers(&self) -> &[ArgMatcher] {
        &self.args
    }

    /// Get the return value
    pub fn return_value(&self) -> Option<&str> {
        self.return_value.as_deref()
    }

    /// Get the sequential return values
    pub fn return_values(&self) -> &[String] {
        &self.return_values
    }

    /// Get expected call count
    pub fn expected_calls(&self) -> Option<usize> {
        self.call_count
    }

    /// Get exception to throw
    pub fn exception(&self) -> Option<&str> {
        self.throws.as_deref()
    }
}

impl fmt::Display for MethodSetup {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}::{}", self.mock_name, self.method_name)?;
        
        // Show method chain if present
        for method in &self.method_chain {
            write!(f, "().{}", method)?;
        }
        
        if !self.args.is_empty() {
            write!(f, "(")?;
            for (i, arg) in self.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
            write!(f, ")")?;
        }
        if let Some(ret) = &self.return_value {
            write!(f, " -> {}", ret)?;
        }
        if !self.return_values.is_empty() {
            write!(f, " -> [")?;
            for (i, val) in self.return_values.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", val)?;
            }
            write!(f, "]")?;
        }
        if let Some(count) = self.call_count {
            write!(f, " (expect {} calls)", count)?;
        }
        Ok(())
    }
}

/// Fluent builder for mock setup
#[derive(Debug, Clone)]
pub struct MockSetup {
    mock_name: String,
    setups: Vec<MethodSetup>,
}

impl MockSetup {
    /// Create a new mock setup
    pub fn new(mock_name: impl Into<String>) -> Self {
        Self {
            mock_name: mock_name.into(),
            setups: Vec::new(),
        }
    }

    /// Start configuring a method
    pub fn when(&mut self, method_name: impl Into<String>) -> &mut MethodSetup {
        let setup = MethodSetup::new(self.mock_name.clone(), method_name);
        self.setups.push(setup);
        self.setups.last_mut().unwrap()
    }

    /// Get all method setups
    pub fn setups(&self) -> &[MethodSetup] {
        &self.setups
    }

    /// Clear all setups
    pub fn clear(&mut self) {
        self.setups.clear();
    }

    /// Get the mock name
    pub fn mock_name(&self) -> &str {
        &self.mock_name
    }
}

/// Fluent builder for mock verification
#[derive(Debug, Clone)]
pub struct MethodVerification {
    mock_name: String,
    method_name: String,
    expected_args: Vec<ArgMatcher>,
    expected_calls: Option<VerifyCount>,
    actual_calls: usize,
    verified: bool,
}

/// Call count verification
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerifyCount {
    /// Exactly n times
    Exactly(usize),
    /// At least n times
    AtLeast(usize),
    /// At most n times
    AtMost(usize),
    /// Never called
    Never,
    /// Called any number of times
    Any,
}

impl VerifyCount {
    /// Check if the actual count matches the expectation
    pub fn matches(&self, actual: usize) -> bool {
        match self {
            VerifyCount::Exactly(n) => actual == *n,
            VerifyCount::AtLeast(n) => actual >= *n,
            VerifyCount::AtMost(n) => actual <= *n,
            VerifyCount::Never => actual == 0,
            VerifyCount::Any => true,
        }
    }
}

impl fmt::Display for VerifyCount {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VerifyCount::Exactly(n) => write!(f, "exactly {} time(s)", n),
            VerifyCount::AtLeast(n) => write!(f, "at least {} time(s)", n),
            VerifyCount::AtMost(n) => write!(f, "at most {} time(s)", n),
            VerifyCount::Never => write!(f, "never"),
            VerifyCount::Any => write!(f, "any number of times"),
        }
    }
}

impl MethodVerification {
    /// Create a new method verification
    pub fn new(mock_name: impl Into<String>, method_name: impl Into<String>) -> Self {
        Self {
            mock_name: mock_name.into(),
            method_name: method_name.into(),
            expected_args: Vec::new(),
            expected_calls: None,
            actual_calls: 0,
            verified: false,
        }
    }

    /// Verify the method was called
    pub fn was_called(&mut self) -> &mut Self {
        self.expected_calls = Some(VerifyCount::AtLeast(1));
        self
    }

    /// Verify the method was never called
    pub fn was_not_called(&mut self) -> &mut Self {
        self.expected_calls = Some(VerifyCount::Never);
        self
    }

    /// Verify exact number of calls
    pub fn times(&mut self, count: usize) -> &mut Self {
        self.expected_calls = Some(VerifyCount::Exactly(count));
        self
    }

    /// Verify at least n calls
    pub fn at_least(&mut self, count: usize) -> &mut Self {
        self.expected_calls = Some(VerifyCount::AtLeast(count));
        self
    }

    /// Verify at most n calls
    pub fn at_most(&mut self, count: usize) -> &mut Self {
        self.expected_calls = Some(VerifyCount::AtMost(count));
        self
    }

    /// Verify called once
    pub fn once(&mut self) -> &mut Self {
        self.expected_calls = Some(VerifyCount::Exactly(1));
        self
    }

    /// Verify with specific arguments
    pub fn with_args(&mut self, args: &[impl ToString]) -> &mut Self {
        self.expected_args.extend(
            args.iter()
                .map(|a| ArgMatcher::Exact(a.to_string()))
        );
        self
    }

    /// Verify with argument matchers
    pub fn with_matchers(&mut self, matchers: Vec<ArgMatcher>) -> &mut Self {
        self.expected_args.extend(matchers);
        self
    }

    /// Set actual call count (used by mock framework)
    pub fn set_actual_calls(&mut self, count: usize) {
        self.actual_calls = count;
    }

    /// Perform verification
    pub fn verify(&mut self) -> Result<(), String> {
        if self.verified {
            return Ok(());
        }

        if let Some(expected) = self.expected_calls {
            if !expected.matches(self.actual_calls) {
                return Err(format!(
                    "{}::{}: expected {} but was called {} time(s)",
                    self.mock_name, self.method_name, expected, self.actual_calls
                ));
            }
        }

        self.verified = true;
        Ok(())
    }

    /// Check if verification passed
    pub fn is_verified(&self) -> bool {
        self.verified
    }

    /// Get the mock name
    pub fn mock_name(&self) -> &str {
        &self.mock_name
    }

    /// Get the method name
    pub fn method_name(&self) -> &str {
        &self.method_name
    }

    /// Get expected arguments
    pub fn expected_args(&self) -> &[ArgMatcher] {
        &self.expected_args
    }

    /// Get actual call count
    pub fn actual_calls(&self) -> usize {
        self.actual_calls
    }
}

impl fmt::Display for MethodVerification {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}::{}", self.mock_name, self.method_name)?;
        if !self.expected_args.is_empty() {
            write!(f, "(")?;
            for (i, arg) in self.expected_args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
            write!(f, ")")?;
        }
        if let Some(count) = self.expected_calls {
            write!(f, " called {}", count)?;
        }
        write!(f, " (actual: {} calls)", self.actual_calls)?;
        Ok(())
    }
}

/// Fluent builder for mock verification
#[derive(Debug, Clone)]
pub struct MockVerify {
    mock_name: String,
    verifications: Vec<MethodVerification>,
}

impl MockVerify {
    /// Create a new mock verification
    pub fn new(mock_name: impl Into<String>) -> Self {
        Self {
            mock_name: mock_name.into(),
            verifications: Vec::new(),
        }
    }

    /// Start verifying a method
    pub fn method(&mut self, method_name: impl Into<String>) -> &mut MethodVerification {
        let verify = MethodVerification::new(self.mock_name.clone(), method_name);
        self.verifications.push(verify);
        self.verifications.last_mut().unwrap()
    }

    /// Get all verifications
    pub fn verifications(&self) -> &[MethodVerification] {
        &self.verifications
    }

    /// Get mutable access to verifications
    pub fn verifications_mut(&mut self) -> &mut [MethodVerification] {
        &mut self.verifications
    }

    /// Verify all expectations
    pub fn verify_all(&mut self) -> Result<(), Vec<String>> {
        let mut errors = Vec::new();

        for verification in &mut self.verifications {
            if let Err(err) = verification.verify() {
                errors.push(err);
            }
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Clear all verifications
    pub fn clear(&mut self) {
        self.verifications.clear();
    }

    /// Get the mock name
    pub fn mock_name(&self) -> &str {
        &self.mock_name
    }
}

/// Spy wrapper that records calls for verification
#[derive(Debug, Clone)]
pub struct Spy {
    name: String,
    calls: Vec<(String, Vec<String>)>,
}

impl Spy {
    /// Create a new spy
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            calls: Vec::new(),
        }
    }

    /// Record a method call
    pub fn record(&mut self, method: impl Into<String>, args: Vec<impl Into<String>>) {
        self.calls.push((
            method.into(),
            args.into_iter().map(|a| a.into()).collect(),
        ));
    }

    /// Get number of calls to a method
    pub fn call_count(&self, method: &str) -> usize {
        self.calls
            .iter()
            .filter(|(m, _)| m == method)
            .count()
    }

    /// Get all calls to a method
    pub fn get_calls(&self, method: &str) -> Vec<&Vec<String>> {
        self.calls
            .iter()
            .filter_map(|(m, args)| if m == method { Some(args) } else { None })
            .collect()
    }

    /// Get all recorded calls
    pub fn all_calls(&self) -> &[(String, Vec<String>)] {
        &self.calls
    }

    /// Clear recorded calls
    pub fn clear(&mut self) {
        self.calls.clear();
    }

    /// Get spy name
    pub fn name(&self) -> &str {
        &self.name
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_method_setup_builder() {
        let mut setup = MethodSetup::new("UserDao", "findById");
        setup.with_args(&[123]).returns("User(id: 123)").times(1);

        assert_eq!(setup.mock_name(), "UserDao");
        assert_eq!(setup.method_name(), "findById");
        assert_eq!(setup.return_value(), Some("User(id: 123)"));
        assert_eq!(setup.expected_calls(), Some(1));
    }

    #[test]
    fn test_mock_setup_fluent() {
        let mut setup = MockSetup::new("UserDao");
        setup.when("findById").with_args(&[123]).returns("User(id: 123)");
        setup.when("save").with_any_args().returns("true");

        assert_eq!(setup.setups().len(), 2);
        assert_eq!(setup.setups()[0].method_name(), "findById");
        assert_eq!(setup.setups()[1].method_name(), "save");
    }

    #[test]
    fn test_method_verification_builder() {
        let mut verify = MethodVerification::new("UserDao", "findById");
        verify.was_called().with_args(&[123]).times(1);

        verify.set_actual_calls(1);
        assert!(verify.verify().is_ok());
        assert!(verify.is_verified());
    }

    #[test]
    fn test_verification_failure() {
        let mut verify = MethodVerification::new("UserDao", "findById");
        verify.times(2);

        verify.set_actual_calls(1);
        assert!(verify.verify().is_err());
    }

    #[test]
    fn test_spy_recording() {
        let mut spy = Spy::new("UserService");
        spy.record("createUser", vec!["Alice"]);
        spy.record("createUser", vec!["Bob"]);
        spy.record("deleteUser", vec!["Alice"]);

        assert_eq!(spy.call_count("createUser"), 2);
        assert_eq!(spy.call_count("deleteUser"), 1);
        assert_eq!(spy.get_calls("createUser").len(), 2);
    }

    #[test]
    fn test_arg_matchers() {
        let matchers = vec![
            ArgMatcher::Any,
            ArgMatcher::GreaterThan(10),
            ArgMatcher::Pattern("user.*".to_string()),
        ];

        let mut setup = MethodSetup::new("Service", "process");
        setup.with_matchers(matchers);

        assert_eq!(setup.matchers().len(), 3);
    }

    #[test]
    fn test_verify_count() {
        assert!(VerifyCount::Exactly(2).matches(2));
        assert!(!VerifyCount::Exactly(2).matches(3));
        assert!(VerifyCount::AtLeast(2).matches(3));
        assert!(!VerifyCount::AtLeast(2).matches(1));
        assert!(VerifyCount::AtMost(2).matches(1));
        assert!(!VerifyCount::AtMost(2).matches(3));
        assert!(VerifyCount::Never.matches(0));
        assert!(!VerifyCount::Never.matches(1));
        assert!(VerifyCount::Any.matches(42));
    }

    #[test]
    fn test_returns_sequence() {
        let mut setup = MethodSetup::new("Counter", "next");
        setup.returns_seq(vec!["1", "2", "3"]);

        assert_eq!(setup.return_values().len(), 3);
        assert_eq!(setup.return_values()[0], "1");
        assert_eq!(setup.return_values()[2], "3");
    }

    #[test]
    fn test_display_formatting() {
        let mut setup = MethodSetup::new("UserDao", "findById");
        setup.with_args(&[123]).returns("User");

        let display = format!("{}", setup);
        assert!(display.contains("UserDao::findById"));
        assert!(display.contains("123"));
        assert!(display.contains("User"));
    }

    #[test]
    fn test_deep_call_chain() {
        let mut setup = MethodSetup::new("Library", "getHeadLibrarian");
        setup.chain("getName").returns("Jane");

        assert_eq!(setup.method_chain().len(), 1);
        assert_eq!(setup.method_chain()[0], "getName");
        assert_eq!(setup.full_method_path(), "getHeadLibrarian().getName");
    }

    #[test]
    fn test_multiple_chain_calls() {
        let mut setup = MethodSetup::new("Company", "getDepartment");
        setup.chain("getManager")
            .chain("getName")
            .with_args(&["Engineering"])
            .returns("Alice");

        assert_eq!(setup.method_chain().len(), 2);
        assert_eq!(setup.full_method_path(), "getDepartment().getManager().getName");
        
        let display = format!("{}", setup);
        assert!(display.contains("getDepartment().getManager().getName"));
    }

    #[test]
    fn test_chain_with_args_and_returns() {
        let mut setup = MethodSetup::new("API", "getEndpoint");
        setup.chain("getHandler")
            .chain("execute")
            .with_args(&["POST", "/api/users"])
            .returns("200 OK");

        assert_eq!(setup.method_chain().len(), 2);
        assert_eq!(setup.return_value(), Some("200 OK"));
    }
}

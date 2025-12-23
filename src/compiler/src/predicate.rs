//! Unified predicate system for AOP, DI, mocking, and architecture rules.
//!
//! This module provides a single predicate expression language that is reused across:
//! - AOP weaving (compile-time, link-time, runtime)
//! - DI binding selection (hybrid DI)
//! - Test mocking selection (test-only)
//! - Architecture rules (static dependency validation)
//!
//! See doc/research/aop.md for the complete specification.

use std::fmt;

/// Predicate context determines which selectors are valid.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PredicateContext {
    /// AOP weaving context - supports execution, within, attr, effect, test, decision, condition, call
    Weaving,
    /// DI binding context - supports type, within, attr
    DependencyInjection,
    /// Mock selection context - supports type, within, attr (test-only)
    Mock,
    /// Architecture rules context - supports import, depend, use, export, config, within, attr
    Architecture,
}

/// Selector types for predicates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Selector {
    // ===== Weaving selectors =====
    /// Matches function execution by signature pattern
    Execution(SignaturePattern),
    /// Matches code within a module/package pattern
    Within(String),
    /// Matches declarations with specific attribute
    Attr(String),
    /// Matches code with specific effect set
    Effect(String),
    /// Matches test functions by name pattern
    Test(String),
    /// Matches decision points (compiler-defined)
    Decision,
    /// Matches condition points (compiler-defined)
    Condition,
    /// Matches function calls by signature pattern (link-time)
    Call(SignaturePattern),

    // ===== DI selectors =====
    /// Matches types by pattern (DI-specific)
    Type(String),

    // ===== AOP runtime selectors =====
    /// Matches object initialization (runtime-only)
    Init(String),

    // ===== Architecture selectors =====
    /// Matches import dependencies
    Import { from: String, to: String },
    /// Matches general dependencies
    Depend { from: String, to: String },
    /// Matches usage of specific types/modules
    Use(String),
    /// Matches exported symbols
    Export(String),
    /// Matches configuration keys
    Config(String),
}

/// Signature pattern for matching function signatures.
///
/// Format: `ret_pat qname_pat(arg_pats)`
/// Example: `* User.new(..)`, `i64 *.calculate(i64, i64)`
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignaturePattern {
    /// Return type pattern (* matches any)
    pub return_type: String,
    /// Qualified name pattern (e.g., User.new, *.calculate)
    pub qualified_name: String,
    /// Argument patterns (.. matches any, or specific patterns)
    pub args: ArgPatterns,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ArgPatterns {
    /// Match any arguments (..)
    Any,
    /// Match specific argument patterns
    Specific(Vec<String>),
}

/// Predicate expression with boolean combinators.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Predicate {
    Selector(Selector),
    Not(Box<Predicate>),
    And(Box<Predicate>, Box<Predicate>),
    Or(Box<Predicate>, Box<Predicate>),
}

/// Context for matching predicates against program elements.
#[derive(Debug, Clone)]
pub struct MatchContext<'a> {
    /// Type name (for DI, mocking)
    pub type_name: Option<&'a str>,
    /// Module path
    pub module_path: Option<&'a str>,
    /// Attributes
    pub attrs: &'a [String],
    /// Function signature (for weaving)
    pub signature: Option<&'a str>,
    /// Effect set (for weaving)
    pub effects: &'a [String],
}

impl<'a> MatchContext<'a> {
    pub fn new() -> Self {
        Self {
            type_name: None,
            module_path: None,
            attrs: &[],
            signature: None,
            effects: &[],
        }
    }

    pub fn with_type_name(mut self, type_name: &'a str) -> Self {
        self.type_name = Some(type_name);
        self
    }

    pub fn with_module_path(mut self, module_path: &'a str) -> Self {
        self.module_path = Some(module_path);
        self
    }

    pub fn with_attrs(mut self, attrs: &'a [String]) -> Self {
        self.attrs = attrs;
        self
    }

    pub fn with_signature(mut self, signature: &'a str) -> Self {
        self.signature = Some(signature);
        self
    }

    pub fn with_effects(mut self, effects: &'a [String]) -> Self {
        self.effects = effects;
        self
    }
}

impl<'a> Default for MatchContext<'a> {
    fn default() -> Self {
        Self::new()
    }
}

impl Predicate {
    /// Check if this predicate matches the given context.
    pub fn matches(&self, ctx: &MatchContext<'_>) -> bool {
        match self {
            Predicate::Selector(sel) => sel.matches(ctx),
            Predicate::Not(inner) => !inner.matches(ctx),
            Predicate::And(lhs, rhs) => lhs.matches(ctx) && rhs.matches(ctx),
            Predicate::Or(lhs, rhs) => lhs.matches(ctx) || rhs.matches(ctx),
        }
    }

    /// Calculate specificity for tie-breaking.
    ///
    /// Higher specificity wins. Rules:
    /// - Literal segment: +2
    /// - Prefix/suffix wildcard (foo*, *bar): +1
    /// - Single wildcard *: 0
    /// - Multi-segment wildcard **: -2
    /// - Negation !: -1
    pub fn specificity(&self) -> i32 {
        match self {
            Predicate::Selector(sel) => sel.specificity(),
            Predicate::Not(inner) => inner.specificity() - 1,
            Predicate::And(lhs, rhs) => lhs.specificity() + rhs.specificity(),
            Predicate::Or(lhs, rhs) => lhs.specificity().max(rhs.specificity()),
        }
    }

    /// Validate that this predicate is legal in the given context.
    pub fn validate(&self, ctx: PredicateContext) -> Result<(), ValidationError> {
        match self {
            Predicate::Selector(sel) => sel.validate(ctx),
            Predicate::Not(inner) => inner.validate(ctx),
            Predicate::And(lhs, rhs) => {
                lhs.validate(ctx)?;
                rhs.validate(ctx)
            }
            Predicate::Or(lhs, rhs) => {
                lhs.validate(ctx)?;
                rhs.validate(ctx)
            }
        }
    }
}

impl Selector {
    fn matches(&self, ctx: &MatchContext<'_>) -> bool {
        match self {
            Selector::Within(pattern) => {
                if let Some(module_path) = ctx.module_path {
                    match_pattern(pattern, module_path)
                } else {
                    false
                }
            }
            Selector::Attr(name) => ctx.attrs.iter().any(|attr| attr == name),
            Selector::Type(pattern) => {
                if let Some(type_name) = ctx.type_name {
                    match_pattern(pattern, type_name)
                } else {
                    false
                }
            }
            Selector::Init(pattern) => {
                if let Some(type_name) = ctx.type_name {
                    match_pattern(pattern, type_name)
                } else {
                    false
                }
            }
            Selector::Effect(effect_name) => ctx.effects.iter().any(|e| e == effect_name),
            Selector::Test(pattern) => {
                if let Some(sig) = ctx.signature {
                    match_pattern(pattern, sig)
                } else {
                    false
                }
            }
            Selector::Execution(sig_pattern) => {
                if let Some(sig) = ctx.signature {
                    sig_pattern.matches(sig)
                } else {
                    false
                }
            }
            Selector::Call(sig_pattern) => {
                if let Some(sig) = ctx.signature {
                    sig_pattern.matches(sig)
                } else {
                    false
                }
            }
            Selector::Decision | Selector::Condition => {
                // Compiler-defined join points, always false for now
                false
            }
            Selector::Import { from, to } => {
                // Match import dependencies
                // Uses module_path for 'from' and type_name for 'to'
                let from_matches = if let Some(module_path) = ctx.module_path {
                    match_pattern(from, module_path)
                } else {
                    false
                };

                let to_matches = if let Some(type_name) = ctx.type_name {
                    match_pattern(to, type_name)
                } else {
                    false
                };

                from_matches && to_matches
            }
            Selector::Depend { from, to } => {
                // Same as Import for now (can be extended for transitive deps)
                let from_matches = if let Some(module_path) = ctx.module_path {
                    match_pattern(from, module_path)
                } else {
                    false
                };

                let to_matches = if let Some(type_name) = ctx.type_name {
                    match_pattern(to, type_name)
                } else {
                    false
                };

                from_matches && to_matches
            }
            Selector::Use(pattern) => {
                if let Some(type_name) = ctx.type_name {
                    match_pattern(pattern, type_name)
                } else {
                    false
                }
            }
            Selector::Export(pattern) => {
                if let Some(type_name) = ctx.type_name {
                    match_pattern(pattern, type_name)
                } else {
                    false
                }
            }
            Selector::Config(key) => {
                // Config matching requires build context
                let _ = key;
                false
            }
        }
    }

    fn specificity(&self) -> i32 {
        match self {
            Selector::Attr(_) => 2,
            Selector::Decision | Selector::Condition => 3, // Very specific
            Selector::Within(pattern)
            | Selector::Type(pattern)
            | Selector::Init(pattern)
            | Selector::Test(pattern)
            | Selector::Use(pattern)
            | Selector::Export(pattern) => pattern_specificity(pattern),
            Selector::Effect(_) | Selector::Config(_) => 2,
            Selector::Execution(sig) | Selector::Call(sig) => sig.specificity(),
            Selector::Import { from, to } | Selector::Depend { from, to } => {
                pattern_specificity(from) + pattern_specificity(to)
            }
        }
    }

    fn validate(&self, ctx: PredicateContext) -> Result<(), ValidationError> {
        let valid = match ctx {
            PredicateContext::Weaving => matches!(
                self,
                Selector::Execution(_)
                    | Selector::Within(_)
                    | Selector::Attr(_)
                    | Selector::Effect(_)
                    | Selector::Test(_)
                    | Selector::Decision
                    | Selector::Condition
                    | Selector::Call(_)
                    | Selector::Init(_) // Runtime weaving via DI proxies
            ),
            PredicateContext::DependencyInjection => {
                matches!(self, Selector::Type(_) | Selector::Within(_) | Selector::Attr(_))
            }
            PredicateContext::Mock => {
                matches!(self, Selector::Type(_) | Selector::Within(_) | Selector::Attr(_))
            }
            PredicateContext::Architecture => matches!(
                self,
                Selector::Import { .. }
                    | Selector::Depend { .. }
                    | Selector::Use(_)
                    | Selector::Export(_)
                    | Selector::Config(_)
                    | Selector::Within(_)
                    | Selector::Attr(_)
            ),
        };

        if !valid {
            Err(ValidationError::InvalidSelectorForContext {
                selector: format!("{:?}", self),
                context: ctx,
            })
        } else {
            Ok(())
        }
    }
}

impl SignaturePattern {
    fn matches(&self, signature: &str) -> bool {
        // Parse the signature: "ReturnType FunctionName(Arg1, Arg2, ...)"
        // Try to extract parts from the signature string

        // Find opening paren
        let paren_pos = if let Some(pos) = signature.find('(') {
            pos
        } else {
            // No params, just match qualified name
            return match_pattern(&self.qualified_name, signature);
        };

        let before_paren = &signature[..paren_pos].trim();

        // Split by whitespace to get return type and function name
        let parts: Vec<&str> = before_paren.split_whitespace().collect();

        let (return_part, name_part) = if parts.len() == 2 {
            (parts[0], parts[1])
        } else if parts.len() == 1 {
            // No explicit return type
            ("*", parts[0])
        } else {
            // Complex signature, just match on the whole thing
            return match_pattern(&self.qualified_name, signature);
        };

        // Match return type
        if self.return_type != "*" && !match_pattern(&self.return_type, return_part) {
            return false;
        }

        // Match function name
        if !match_pattern(&self.qualified_name, name_part) {
            return false;
        }

        // Match arguments if not ".."
        match &self.args {
            ArgPatterns::Any => true, // ".." matches any args
            ArgPatterns::Specific(expected_args) => {
                // Extract args from signature
                let args_end = signature.rfind(')').unwrap_or(signature.len());
                let args_str = &signature[paren_pos + 1..args_end].trim();

                if args_str.is_empty() {
                    return expected_args.is_empty();
                }

                let actual_args: Vec<&str> = args_str.split(',').map(|s| s.trim()).collect();

                if actual_args.len() != expected_args.len() {
                    return false;
                }

                // Match each argument pattern
                for (expected, actual) in expected_args.iter().zip(actual_args.iter()) {
                    if expected != "*" && !match_pattern(expected, actual) {
                        return false;
                    }
                }

                true
            }
        }
    }

    fn specificity(&self) -> i32 {
        let mut score = pattern_specificity(&self.qualified_name);

        // Return type specificity
        if self.return_type != "*" {
            score += 2;
        }

        // Argument specificity
        score = match &self.args {
            ArgPatterns::Any => score, // No bonus
            ArgPatterns::Specific(args) => score + (args.len() as i32 * 2),
        };

        score
    }
}

#[derive(Debug, Clone)]
pub enum ValidationError {
    InvalidSelectorForContext {
        selector: String,
        context: PredicateContext,
    },
}

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValidationError::InvalidSelectorForContext { selector, context } => {
                write!(
                    f,
                    "Selector {} is not valid in {:?} context",
                    selector, context
                )
            }
        }
    }
}

impl std::error::Error for ValidationError {}

/// Pattern matching with wildcards.
///
/// Supports:
/// - `*` matches one segment
/// - `**` matches zero or more segments
/// - `foo*` / `*bar` prefix/suffix wildcards
pub fn match_pattern(pattern: &str, value: &str) -> bool {
    let pat_segments: Vec<&str> = pattern.split('.').collect();
    let val_segments: Vec<&str> = value.split('.').collect();
    match_segments(&pat_segments, &val_segments)
}

fn match_segments(pat: &[&str], val: &[&str]) -> bool {
    if pat.is_empty() {
        return val.is_empty();
    }
    if pat[0] == "**" {
        // ** matches zero or more segments
        for skip in 0..=val.len() {
            if match_segments(&pat[1..], &val[skip..]) {
                return true;
            }
        }
        return false;
    }
    if val.is_empty() {
        return false;
    }
    if !match_segment(pat[0], val[0]) {
        return false;
    }
    match_segments(&pat[1..], &val[1..])
}

fn match_segment(pattern: &str, value: &str) -> bool {
    if pattern == "*" {
        return true;
    }
    if !pattern.contains('*') {
        return pattern == value;
    }

    // Handle prefix/suffix wildcards
    let mut remainder = value;
    let mut is_first = true;
    for part in pattern.split('*') {
        if part.is_empty() {
            is_first = false;
            continue;
        }
        if is_first {
            if !remainder.starts_with(part) {
                return false;
            }
            remainder = &remainder[part.len()..];
        } else if let Some(idx) = remainder.find(part) {
            remainder = &remainder[idx + part.len()..];
        } else {
            return false;
        }
        is_first = false;
    }

    if !pattern.ends_with('*') {
        if let Some(last) = pattern.split('*').last() {
            return remainder.is_empty() && (last.is_empty() || pattern.ends_with(last));
        }
    }
    true
}

fn pattern_specificity(pattern: &str) -> i32 {
    pattern
        .split('.')
        .map(segment_specificity)
        .sum::<i32>()
}

fn segment_specificity(segment: &str) -> i32 {
    if segment == "**" {
        -2
    } else if segment == "*" {
        0
    } else if segment.contains('*') {
        1 // Prefix/suffix wildcard
    } else {
        2 // Literal
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pattern_matching() {
        assert!(match_pattern("app.**", "app.core.user"));
        assert!(match_pattern("app.*.user", "app.core.user"));
        assert!(!match_pattern("app.*.user", "app.core.auth.user"));
        assert!(match_pattern("app.service*", "app.service_v2"));
        assert!(match_pattern("*Service", "UserService"));
    }

    #[test]
    fn test_specificity() {
        let pred1 = Predicate::Selector(Selector::Within("app.core.user".into()));
        let pred2 = Predicate::Selector(Selector::Within("app.**".into()));
        assert!(pred1.specificity() > pred2.specificity());
    }

    #[test]
    fn test_context_validation() {
        let exec = Predicate::Selector(Selector::Execution(SignaturePattern {
            return_type: "*".into(),
            qualified_name: "User.new".into(),
            args: ArgPatterns::Any,
        }));

        // Valid in weaving context
        assert!(exec.validate(PredicateContext::Weaving).is_ok());

        // Invalid in DI context
        assert!(exec.validate(PredicateContext::DependencyInjection).is_err());
    }

    #[test]
    fn test_predicate_matching() {
        let attrs = vec!["inject".to_string()];
        let ctx = MatchContext::new()
            .with_type_name("UserService")
            .with_module_path("app.core.user")
            .with_attrs(&attrs);

        let pred = Predicate::And(
            Box::new(Predicate::Selector(Selector::Type("*Service".into()))),
            Box::new(Predicate::Selector(Selector::Attr("inject".into()))),
        );

        assert!(pred.matches(&ctx));
    }

    #[test]
    fn test_signature_pattern_matching() {
        // Test various signature patterns
        let sig1 = SignaturePattern {
            return_type: "*".into(),
            qualified_name: "my_function".into(),
            args: ArgPatterns::Any,
        };
        assert!(sig1.matches("I64 my_function()"));
        assert!(sig1.matches("String my_function(I64, String)"));

        let sig2 = SignaturePattern {
            return_type: "I64".into(),
            qualified_name: "calc".into(),
            args: ArgPatterns::Specific(vec!["I64".into(), "I64".into()]),
        };
        assert!(sig2.matches("I64 calc(I64, I64)"));
        assert!(!sig2.matches("String calc(I64, I64)"));  // Wrong return type
        assert!(!sig2.matches("I64 calc(I64)"));  // Wrong arg count

        let sig3 = SignaturePattern {
            return_type: "*".into(),
            qualified_name: "User.*".into(),
            args: ArgPatterns::Any,
        };
        assert!(sig3.matches("Void User.new()"));
        assert!(sig3.matches("String User.getName()"));
        assert!(!sig3.matches("I64 Service.calc()"));  // Wrong class
    }
}

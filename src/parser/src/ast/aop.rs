//! AST nodes for AOP (Aspect-Oriented Programming) and predicates.
//!
//! This module defines AST nodes for:
//! - Predicate expressions (`pc{...}`)
//! - AOP advice declarations (`on pc{...} use <Interceptor>`)
//! - DI bindings (`bind on pc{...} -> <Impl>`)
//! - Architecture rules (`forbid pc{...}`, `allow pc{...}`)
//!
//! See doc/research/aop.md for the complete specification.

use crate::token::Span;
// Don't import from ast to avoid circular dependencies
// We'll use String for types and paths, and Box<Expr> where needed

/// Predicate expression within `pc{...}` syntactic island.
/// The predicate language supports boolean combinators and selector functions.
#[derive(Debug, Clone, PartialEq)]
pub struct PredicateExpr {
    pub kind: PredicateKind,
    pub span: Span,
}

#[derive(Debug, Clone, PartialEq)]
pub enum PredicateKind {
    /// Selector function call, e.g., `execution(* User.new(..))`
    Selector {
        name: String,
        args: Vec<String>,
    },
    /// Logical NOT: `!predicate`
    Not(Box<PredicateExpr>),
    /// Logical AND: `pred1 & pred2`
    And(Box<PredicateExpr>, Box<PredicateExpr>),
    /// Logical OR: `pred1 | pred2`
    Or(Box<PredicateExpr>, Box<PredicateExpr>),
}

/// Path pattern string for matching module/type paths.
/// Supports wildcards: `*`, `**`, `prefix*`, `*suffix`
/// Note: Renamed to PathPattern to avoid collision with Pattern (match pattern) enum
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathPattern {
    pub value: String,
    pub span: Span,
}

/// Signature pattern for matching function signatures.
/// Format: `ret_type qname(args...)`
/// Example: `* User.new(..)`, `i64 *.calculate(i64, i64)`
#[derive(Debug, Clone, PartialEq)]
pub struct SignaturePattern {
    /// Return type pattern (* matches any)
    pub return_type: String,
    /// Qualified name pattern (e.g., User.new, *.calculate)
    pub qualified_name: String,
    /// Argument patterns (.. matches any, or specific patterns)
    pub args: Vec<String>, // Empty for `..`, specific types otherwise
    pub span: Span,
}

/// AOP advice declaration: `on pc{...} use <Interceptor>`
#[derive(Debug, Clone, PartialEq)]
pub struct AopAdvice {
    /// Pointcut predicate
    pub pointcut: PredicateExpr,
    /// Advice type (before, after_success, after_error, around)
    pub advice_type: AdviceType,
    /// Interceptor class/function to use (qualified name like "MyModule.MyClass")
    pub interceptor: String,
    /// Priority (optional, default 0)
    pub priority: Option<i64>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AdviceType {
    Before,
    AfterSuccess,
    AfterError,
    Around,
}

/// Dependency injection binding: `bind on pc{...} -> <Impl> scope priority`
#[derive(Debug, Clone, PartialEq)]
pub struct DiBinding {
    /// Pointcut predicate for selecting injection points
    pub pointcut: PredicateExpr,
    /// Implementation type to bind (qualified name like "MyModule.MyImpl")
    pub implementation: String,
    /// Scope (singleton, transient, etc.)
    pub scope: Option<DiScope>,
    /// Priority for tie-breaking
    pub priority: Option<i64>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiScope {
    Singleton,
    Transient,
    Scoped,
}

/// Architecture rule: `forbid pc{...}` or `allow pc{...}`
#[derive(Debug, Clone, PartialEq)]
pub struct ArchitectureRule {
    /// Rule type (forbid or allow)
    pub rule_type: ArchRuleType,
    /// Pointcut predicate for matching dependencies
    pub pointcut: PredicateExpr,
    /// Optional description/message
    pub message: Option<String>,
    pub span: Span,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArchRuleType {
    Forbid,
    Allow,
}

/// Mock declaration: `mock Name implements Trait:`
#[derive(Debug, Clone, PartialEq)]
pub struct MockDecl {
    /// Mock name
    pub name: String,
    /// Trait being mocked (qualified name like "MyTrait")
    pub trait_name: String,
    /// Method expectations (stored as strings, parsed later)
    pub expectations: Vec<String>,
    pub span: Span,
}

impl PredicateExpr {
    pub fn selector(name: String, args: Vec<String>, span: Span) -> Self {
        Self {
            kind: PredicateKind::Selector { name, args },
            span,
        }
    }

    pub fn not(inner: PredicateExpr, span: Span) -> Self {
        Self {
            kind: PredicateKind::Not(Box::new(inner)),
            span,
        }
    }

    pub fn and(left: PredicateExpr, right: PredicateExpr, span: Span) -> Self {
        Self {
            kind: PredicateKind::And(Box::new(left), Box::new(right)),
            span,
        }
    }

    pub fn or(left: PredicateExpr, right: PredicateExpr, span: Span) -> Self {
        Self {
            kind: PredicateKind::Or(Box::new(left), Box::new(right)),
            span,
        }
    }
}

impl AdviceType {
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "before" => Some(AdviceType::Before),
            "after_success" | "after-success" => Some(AdviceType::AfterSuccess),
            "after_error" | "after-error" => Some(AdviceType::AfterError),
            "around" => Some(AdviceType::Around),
            _ => None,
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            AdviceType::Before => "before",
            AdviceType::AfterSuccess => "after_success",
            AdviceType::AfterError => "after_error",
            AdviceType::Around => "around",
        }
    }
}

impl DiScope {
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "singleton" => Some(DiScope::Singleton),
            "transient" => Some(DiScope::Transient),
            "scoped" => Some(DiScope::Scoped),
            _ => None,
        }
    }

    pub fn as_str(&self) -> &'static str {
        match self {
            DiScope::Singleton => "singleton",
            DiScope::Transient => "transient",
            DiScope::Scoped => "scoped",
        }
    }
}

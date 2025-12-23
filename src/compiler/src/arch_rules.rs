//! Architecture rules engine for enforcing dependency constraints.
//!
//! This module provides architecture validation using the unified predicate system.
//! Rules can forbid or allow specific dependencies, imports, or type usage patterns.
//!
//! See doc/research/aop.md section 10 for the complete specification.

use crate::hir::HirModule;
use crate::predicate::{MatchContext, Predicate, PredicateContext};
use std::collections::HashMap;

/// Rule action - forbid or allow
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RuleAction {
    /// Forbid the matched pattern (violations are errors)
    Forbid,
    /// Allow the matched pattern (can override Forbid with higher priority)
    Allow,
}

/// An architecture rule
#[derive(Debug, Clone)]
pub struct ArchRule {
    pub action: RuleAction,
    pub predicate: Predicate,
    pub priority: i64,
    pub message: Option<String>,
}

/// Architecture rules configuration
#[derive(Debug, Clone)]
pub struct ArchRulesConfig {
    pub enabled: bool,
    pub rules: Vec<ArchRule>,
}

impl ArchRulesConfig {
    /// Create an empty configuration (validation disabled)
    pub fn disabled() -> Self {
        Self {
            enabled: false,
            rules: Vec::new(),
        }
    }

    /// Create a configuration with the given rules
    pub fn new(rules: Vec<ArchRule>) -> Self {
        Self {
            enabled: !rules.is_empty(),
            rules,
        }
    }
}

/// Dependency type for architecture validation
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DependencyKind {
    /// Module import
    Import { from: String, to: String },
    /// General dependency (import or usage)
    Depend { from: String, to: String },
    /// Type usage
    Use { type_name: String, location: String },
}

/// A detected dependency in the program
#[derive(Debug, Clone)]
pub struct Dependency {
    pub kind: DependencyKind,
    pub source_file: String,
    pub line: usize,
}

impl Dependency {
    /// Create a match context for predicate evaluation
    pub fn to_match_context(&self) -> MatchContext<'_> {
        match &self.kind {
            DependencyKind::Import { from, to } => MatchContext::new()
                .with_module_path(from)
                .with_type_name(to),
            DependencyKind::Depend { from, to } => MatchContext::new()
                .with_module_path(from)
                .with_type_name(to),
            DependencyKind::Use { type_name, location } => {
                MatchContext::new().with_type_name(type_name).with_module_path(location)
            }
        }
    }
}

/// Architecture rule violation
#[derive(Debug, Clone)]
pub struct Violation {
    pub dependency: Dependency,
    pub rule: ArchRule,
    pub message: String,
}

/// Architecture rules checker
pub struct ArchRulesChecker {
    config: ArchRulesConfig,
}

impl ArchRulesChecker {
    /// Create a new checker with the given configuration
    pub fn new(config: ArchRulesConfig) -> Self {
        Self { config }
    }

    /// Check a module for architecture rule violations
    pub fn check_module(&self, module: &HirModule) -> Vec<Violation> {
        if !self.config.enabled {
            return Vec::new();
        }

        let dependencies = self.extract_dependencies(module);
        let mut violations = Vec::new();

        for dep in dependencies {
            if let Some(violation) = self.check_dependency(&dep) {
                violations.push(violation);
            }
        }

        violations
    }

    /// Extract dependencies from a module
    fn extract_dependencies(&self, module: &HirModule) -> Vec<Dependency> {
        let mut deps = Vec::new();

        // TODO: Extract imports from module
        // For now, return empty list - this needs to be implemented
        // when the module system has import tracking

        // Extract type usage from functions
        for func in &module.functions {
            // TODO: Scan function body for type usage
            // This would require analyzing the HIR expressions
            // For now, just extract from function signature
            let _ = func; // Suppress unused warning
        }

        deps
    }

    /// Check a single dependency against all rules
    fn check_dependency(&self, dep: &Dependency) -> Option<Violation> {
        let match_ctx = dep.to_match_context();

        // Collect matching rules with their priorities
        let mut matched_rules: Vec<(RuleAction, i64, &ArchRule)> = Vec::new();

        for rule in &self.config.rules {
            if rule
                .predicate
                .validate(PredicateContext::Architecture)
                .is_ok()
                && rule.predicate.matches(&match_ctx)
            {
                matched_rules.push((rule.action, rule.priority, rule));
            }
        }

        if matched_rules.is_empty() {
            return None;
        }

        // Sort by priority (higher first), then by action (Forbid before Allow)
        matched_rules.sort_by(|a, b| {
            b.1.cmp(&a.1).then_with(|| {
                match (a.0, b.0) {
                    (RuleAction::Forbid, RuleAction::Allow) => std::cmp::Ordering::Less,
                    (RuleAction::Allow, RuleAction::Forbid) => std::cmp::Ordering::Greater,
                    _ => std::cmp::Ordering::Equal,
                }
            })
        });

        // The highest priority rule wins
        let (winning_action, _, winning_rule) = &matched_rules[0];

        if *winning_action == RuleAction::Forbid {
            let message = winning_rule.message.clone().unwrap_or_else(|| {
                format!(
                    "Architecture violation: forbidden dependency at {}:{}",
                    dep.source_file, dep.line
                )
            });

            Some(Violation {
                dependency: dep.clone(),
                rule: (*winning_rule).clone(),
                message,
            })
        } else {
            None
        }
    }
}

/// Parse architecture rules from SDN-like configuration
pub fn parse_arch_rules(config_str: &str) -> Result<ArchRulesConfig, String> {
    // TODO: Implement proper SDN parsing
    // For now, return an empty configuration
    let _ = config_str;
    Ok(ArchRulesConfig::disabled())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::predicate_parser::parse_predicate;

    #[test]
    fn test_arch_rules_disabled() {
        let config = ArchRulesConfig::disabled();
        let checker = ArchRulesChecker::new(config);

        // Create a dummy module
        let module = HirModule::new();

        let violations = checker.check_module(&module);
        assert_eq!(violations.len(), 0);
    }

    #[test]
    fn test_forbid_import() {
        // Rule: forbid imports from domain to infrastructure
        let predicate = parse_predicate("pc{ within(domain.**) }").unwrap();

        let rule = ArchRule {
            action: RuleAction::Forbid,
            predicate,
            priority: 10,
            message: Some("Domain layer cannot import from infrastructure".to_string()),
        };

        let config = ArchRulesConfig::new(vec![rule]);
        let checker = ArchRulesChecker::new(config);

        // Test with a dependency that matches
        let dep = Dependency {
            kind: DependencyKind::Import {
                from: "domain.user".to_string(),
                to: "infrastructure.db".to_string(),
            },
            source_file: "domain/user.spl".to_string(),
            line: 10,
        };

        let violation = checker.check_dependency(&dep);
        assert!(violation.is_some());
        if let Some(v) = violation {
            assert!(v.message.contains("Domain layer"));
        }
    }

    #[test]
    fn test_allow_overrides_forbid() {
        // Forbid all within domain
        let forbid_pred = parse_predicate("pc{ within(domain.**) }").unwrap();
        let forbid_rule = ArchRule {
            action: RuleAction::Forbid,
            predicate: forbid_pred,
            priority: 10,
            message: None,
        };

        // Allow specific exceptions with higher priority
        let allow_pred = parse_predicate("pc{ within(domain.exceptions.**) }").unwrap();
        let allow_rule = ArchRule {
            action: RuleAction::Allow,
            predicate: allow_pred,
            priority: 20,
            message: None,
        };

        let config = ArchRulesConfig::new(vec![forbid_rule, allow_rule]);
        let checker = ArchRulesChecker::new(config);

        // Test with a dependency in exceptions (should be allowed)
        let dep = Dependency {
            kind: DependencyKind::Import {
                from: "domain.exceptions.custom".to_string(),
                to: "infrastructure.logging".to_string(),
            },
            source_file: "domain/exceptions/custom.spl".to_string(),
            line: 5,
        };

        let violation = checker.check_dependency(&dep);
        assert!(violation.is_none(), "Higher priority allow should override forbid");
    }

    #[test]
    fn test_import_selector() {
        // Forbid imports from domain to infrastructure
        let predicate =
            parse_predicate("pc{ import(domain.**, infrastructure.**) }").unwrap();

        let rule = ArchRule {
            action: RuleAction::Forbid,
            predicate,
            priority: 10,
            message: Some("Domain layer cannot depend on infrastructure".to_string()),
        };

        let config = ArchRulesConfig::new(vec![rule]);
        let checker = ArchRulesChecker::new(config);

        // Test with a matching import
        let dep = Dependency {
            kind: DependencyKind::Import {
                from: "domain.user".to_string(),
                to: "infrastructure.database".to_string(),
            },
            source_file: "domain/user.spl".to_string(),
            line: 1,
        };

        let violation = checker.check_dependency(&dep);
        assert!(violation.is_some(), "Import selector should match");

        // Test with a non-matching import
        let dep2 = Dependency {
            kind: DependencyKind::Import {
                from: "infrastructure.database".to_string(),
                to: "domain.user".to_string(),
            },
            source_file: "infrastructure/database.spl".to_string(),
            line: 1,
        };

        let violation2 = checker.check_dependency(&dep2);
        assert!(violation2.is_none(), "Import selector should not match reversed dependency");
    }

    #[test]
    fn test_use_selector() {
        // Forbid use of Container in domain layer
        let predicate = parse_predicate("pc{ use(Container) & within(domain.**) }").unwrap();

        let rule = ArchRule {
            action: RuleAction::Forbid,
            predicate,
            priority: 10,
            message: Some("Domain layer should not use Container directly".to_string()),
        };

        let config = ArchRulesConfig::new(vec![rule]);
        let checker = ArchRulesChecker::new(config);

        // Test with matching usage
        let dep = Dependency {
            kind: DependencyKind::Use {
                type_name: "Container".to_string(),
                location: "domain.services".to_string(),
            },
            source_file: "domain/services.spl".to_string(),
            line: 10,
        };

        let violation = checker.check_dependency(&dep);
        assert!(violation.is_some(), "Use selector should match");

        // Test with non-matching location
        let dep2 = Dependency {
            kind: DependencyKind::Use {
                type_name: "Container".to_string(),
                location: "infrastructure.ioc".to_string(),
            },
            source_file: "infrastructure/ioc.spl".to_string(),
            line: 5,
        };

        let violation2 = checker.check_dependency(&dep2);
        assert!(
            violation2.is_none(),
            "Use selector should not match outside domain"
        );
    }
}

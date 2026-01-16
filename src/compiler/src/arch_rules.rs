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

    /// Load from HIR architecture rules (parsed from Simple source code)
    pub fn from_hir_rules(hir_rules: &[crate::hir::HirArchRule]) -> Self {
        let rules = hir_rules
            .iter()
            .filter_map(|hir_rule| {
                let action = match hir_rule.rule_type.as_str() {
                    "forbid" => RuleAction::Forbid,
                    "allow" => RuleAction::Allow,
                    _ => return None,
                };

                // Parse the predicate text
                // Silently skip rules with invalid predicates during filter_map
                // Predicate syntax is validated during HIR lowering where proper
                // error reporting occurs
                let predicate = match crate::predicate_parser::parse_predicate(&hir_rule.predicate_text) {
                    Ok(pred) => pred,
                    Err(_) => return None,
                };

                Some(ArchRule {
                    action,
                    predicate,
                    priority: hir_rule.priority,
                    message: hir_rule.message.clone(),
                })
            })
            .collect();

        Self::new(rules)
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
            DependencyKind::Import { from, to } => MatchContext::new().with_module_path(from).with_type_name(to),
            DependencyKind::Depend { from, to } => MatchContext::new().with_module_path(from).with_type_name(to),
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

        // Extract imports from module
        let module_name = module.name.as_deref().unwrap_or("<unknown>");

        for import in &module.imports {
            let from = module_name.to_string();

            if import.is_glob {
                // Glob import: use foo.bar.*
                let to = import.from_path.join(".");
                deps.push(Dependency {
                    kind: DependencyKind::Import { from: from.clone(), to },
                    source_file: module_name.to_string(),
                    // Line number tracking requires adding source location fields to HIR structures
                    // (HirImport, HirFunction, LocalVar, etc.) and threading this information
                    // through the entire lowering pipeline from AST -> HIR -> MIR
                    line: 0,
                });
            } else {
                // Specific imports: use foo.bar.{Item1, Item2}
                for (item, _alias) in &import.items {
                    let mut to_path = import.from_path.clone();
                    to_path.push(item.clone());
                    let to = to_path.join(".");

                    deps.push(Dependency {
                        kind: DependencyKind::Import { from: from.clone(), to },
                        source_file: module_name.to_string(),
                        line: 0, // Requires HIR source location fields
                    });
                }
            }
        }

        // Extract type usage from functions
        for func in &module.functions {
            // Extract from function signature (parameters and return type)
            for param in &func.params {
                if let Some(type_name) = self.get_type_name(param.ty, &module.types) {
                    deps.push(Dependency {
                        kind: DependencyKind::Use {
                            type_name,
                            location: module_name.to_string(),
                        },
                        source_file: module_name.to_string(),
                        line: 0, // Requires HIR source location fields
                    });
                }
            }

            // Extract from return type
            if let Some(type_name) = self.get_type_name(func.return_type, &module.types) {
                deps.push(Dependency {
                    kind: DependencyKind::Use {
                        type_name,
                        location: module_name.to_string(),
                    },
                    source_file: module_name.to_string(),
                    line: 0, // TODO: [compiler][P2] Track line numbers
                });
            }

            // Extract from local variables
            for local in &func.locals {
                if let Some(type_name) = self.get_type_name(local.ty, &module.types) {
                    deps.push(Dependency {
                        kind: DependencyKind::Use {
                            type_name,
                            location: module_name.to_string(),
                        },
                        source_file: module_name.to_string(),
                        line: 0, // Requires HIR source location fields
                    });
                }
            }
        }

        deps
    }

    /// Get the type name from a TypeId for dependency tracking.
    /// Returns the type name for named types (struct, class, enum).
    /// Built-in types (i64, bool, etc.) are not tracked since they're not architectural dependencies.
    fn get_type_name(&self, type_id: crate::hir::TypeId, types: &crate::hir::TypeRegistry) -> Option<String> {
        types.get_type_name(type_id).map(|s| s.to_string())
    }

    /// Check a single dependency against all rules
    fn check_dependency(&self, dep: &Dependency) -> Option<Violation> {
        let match_ctx = dep.to_match_context();

        // Collect matching rules with their priorities
        let mut matched_rules: Vec<(RuleAction, i64, &ArchRule)> = Vec::new();

        for rule in &self.config.rules {
            if rule.predicate.validate(PredicateContext::Architecture).is_ok() && rule.predicate.matches(&match_ctx) {
                matched_rules.push((rule.action, rule.priority, rule));
            }
        }

        if matched_rules.is_empty() {
            return None;
        }

        // Sort by priority (higher first), then by action (Forbid before Allow)
        matched_rules.sort_by(|a, b| {
            b.1.cmp(&a.1).then_with(|| match (a.0, b.0) {
                (RuleAction::Forbid, RuleAction::Allow) => std::cmp::Ordering::Less,
                (RuleAction::Allow, RuleAction::Forbid) => std::cmp::Ordering::Greater,
                _ => std::cmp::Ordering::Equal,
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
///
/// NOTE: Currently returns disabled configuration. Architecture rules are defined
/// programmatically via ArchRulesConfig::with_rules() or through compiler directives.
/// SDN file-based configuration will be implemented when needed for project-level
/// architecture enforcement files.
pub fn parse_arch_rules(config_str: &str) -> Result<ArchRulesConfig, String> {
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
        let predicate = parse_predicate("pc{ import(domain.**, infrastructure.**) }").unwrap();

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
        assert!(
            violation2.is_none(),
            "Import selector should not match reversed dependency"
        );
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
        assert!(violation2.is_none(), "Use selector should not match outside domain");
    }

    #[test]
    fn test_wildcard_import_pattern() {
        // Test pattern: import(*, crate.test.*)
        // Should match any module importing from crate.test.*
        let predicate = parse_predicate("pc{ import(*, crate.test.*) }").unwrap();

        let rule = ArchRule {
            action: RuleAction::Forbid,
            predicate,
            priority: 10,
            message: Some("Cannot import from test modules".to_string()),
        };

        let config = ArchRulesConfig::new(vec![rule]);
        let checker = ArchRulesChecker::new(config);

        // Test with matching import
        let dep = Dependency {
            kind: DependencyKind::Import {
                from: "<unknown>".to_string(),
                to: "crate.test.helpers".to_string(),
            },
            source_file: "test.spl".to_string(),
            line: 1,
        };

        let violation = checker.check_dependency(&dep);
        assert!(
            violation.is_some(),
            "Should detect violation for import from crate.test.helpers"
        );
        if let Some(v) = violation {
            assert!(v.message.contains("Cannot import from test modules"));
        }

        // Test with non-matching import
        let dep2 = Dependency {
            kind: DependencyKind::Import {
                from: "<unknown>".to_string(),
                to: "crate.infrastructure.database".to_string(),
            },
            source_file: "test.spl".to_string(),
            line: 2,
        };

        let violation2 = checker.check_dependency(&dep2);
        assert!(
            violation2.is_none(),
            "Should not detect violation for import from crate.infrastructure"
        );
    }

    #[test]
    fn test_type_usage_extraction() {
        // Test that type usage from function signatures is extracted
        use crate::hir::{HirFunction, HirModule, LocalVar, TypeId, TypeRegistry};
        use simple_parser::ast::Mutability;

        let mut module = HirModule::new();

        // Create a function that uses a custom type
        let func = HirFunction {
            name: "process".to_string(),
            params: vec![],
            locals: vec![],
            return_type: TypeId::I64,
            body: vec![],
            visibility: simple_parser::ast::Visibility::Public,
            contract: None,
            is_pure: false,
            inject: false,
            concurrency_mode: crate::hir::ConcurrencyMode::Unsafe,
            module_path: String::new(),
            attributes: vec![],
            effects: vec![],
            layout_hint: None,
            verification_mode: crate::hir::VerificationMode::default(),
            is_ghost: false,
        };

        module.functions.push(func);

        // Create checker
        let config = ArchRulesConfig::disabled();
        let checker = ArchRulesChecker::new(config);

        // Extract dependencies
        let deps = checker.extract_dependencies(&module);

        // Should not have any type usage dependencies (i64 is built-in)
        let type_deps: Vec<_> = deps
            .iter()
            .filter(|d| matches!(d.kind, DependencyKind::Use { .. }))
            .collect();

        assert_eq!(type_deps.len(), 0, "Built-in types should not be tracked");
    }

    #[test]
    fn test_use_selector_for_types() {
        // Test use() selector for type usage
        let predicate = parse_predicate("pc{ use(DatabaseConnection) }").unwrap();

        let rule = ArchRule {
            action: RuleAction::Forbid,
            predicate,
            priority: 10,
            message: Some("Direct database usage is forbidden".to_string()),
        };

        let config = ArchRulesConfig::new(vec![rule]);
        let checker = ArchRulesChecker::new(config);

        // Test with matching type usage
        let dep = Dependency {
            kind: DependencyKind::Use {
                type_name: "DatabaseConnection".to_string(),
                location: "services".to_string(),
            },
            source_file: "services.spl".to_string(),
            line: 10,
        };

        let violation = checker.check_dependency(&dep);
        assert!(
            violation.is_some(),
            "Should detect violation for DatabaseConnection usage"
        );
        if let Some(v) = violation {
            assert!(v.message.contains("Direct database usage is forbidden"));
        }

        // Test with non-matching type
        let dep2 = Dependency {
            kind: DependencyKind::Use {
                type_name: "UserService".to_string(),
                location: "services".to_string(),
            },
            source_file: "services.spl".to_string(),
            line: 15,
        };

        let violation2 = checker.check_dependency(&dep2);
        assert!(violation2.is_none(), "Should not match UserService");
    }

    #[test]
    fn test_combined_use_and_within() {
        // Test combining use() with within() to restrict type usage in specific modules
        let predicate = parse_predicate("pc{ use(DatabaseConnection) & within(domain.**) }").unwrap();

        let rule = ArchRule {
            action: RuleAction::Forbid,
            predicate,
            priority: 10,
            message: Some("Domain layer cannot use database directly".to_string()),
        };

        let config = ArchRulesConfig::new(vec![rule]);
        let checker = ArchRulesChecker::new(config);

        // Test with matching usage in domain layer
        let dep = Dependency {
            kind: DependencyKind::Use {
                type_name: "DatabaseConnection".to_string(),
                location: "domain.services".to_string(),
            },
            source_file: "domain/services.spl".to_string(),
            line: 10,
        };

        let violation = checker.check_dependency(&dep);
        assert!(violation.is_some(), "Should detect database usage in domain layer");

        // Test with same type but in infrastructure layer
        let dep2 = Dependency {
            kind: DependencyKind::Use {
                type_name: "DatabaseConnection".to_string(),
                location: "infrastructure.persistence".to_string(),
            },
            source_file: "infrastructure/persistence.spl".to_string(),
            line: 5,
        };

        let violation2 = checker.check_dependency(&dep2);
        assert!(violation2.is_none(), "Infrastructure layer can use database");
    }
}

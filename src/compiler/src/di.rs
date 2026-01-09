//! Dependency injection configuration and predicate parsing.

use crate::predicate::{MatchContext, Predicate, PredicateContext};
use crate::predicate_parser;
use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiMode {
    Hybrid,
    Manual,
}

impl DiMode {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "hybrid" => Ok(DiMode::Hybrid),
            "manual" => Ok(DiMode::Manual),
            _ => Err(format!("unknown di.mode '{}'", value)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiScope {
    Singleton,
    Transient,
}

impl DiScope {
    fn parse(value: &str) -> Result<Self, String> {
        match value {
            "Singleton" | "singleton" => Ok(DiScope::Singleton),
            "Transient" | "transient" => Ok(DiScope::Transient),
            _ => Err(format!("unknown scope '{}'", value)),
        }
    }
}

#[derive(Debug, Clone)]
pub struct DiBindingRule {
    pub predicate: Predicate,
    pub impl_type: String,
    pub scope: DiScope,
    pub priority: i64,
    pub order: usize,
    pub raw_predicate: String,
}

#[derive(Debug, Clone, Default)]
pub struct DiProfile {
    pub bindings: Vec<DiBindingRule>,
}

#[derive(Debug, Clone)]
pub struct DiConfig {
    pub mode: DiMode,
    pub profiles: HashMap<String, DiProfile>,
}

#[derive(Debug, Clone)]
pub struct DiResolveError {
    pub profile: String,
    pub matches: Vec<(String, i64, i32)>,
}

/// Helper to create a match context for DI binding selection.
pub fn create_di_match_context<'a>(
    type_name: &'a str,
    module_path: &'a str,
    attrs: &'a [String],
) -> MatchContext<'a> {
    MatchContext::new()
        .with_type_name(type_name)
        .with_module_path(module_path)
        .with_attrs(attrs)
}

impl DiConfig {
    pub fn select_binding(
        &self,
        profile: &str,
        ctx: &MatchContext<'_>,
    ) -> Result<Option<&DiBindingRule>, DiResolveError> {
        let Some(profile_cfg) = self.profiles.get(profile) else {
            return Ok(None);
        };

        let mut matches = Vec::new();
        for binding in &profile_cfg.bindings {
            if binding.predicate.matches(ctx) {
                let specificity = binding.predicate.specificity();
                matches.push((binding, specificity));
            }
        }

        if matches.is_empty() {
            return Ok(None);
        }

        matches.sort_by(|(a, a_spec), (b, b_spec)| {
            a.priority
                .cmp(&b.priority)
                .then_with(|| a_spec.cmp(b_spec))
                .then_with(|| b.order.cmp(&a.order))
        });

        let (winner, _) = matches.last().unwrap();
        Ok(Some(*winner))
    }
}

pub fn parse_di_config(toml: &toml::Value) -> Result<Option<DiConfig>, String> {
    let Some(di_table) = toml.get("di").and_then(|v| v.as_table()) else {
        return Ok(None);
    };

    let mode = di_table
        .get("mode")
        .and_then(|v| v.as_str())
        .map(DiMode::parse)
        .transpose()?
        .unwrap_or(DiMode::Hybrid);

    let mut profiles = HashMap::new();
    if let Some(profiles_table) = di_table.get("profiles").and_then(|v| v.as_table()) {
        for (profile_name, profile_value) in profiles_table {
            let mut profile = DiProfile::default();
            let bindings = match profile_value.get("bindings") {
                None => Vec::new(),
                Some(value) => value
                    .as_array()
                    .ok_or_else(|| {
                        format!("di.profiles.{}.bindings must be an array", profile_name)
                    })?
                    .clone(),
            };

            for (idx, binding_val) in bindings.iter().enumerate() {
                let binding = binding_val.as_table().ok_or_else(|| {
                    format!(
                        "di.profiles.{}.bindings[{}] must be a table",
                        profile_name, idx
                    )
                })?;

                let predicate_raw = binding
                    .get("on")
                    .or_else(|| binding.get("predicate"))
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| {
                        format!(
                            "di.profiles.{}.bindings[{}] missing 'on' predicate",
                            profile_name, idx
                        )
                    })?;
                let predicate = predicate_parser::parse_predicate(predicate_raw)?;
                // Validate that the predicate is legal for DI context
                predicate
                    .validate(PredicateContext::DependencyInjection)
                    .map_err(|e| format!("invalid predicate for DI binding: {}", e))?;

                let impl_type = binding
                    .get("impl")
                    .or_else(|| binding.get("impl_type"))
                    .and_then(|v| v.as_str())
                    .ok_or_else(|| {
                        format!(
                            "di.profiles.{}.bindings[{}] missing 'impl' type",
                            profile_name, idx
                        )
                    })?
                    .to_string();

                let scope = binding
                    .get("scope")
                    .and_then(|v| v.as_str())
                    .map(DiScope::parse)
                    .transpose()?
                    .unwrap_or(DiScope::Transient);

                let priority = binding
                    .get("priority")
                    .and_then(|v| v.as_integer())
                    .unwrap_or(0);

                profile.bindings.push(DiBindingRule {
                    predicate,
                    impl_type,
                    scope,
                    priority,
                    order: idx,
                    raw_predicate: predicate_raw.to_string(),
                });
            }

            profiles.insert(profile_name.clone(), profile);
        }
    }

    Ok(Some(DiConfig { mode, profiles }))
}

/// Runtime DI container for managing instances.
#[derive(Debug, Clone)]
pub struct DiContainer {
    /// Singleton instances (type name -> value)
    singletons: HashMap<String, crate::value::Value>,
    /// Configuration for bindings
    config: DiConfig,
    /// Active profile name
    active_profile: String,
}

impl DiContainer {
    /// Create a new DI container with the given configuration.
    pub fn new(config: DiConfig, active_profile: String) -> Self {
        Self {
            singletons: HashMap::new(),
            config,
            active_profile,
        }
    }

    /// Resolve a dependency for the given type.
    ///
    /// Returns the implementation type name to instantiate.
    pub fn resolve_type(
        &self,
        type_name: &str,
        module_path: &str,
        attrs: &[String],
    ) -> Result<Option<(String, DiScope)>, DiResolveError> {
        let ctx = create_di_match_context(type_name, module_path, attrs);
        let binding = self.config.select_binding(&self.active_profile, &ctx)?;

        Ok(binding.map(|b| (b.impl_type.clone(), b.scope)))
    }

    /// Get or create a singleton instance.
    ///
    /// For singleton scope, this manages the cached instance.
    /// For transient scope, this always returns None (caller creates new instance).
    pub fn get_or_create_singleton(
        &mut self,
        impl_type: &str,
        scope: DiScope,
        create_fn: impl FnOnce() -> crate::value::Value,
    ) -> crate::value::Value {
        match scope {
            DiScope::Singleton => self
                .singletons
                .entry(impl_type.to_string())
                .or_insert_with(create_fn)
                .clone(),
            DiScope::Transient => create_fn(),
        }
    }

    /// Check if a type has a binding in the current profile.
    pub fn has_binding(&self, type_name: &str, module_path: &str, attrs: &[String]) -> bool {
        let ctx = create_di_match_context(type_name, module_path, attrs);
        self.config
            .select_binding(&self.active_profile, &ctx)
            .ok()
            .flatten()
            .is_some()
    }

    /// Get the active profile name.
    pub fn active_profile(&self) -> &str {
        &self.active_profile
    }
}

/// Typed dependency graph for compile-time analysis.
#[derive(Debug, Clone, Default)]
pub struct DependencyGraph {
    /// Map of type name -> dependencies (parameter types)
    dependencies: HashMap<String, Vec<String>>,
    /// Map of type name -> implementations
    implementations: HashMap<String, Vec<String>>,
}

impl DependencyGraph {
    /// Add a dependency edge: `from_type` depends on `param_type`.
    pub fn add_dependency(&mut self, from_type: String, param_type: String) {
        self.dependencies
            .entry(from_type)
            .or_insert_with(Vec::new)
            .push(param_type);
    }

    /// Add an implementation: `impl_type` implements `trait_type`.
    pub fn add_implementation(&mut self, trait_type: String, impl_type: String) {
        self.implementations
            .entry(trait_type)
            .or_insert_with(Vec::new)
            .push(impl_type);
    }

    /// Get dependencies for a type.
    pub fn get_dependencies(&self, type_name: &str) -> Option<&[String]> {
        self.dependencies.get(type_name).map(|v| v.as_slice())
    }

    /// Get implementations for a trait/type.
    pub fn get_implementations(&self, trait_name: &str) -> Option<&[String]> {
        self.implementations.get(trait_name).map(|v| v.as_slice())
    }

    /// Check for circular dependencies using DFS.
    pub fn check_circular(&self, start_type: &str) -> Option<Vec<String>> {
        let mut visited = HashMap::new();
        let mut path = Vec::new();
        self.dfs_check(start_type, &mut visited, &mut path)
    }

    fn dfs_check(
        &self,
        current: &str,
        visited: &mut HashMap<String, bool>,
        path: &mut Vec<String>,
    ) -> Option<Vec<String>> {
        // If we've seen this node in the current path, we have a cycle
        if path.contains(&current.to_string()) {
            path.push(current.to_string());
            return Some(path.clone());
        }

        // If we've already fully explored this node, skip it
        if visited.get(current) == Some(&true) {
            return None;
        }

        path.push(current.to_string());

        if let Some(deps) = self.dependencies.get(current) {
            for dep in deps {
                if let Some(cycle) = self.dfs_check(dep, visited, path) {
                    return Some(cycle);
                }
            }
        }

        path.pop();
        visited.insert(current.to_string(), true);
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_predicate_basic() {
        let pred = predicate_parser::parse_predicate("pc{ type(Foo) & !attr(test) }").unwrap();
        let attrs = vec!["release".to_string()];
        let ctx = create_di_match_context("Foo", "app.core", &attrs);
        assert!(pred.matches(&ctx));
    }

    #[test]
    fn parse_di_config_basic() {
        let toml: toml::Value = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
  { on = "pc{ type(Foo) }", impl = "Bar", scope = "Singleton", priority = 10 }
]
"#
        .parse()
        .unwrap();

        let config = parse_di_config(&toml).unwrap().unwrap();
        assert_eq!(config.mode, DiMode::Hybrid);
        let profile = config.profiles.get("default").unwrap();
        assert_eq!(profile.bindings.len(), 1);
        assert_eq!(profile.bindings[0].impl_type, "Bar");
        assert_eq!(profile.bindings[0].priority, 10);
        assert_eq!(profile.bindings[0].scope, DiScope::Singleton);
    }

    #[test]
    fn match_pattern_segments() {
        use crate::predicate::match_pattern;
        assert!(match_pattern("app.**", "app.core.user"));
        assert!(match_pattern("app.*.user", "app.core.user"));
        assert!(!match_pattern("app.*.user", "app.core.auth.user"));
        assert!(match_pattern("app.service*", "app.service_v2"));
    }

    #[test]
    fn di_container_resolve_type() {
        let toml: toml::Value = r#"
[di]
mode = "hybrid"

[di.profiles.test]
bindings = [
  { on = "pc{ type(UserRepository) }", impl = "MockUserRepository", scope = "Singleton", priority = 10 }
]
"#
        .parse()
        .unwrap();

        let config = parse_di_config(&toml).unwrap().unwrap();
        let container = DiContainer::new(config, "test".to_string());

        let result = container
            .resolve_type("UserRepository", "app.domain", &[])
            .unwrap();

        assert!(result.is_some());
        let (impl_type, scope) = result.unwrap();
        assert_eq!(impl_type, "MockUserRepository");
        assert_eq!(scope, DiScope::Singleton);
    }

    #[test]
    fn di_container_no_binding() {
        let toml: toml::Value = r#"
[di]
mode = "hybrid"

[di.profiles.test]
bindings = []
"#
        .parse()
        .unwrap();

        let config = parse_di_config(&toml).unwrap().unwrap();
        let container = DiContainer::new(config, "test".to_string());

        let result = container
            .resolve_type("UserRepository", "app.domain", &[])
            .unwrap();

        assert!(result.is_none());
    }

    #[test]
    fn dependency_graph_circular_detection() {
        let mut graph = DependencyGraph::default();

        // Create a circular dependency: A -> B -> C -> A
        graph.add_dependency("A".to_string(), "B".to_string());
        graph.add_dependency("B".to_string(), "C".to_string());
        graph.add_dependency("C".to_string(), "A".to_string());

        let cycle = graph.check_circular("A");
        assert!(cycle.is_some());
        let cycle_path = cycle.unwrap();
        assert!(cycle_path.contains(&"A".to_string()));
        assert!(cycle_path.contains(&"B".to_string()));
        assert!(cycle_path.contains(&"C".to_string()));
    }

    #[test]
    fn dependency_graph_no_circular() {
        let mut graph = DependencyGraph::default();

        // Create a non-circular dependency: A -> B -> C
        graph.add_dependency("A".to_string(), "B".to_string());
        graph.add_dependency("B".to_string(), "C".to_string());

        let cycle = graph.check_circular("A");
        assert!(cycle.is_none());
    }

    #[test]
    fn dependency_graph_get_deps() {
        let mut graph = DependencyGraph::default();

        graph.add_dependency("OrderService".to_string(), "OrderRepository".to_string());
        graph.add_dependency("OrderService".to_string(), "Clock".to_string());

        let deps = graph.get_dependencies("OrderService").unwrap();
        assert_eq!(deps.len(), 2);
        assert!(deps.contains(&"OrderRepository".to_string()));
        assert!(deps.contains(&"Clock".to_string()));
    }

    #[test]
    fn dependency_graph_implementations() {
        let mut graph = DependencyGraph::default();

        graph.add_implementation(
            "UserRepository".to_string(),
            "SqlUserRepository".to_string(),
        );
        graph.add_implementation(
            "UserRepository".to_string(),
            "MockUserRepository".to_string(),
        );

        let impls = graph.get_implementations("UserRepository").unwrap();
        assert_eq!(impls.len(), 2);
        assert!(impls.contains(&"SqlUserRepository".to_string()));
        assert!(impls.contains(&"MockUserRepository".to_string()));
    }
}

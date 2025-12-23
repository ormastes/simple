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
                predicate.validate(PredicateContext::DependencyInjection)
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
}

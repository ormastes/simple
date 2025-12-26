//! Runtime AOP configuration parsing for interpreter-only around init support.

use crate::predicate::{MatchContext, Predicate, PredicateContext};
use crate::predicate_parser;

#[derive(Debug, Clone)]
pub struct AopConfig {
    pub runtime_enabled: bool,
    pub around: Vec<AopAroundRule>,
}

#[derive(Debug, Clone)]
pub struct AopAroundRule {
    pub predicate: Predicate,
    pub advice: String,
    pub priority: i64,
    pub order: usize,
    pub raw_predicate: String,
}

/// Helper to create a match context for AOP weaving.
pub fn create_aop_match_context<'a>(
    type_name: &'a str,
    module_path: &'a str,
    attrs: &'a [String],
) -> MatchContext<'a> {
    MatchContext::new()
        .with_type_name(type_name)
        .with_module_path(module_path)
        .with_attrs(attrs)
}

pub fn parse_aop_config(toml: &toml::Value) -> Result<Option<AopConfig>, String> {
    let Some(aspects_table) = toml.get("aspects").and_then(|v| v.as_table()) else {
        return Ok(None);
    };
    let Some(runtime_table) = aspects_table.get("runtime").and_then(|v| v.as_table()) else {
        return Ok(None);
    };

    let runtime_enabled = runtime_table
        .get("enabled")
        .and_then(|v| v.as_bool())
        .unwrap_or(true);

    let around_values = match runtime_table.get("around") {
        None => Vec::new(),
        Some(value) => value
            .as_array()
            .ok_or_else(|| "aspects.runtime.around must be an array".to_string())?
            .clone(),
    };

    let mut around = Vec::new();
    for (idx, rule_val) in around_values.iter().enumerate() {
        let rule = rule_val.as_table().ok_or_else(|| {
            format!("aspects.runtime.around[{}] must be a table", idx)
        })?;

        let predicate_raw = rule
            .get("on")
            .or_else(|| rule.get("predicate"))
            .and_then(|v| v.as_str())
            .ok_or_else(|| {
                format!("aspects.runtime.around[{}] missing 'on' predicate", idx)
            })?;
        let advice = rule
            .get("use")
            .or_else(|| rule.get("advice"))
            .and_then(|v| v.as_str())
            .ok_or_else(|| {
                format!("aspects.runtime.around[{}] missing 'use' advice", idx)
            })?;

        let priority = rule
            .get("priority")
            .and_then(|v| v.as_integer())
            .unwrap_or(0);

        let predicate = predicate_parser::parse_predicate(predicate_raw)?;
        // Validate that the predicate is legal for weaving context
        predicate.validate(PredicateContext::Weaving)
            .map_err(|e| format!("invalid predicate for AOP weaving: {}", e))?;
        around.push(AopAroundRule {
            predicate,
            advice: advice.to_string(),
            priority,
            order: idx,
            raw_predicate: predicate_raw.to_string(),
        });
    }

    Ok(Some(AopConfig {
        runtime_enabled,
        around,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_runtime_aop_config() {
        let toml: toml::Value = r#"
[aspects.runtime]
enabled = true
around = [
  { on = "pc{ init(Foo) }", use = "around_fn", priority = 10 }
]
"#
        .parse()
        .expect("parse toml");
        let config = parse_aop_config(&toml).expect("parse aop");
        let config = config.expect("config present");
        assert!(config.runtime_enabled);
        assert_eq!(config.around.len(), 1);
        let ctx = create_aop_match_context("Foo", "Foo", &[]);
        assert!(config.around[0].predicate.matches(&ctx));
    }
}

//! Runtime AOP configuration parsing for interpreter-only around init support.

use crate::predicate::{MatchContext, Predicate, PredicateContext};
use crate::predicate_parser;

#[derive(Debug, Clone)]
pub struct AopConfig {
    pub runtime_enabled: bool,
    pub loads: Vec<String>,
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
pub fn create_aop_match_context<'a>(type_name: &'a str, module_path: &'a str, attrs: &'a [String]) -> MatchContext<'a> {
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

    let runtime_enabled = runtime_table.get("enabled").and_then(|v| v.as_bool()).unwrap_or(true);
    let loads = parse_string_or_array(
        runtime_table.get("load").or_else(|| runtime_table.get("loads")),
        "aspects.runtime.load",
    )?;
    for path in &loads {
        validate_local_child_config_path(path)?;
    }

    let around_values = match runtime_table.get("around") {
        None => Vec::new(),
        Some(value) => value
            .as_array()
            .ok_or_else(|| "aspects.runtime.around must be an array".to_string())?
            .clone(),
    };

    let mut around = Vec::new();
    for (idx, rule_val) in around_values.iter().enumerate() {
        let rule = rule_val
            .as_table()
            .ok_or_else(|| format!("aspects.runtime.around[{}] must be a table", idx))?;

        let predicate_raw = rule
            .get("on")
            .or_else(|| rule.get("predicate"))
            .and_then(|v| v.as_str())
            .ok_or_else(|| format!("aspects.runtime.around[{}] missing 'on' predicate", idx))?;
        let advice = rule
            .get("use")
            .or_else(|| rule.get("advice"))
            .and_then(|v| v.as_str())
            .ok_or_else(|| format!("aspects.runtime.around[{}] missing 'use' advice", idx))?;

        let priority = rule.get("priority").and_then(|v| v.as_integer()).unwrap_or(0);

        let predicate = predicate_parser::parse_predicate(predicate_raw)?;
        // Validate that the predicate is legal for weaving context
        predicate
            .validate(PredicateContext::Weaving)
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
        loads,
        around,
    }))
}

fn parse_string_or_array(value: Option<&toml::Value>, field: &str) -> Result<Vec<String>, String> {
    match value {
        None => Ok(Vec::new()),
        Some(v) => {
            if let Some(s) = v.as_str() {
                return Ok(vec![s.to_string()]);
            }
            let arr = v
                .as_array()
                .ok_or_else(|| format!("{} must be a string or array of strings", field))?;
            arr.iter()
                .enumerate()
                .map(|(idx, item)| {
                    item.as_str()
                        .map(|s| s.to_string())
                        .ok_or_else(|| format!("{}[{}] must be a string", field, idx))
                })
                .collect()
        }
    }
}

pub fn validate_local_child_config_path(path: &str) -> Result<(), String> {
    if path.is_empty() {
        return Err("AOP config load path cannot be empty".to_string());
    }
    if path.starts_with('/') || path.starts_with('\\') || path.starts_with('~') {
        return Err(format!("AOP config load path '{}' must be relative", path));
    }
    if path.contains(':') {
        return Err(format!(
            "AOP config load path '{}' must not contain a drive or scheme",
            path
        ));
    }
    for part in path.split(['/', '\\']) {
        if part == ".." {
            return Err(format!(
                "AOP config load path '{}' cannot escape the current directory",
                path
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_runtime_aop_config() {
        let toml: toml::Value = r#"
[aspects.runtime]
enabled = true
load = "config/aop.sdn"
around = [
  { on = "pc{ init(Foo) }", use = "around_fn", priority = 10 }
]
"#
        .parse()
        .expect("parse toml");
        let config = parse_aop_config(&toml).expect("parse aop");
        let config = config.expect("config present");
        assert!(config.runtime_enabled);
        assert_eq!(config.loads, vec!["config/aop.sdn"]);
        assert_eq!(config.around.len(), 1);
        let ctx = create_aop_match_context("Foo", "Foo", &[]);
        assert!(config.around[0].predicate.matches(&ctx));
    }

    #[test]
    fn reject_aop_load_paths_outside_current_tree() {
        for path in [
            "/tmp/aop.sdn",
            "../aop.sdn",
            "config/../secret.sdn",
            "C:\\temp\\aop.sdn",
            "https://x/aop.sdn",
        ] {
            assert!(
                validate_local_child_config_path(path).is_err(),
                "path should be rejected: {}",
                path
            );
        }
        assert!(validate_local_child_config_path("config/aop.sdn").is_ok());
        assert!(validate_local_child_config_path("./config/aop.sdn").is_ok());
    }
}

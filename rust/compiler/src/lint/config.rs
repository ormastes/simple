//! Lint configuration and level management.

use super::types::{LintLevel, LintName};
use simple_parser::ast::{Attribute, Expr};
use std::collections::HashMap;

/// Lint configuration for a scope (module, function, etc.)
#[derive(Debug, Clone, Default)]
pub struct LintConfig {
    /// Overridden lint levels
    levels: HashMap<LintName, LintLevel>,
}

impl LintConfig {
    pub fn new() -> Self {
        Self::default()
    }

    /// Load lint configuration from a simple.sdn file
    ///
    /// Expected format:
    /// ```sdn
    /// [lints]
    /// primitive_api = "deny"
    /// bare_bool = "warn"
    /// ```
    pub fn from_sdn_file(path: &std::path::Path) -> Result<Self, String> {
        use std::fs;

        let content = fs::read_to_string(path).map_err(|e| format!("Failed to read lint config: {}", e))?;

        Self::from_sdn_string(&content)
    }

    /// Parse lint configuration from SDN string
    pub fn from_sdn_string(content: &str) -> Result<Self, String> {
        let mut config = Self::new();
        let mut in_lints_section = false;

        for line in content.lines() {
            let line = line.trim();

            // Skip empty lines and comments
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            // Check for [lints] section
            if line == "[lints]" {
                in_lints_section = true;
                continue;
            }

            // Check for other sections (exit lints section)
            if line.starts_with('[') && line.ends_with(']') {
                in_lints_section = false;
                continue;
            }

            // Parse lint = "level" entries
            if in_lints_section {
                if let Some((lint_name, level_str)) = line.split_once('=') {
                    let lint_name = lint_name.trim();
                    let level_str = level_str.trim().trim_matches('"').trim_matches('\'');

                    if let Some(lint) = LintName::from_str(lint_name) {
                        if let Some(level) = LintLevel::from_str(level_str) {
                            config.set_level(lint, level);
                        } else {
                            return Err(format!("Invalid lint level '{}' for lint '{}'", level_str, lint_name));
                        }
                    } else {
                        // Unknown lint name - could be a warning in the future
                        eprintln!("Warning: Unknown lint name '{}'", lint_name);
                    }
                }
            }
        }

        Ok(config)
    }

    /// Set the level for a specific lint
    pub fn set_level(&mut self, lint: LintName, level: LintLevel) {
        self.levels.insert(lint, level);
    }

    /// Get the effective level for a lint
    pub fn get_level(&self, lint: LintName) -> LintLevel {
        self.levels.get(&lint).copied().unwrap_or_else(|| lint.default_level())
    }

    /// Parse lint attributes and update config
    /// Handles: #[allow(lint)], #[warn(lint)], #[deny(lint)]
    pub fn apply_attributes(&mut self, attributes: &[Attribute]) {
        for attr in attributes {
            let level = match attr.name.as_str() {
                "allow" => LintLevel::Allow,
                "warn" => LintLevel::Warn,
                "deny" => LintLevel::Deny,
                _ => continue,
            };

            // Parse lint names from args: #[deny(primitive_api, bare_bool)]
            if let Some(ref args) = attr.args {
                for arg in args {
                    if let Expr::Identifier(lint_name) = arg {
                        // Handle meta-lint "unknown_annotation" which suppresses both
                        if lint_name == "unknown_annotation" {
                            self.set_level(LintName::UnknownDecorator, level);
                            self.set_level(LintName::UnknownAttribute, level);
                        } else if let Some(lint) = LintName::from_str(lint_name) {
                            self.set_level(lint, level);
                        }
                    }
                }
            }
        }
    }

    /// Create a child config that inherits from this one
    pub fn child(&self) -> Self {
        Self {
            levels: self.levels.clone(),
        }
    }
}

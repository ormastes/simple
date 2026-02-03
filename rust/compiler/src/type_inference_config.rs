//! Type inference configuration for empty collections.
//!
//! This module provides configuration for default types when type inference
//! cannot determine the element type (e.g., empty arrays `[]`).
//!
//! Configuration can be set at:
//! 1. Project level via `simple.toml` `[type_inference]` section
//! 2. Module level via `@type_config` directive in `__init__.spl`

use crate::hir::TypeId;
use std::collections::HashMap;
use std::path::Path;

/// Type inference configuration
#[derive(Debug, Clone)]
pub struct TypeInferenceConfig {
    /// Default element type for empty arrays `[]`
    pub empty_array_default: TypeId,
    /// Default element type for empty SIMD vectors
    pub empty_vector_default: TypeId,
    /// Default key type for empty dicts `{}`
    pub empty_dict_key_default: TypeId,
    /// Default value type for empty dicts `{}`
    pub empty_dict_value_default: TypeId,
    /// If true, require explicit type annotation for empty collections
    pub strict_empty_collections: bool,
}

impl Default for TypeInferenceConfig {
    fn default() -> Self {
        Self {
            // Default to i32 for arrays (most common numeric type)
            empty_array_default: TypeId::I32,
            // Default to f64 for vectors (common for SIMD/math)
            empty_vector_default: TypeId::F64,
            // Default to String keys for dicts
            empty_dict_key_default: TypeId::STRING,
            // Default to Any values for dicts
            empty_dict_value_default: TypeId::ANY,
            // Don't require explicit annotations by default
            strict_empty_collections: false,
        }
    }
}

impl TypeInferenceConfig {
    /// Create a new config with default settings
    pub fn new() -> Self {
        Self::default()
    }

    /// Create config that requires explicit type annotations
    pub fn strict() -> Self {
        Self {
            strict_empty_collections: true,
            ..Self::default()
        }
    }

    /// Parse type inference configuration from TOML table
    ///
    /// Expected format in simple.toml:
    /// ```toml
    /// [type_inference]
    /// empty_array_default = "i32"
    /// empty_vector_default = "f64"
    /// empty_dict_key_default = "text"
    /// empty_dict_value_default = "any"
    /// strict_empty_collections = false
    /// ```
    pub fn from_toml(table: &toml::value::Table) -> Result<Self, String> {
        let mut config = Self::default();

        if let Some(v) = table.get("empty_array_default") {
            config.empty_array_default = parse_type_id(v.as_str().ok_or("expected string")?)?;
        }

        if let Some(v) = table.get("empty_vector_default") {
            config.empty_vector_default = parse_type_id(v.as_str().ok_or("expected string")?)?;
        }

        if let Some(v) = table.get("empty_dict_key_default") {
            config.empty_dict_key_default = parse_type_id(v.as_str().ok_or("expected string")?)?;
        }

        if let Some(v) = table.get("empty_dict_value_default") {
            config.empty_dict_value_default = parse_type_id(v.as_str().ok_or("expected string")?)?;
        }

        if let Some(v) = table.get("strict_empty_collections") {
            config.strict_empty_collections = v.as_bool().ok_or("expected boolean")?;
        }

        Ok(config)
    }

    /// Parse from SDN string (for __init__.spl @type_config)
    ///
    /// Expected format:
    /// ```simple
    /// @type_config(empty_array: i32, empty_vector: f64)
    /// ```
    pub fn from_attribute_args(args: &HashMap<String, String>) -> Result<Self, String> {
        let mut config = Self::default();

        if let Some(v) = args.get("empty_array") {
            config.empty_array_default = parse_type_id(v)?;
        }

        if let Some(v) = args.get("empty_vector") {
            config.empty_vector_default = parse_type_id(v)?;
        }

        if let Some(v) = args.get("empty_dict_key") {
            config.empty_dict_key_default = parse_type_id(v)?;
        }

        if let Some(v) = args.get("empty_dict_value") {
            config.empty_dict_value_default = parse_type_id(v)?;
        }

        if let Some(v) = args.get("strict") {
            config.strict_empty_collections = v == "true";
        }

        Ok(config)
    }

    /// Merge module-level config over project-level config
    pub fn merge(&self, module_config: &TypeInferenceConfig) -> TypeInferenceConfig {
        // Module config takes precedence where set
        // For now, just clone module config (full override)
        module_config.clone()
    }

    /// Load type inference config from an SDN file
    ///
    /// Expected format (type_defaults.sdn):
    /// ```sdn
    /// type_inference |setting, value|
    ///     empty_array, i32
    ///     empty_vector, f64
    ///     strict, false
    /// ```
    pub fn from_sdn_file(path: &Path) -> Result<Self, String> {
        let content = std::fs::read_to_string(path).map_err(|e| format!("failed to read type_defaults.sdn: {}", e))?;
        Self::from_sdn_string(&content)
    }

    /// Parse type inference config from SDN string
    pub fn from_sdn_string(content: &str) -> Result<Self, String> {
        let mut config = Self::default();

        // Simple key-value parsing for SDN table format
        for line in content.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') || line.starts_with('|') {
                continue;
            }
            // Skip table header line
            if line.starts_with("type_inference") {
                continue;
            }
            // Parse "key, value" rows
            if let Some((key, value)) = line.split_once(',') {
                let key = key.trim();
                let value = value.trim();
                match key {
                    "empty_array" | "empty_array_default" => {
                        config.empty_array_default = parse_type_id(value)?;
                    }
                    "empty_vector" | "empty_vector_default" => {
                        config.empty_vector_default = parse_type_id(value)?;
                    }
                    "empty_dict_key" | "empty_dict_key_default" => {
                        config.empty_dict_key_default = parse_type_id(value)?;
                    }
                    "empty_dict_value" | "empty_dict_value_default" => {
                        config.empty_dict_value_default = parse_type_id(value)?;
                    }
                    "strict" | "strict_empty_collections" => {
                        config.strict_empty_collections = value == "true";
                    }
                    _ => {} // Ignore unknown keys
                }
            }
        }

        Ok(config)
    }

    /// Try to load module-level config from a directory
    ///
    /// Looks for `type_defaults.sdn` in the given directory.
    /// Returns None if the file doesn't exist.
    pub fn try_load_for_directory(dir: &Path) -> Option<Self> {
        let config_path = dir.join("type_defaults.sdn");
        if config_path.exists() {
            match Self::from_sdn_file(&config_path) {
                Ok(config) => Some(config),
                Err(e) => {
                    tracing::warn!("Failed to load type_defaults.sdn: {}", e);
                    None
                }
            }
        } else {
            None
        }
    }
}

/// Parse a type name string to TypeId
fn parse_type_id(name: &str) -> Result<TypeId, String> {
    match name.to_lowercase().as_str() {
        "void" | "unit" | "()" => Ok(TypeId::VOID),
        "bool" => Ok(TypeId::BOOL),
        "i8" => Ok(TypeId::I8),
        "i16" => Ok(TypeId::I16),
        "i32" | "int" => Ok(TypeId::I32),
        "i64" | "long" => Ok(TypeId::I64),
        "u8" | "byte" => Ok(TypeId::U8),
        "u16" => Ok(TypeId::U16),
        "u32" | "uint" => Ok(TypeId::U32),
        "u64" | "ulong" => Ok(TypeId::U64),
        "f32" | "float" => Ok(TypeId::F32),
        "f64" | "double" => Ok(TypeId::F64),
        "text" | "string" | "str" => Ok(TypeId::STRING),
        "nil" | "null" | "none" => Ok(TypeId::NIL),
        "any" | "dynamic" => Ok(TypeId::ANY),
        "char" => Ok(TypeId::CHAR),
        _ => Err(format!("unknown type name: {}", name)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = TypeInferenceConfig::default();
        assert_eq!(config.empty_array_default, TypeId::I32);
        assert_eq!(config.empty_vector_default, TypeId::F64);
        assert!(!config.strict_empty_collections);
    }

    #[test]
    fn test_parse_type_id() {
        assert_eq!(parse_type_id("i32").unwrap(), TypeId::I32);
        assert_eq!(parse_type_id("int").unwrap(), TypeId::I32);
        assert_eq!(parse_type_id("text").unwrap(), TypeId::STRING);
        assert_eq!(parse_type_id("any").unwrap(), TypeId::ANY);
        assert!(parse_type_id("invalid").is_err());
    }

    #[test]
    fn test_strict_config() {
        let config = TypeInferenceConfig::strict();
        assert!(config.strict_empty_collections);
    }
}

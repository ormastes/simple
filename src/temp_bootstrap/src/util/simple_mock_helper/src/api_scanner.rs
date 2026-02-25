//! simple_mock_helper::api_scanner
//!
//! Scans Rust source files to extract public API (structs, methods, functions).
//! Generates or updates public_api.yml automatically.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

use serde::{Deserialize, Serialize};

/// Scanned public API from source code.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ScannedApi {
    /// Types (struct/enum) with their public methods
    pub types: BTreeMap<String, ScannedType>,
    /// Standalone public functions
    pub public_functions: BTreeMap<String, Vec<String>>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ScannedType {
    pub methods: Vec<String>,
}

/// Scan a directory tree for Rust source files and extract public API.
pub fn scan_directory(root: &Path) -> anyhow::Result<ScannedApi> {
    let mut api = ScannedApi::default();

    scan_dir_recursive(root, &mut api)?;

    Ok(api)
}

fn scan_dir_recursive(dir: &Path, api: &mut ScannedApi) -> anyhow::Result<()> {
    if !dir.is_dir() {
        return Ok(());
    }

    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();

        // Skip target, tests, and hidden directories
        if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
            if name.starts_with('.') || name == "target" || name == "tests" {
                continue;
            }
        }

        if path.is_dir() {
            scan_dir_recursive(&path, api)?;
        } else if path.extension().map_or(false, |ext| ext == "rs") {
            scan_rust_file(&path, api)?;
        }
    }

    Ok(())
}

/// Scan a single Rust file for public API.
fn scan_rust_file(path: &Path, api: &mut ScannedApi) -> anyhow::Result<()> {
    let content = fs::read_to_string(path)?;

    // Extract crate name from path (e.g., src/driver/src/runner.rs -> simple_driver)
    let crate_name = extract_crate_name(path);

    // Track current impl block
    let mut current_impl_type: Option<String> = None;
    let mut brace_depth = 0;
    let mut in_impl_block = false;

    for line in content.lines() {
        let trimmed = line.trim();

        // Track brace depth for impl blocks
        brace_depth += line.matches('{').count() as i32;
        brace_depth -= line.matches('}').count() as i32;

        if brace_depth == 0 {
            in_impl_block = false;
            current_impl_type = None;
        }

        // Detect impl blocks: `impl TypeName {` or `impl TypeName for Trait {`
        if trimmed.starts_with("impl ") && !trimmed.contains(" for ") {
            if let Some(type_name) = extract_impl_type(trimmed) {
                current_impl_type = Some(type_name);
                in_impl_block = true;
            }
        }

        // Detect public struct/enum definitions
        if trimmed.starts_with("pub struct ") || trimmed.starts_with("pub enum ") {
            if let Some(type_name) = extract_type_name(trimmed) {
                let full_name = format!("{}::{}", crate_name, type_name);
                api.types.entry(full_name).or_default();
            }
        }

        // Detect public functions
        if trimmed.starts_with("pub fn ") || trimmed.starts_with("pub async fn ") {
            if let Some(fn_name) = extract_fn_name(trimmed) {
                if in_impl_block {
                    // Method on a type
                    if let Some(ref type_name) = current_impl_type {
                        let full_type = format!("{}::{}", crate_name, type_name);
                        let entry = api.types.entry(full_type).or_default();
                        if !entry.methods.contains(&fn_name) {
                            entry.methods.push(fn_name);
                        }
                    }
                } else {
                    // Standalone function
                    let funcs = api.public_functions.entry(crate_name.clone()).or_default();
                    if !funcs.contains(&fn_name) {
                        funcs.push(fn_name);
                    }
                }
            }
        }
    }

    Ok(())
}

/// Extract crate name from file path.
fn extract_crate_name(path: &Path) -> String {
    // Look for src/<crate>/src pattern
    let path_str = path.to_string_lossy();

    // Try to find crate name from path like "src/driver/src/runner.rs"
    if let Some(caps) = path_str.find("/src/") {
        let after = &path_str[caps + 5..];
        if let Some(next_slash) = after.find('/') {
            let crate_dir = &after[..next_slash];
            return format!("simple_{}", crate_dir);
        }
    }

    // Fallback: use parent directory name
    path.parent()
        .and_then(|p| p.file_name())
        .and_then(|n| n.to_str())
        .map(|s| s.to_string())
        .unwrap_or_else(|| "unknown".to_string())
}

/// Extract type name from impl line.
/// Extract identifier from line, stopping at first delimiter
fn extract_identifier(line: &str, delimiters: &[char]) -> Option<String> {
    let type_name = delimiters
        .iter()
        .filter_map(|&c| line.find(c))
        .min()
        .map(|idx| &line[..idx])
        .unwrap_or(line);

    let type_name = type_name.trim();
    if type_name.is_empty() {
        None
    } else {
        Some(type_name.to_string())
    }
}

fn extract_impl_type(line: &str) -> Option<String> {
    // impl TypeName { or impl TypeName<T> {
    let line = line.trim_start_matches("impl ").trim();
    let result = extract_identifier(line, &['<', '{', ' ']);
    // Filter out Default trait impl
    result.filter(|s| s != "Default")
}

/// Extract type name from struct/enum definition.
fn extract_type_name(line: &str) -> Option<String> {
    let line = line
        .trim_start_matches("pub struct ")
        .trim_start_matches("pub enum ")
        .trim();
    extract_identifier(line, &['<', '{', '(', ';', ' '])
}

/// Extract function name from fn definition.
fn extract_fn_name(line: &str) -> Option<String> {
    let line = line.trim_start_matches("pub async fn ");
    let line = line.trim_start_matches("pub fn ");
    let line = line.trim();

    let fn_name = if let Some(idx) = line.find('<') {
        &line[..idx]
    } else if let Some(idx) = line.find('(') {
        &line[..idx]
    } else {
        line
    };

    let fn_name = fn_name.trim();
    if fn_name.is_empty() {
        None
    } else {
        Some(fn_name.to_string())
    }
}

/// Generate YAML content from scanned API.
pub fn generate_yaml(api: &ScannedApi) -> String {
    let mut yaml = String::new();
    yaml.push_str("# Auto-generated public API specification\n");
    yaml.push_str("# Generated by: smh_coverage --scan-source\n");
    yaml.push_str("# \n");
    yaml.push_str("# For Integration Tests: public functions on class/struct\n");
    yaml.push_str("# For System Tests: class/struct methods\n\n");

    // Public functions section
    if !api.public_functions.is_empty() {
        yaml.push_str("public_functions:\n");
        for (crate_name, funcs) in &api.public_functions {
            yaml.push_str(&format!("  {}:\n", crate_name));
            for func in funcs {
                yaml.push_str(&format!("    - {}\n", func));
            }
        }
        yaml.push('\n');
    }

    // Types section
    if !api.types.is_empty() {
        yaml.push_str("types:\n");
        for (type_name, type_spec) in &api.types {
            yaml.push_str(&format!("  {}:\n", type_name));
            yaml.push_str("    methods: [");
            yaml.push_str(&type_spec.methods.join(", "));
            yaml.push_str("]\n");
        }
    }

    yaml
}

/// Write YAML to file.
pub fn write_yaml(api: &ScannedApi, path: &Path) -> anyhow::Result<()> {
    let yaml = generate_yaml(api);
    fs::write(path, yaml)?;
    Ok(())
}

/// Load existing YAML and merge with scanned API.
pub fn merge_with_existing(
    scanned: &ScannedApi,
    existing_path: &Path,
) -> anyhow::Result<ScannedApi> {
    if !existing_path.exists() {
        return Ok(scanned.clone());
    }

    let existing_content = fs::read_to_string(existing_path)?;
    let existing: ScannedApi = serde_yaml::from_str(&existing_content)?;

    let mut merged = scanned.clone();

    // Merge types - keep existing methods that are still in source
    for (type_name, existing_type) in &existing.types {
        if let Some(scanned_type) = merged.types.get_mut(type_name) {
            // Keep order from existing, add new ones
            let scanned_methods: BTreeSet<_> = scanned_type.methods.iter().cloned().collect();
            let mut merged_methods = Vec::new();

            for method in &existing_type.methods {
                if scanned_methods.contains(method) {
                    merged_methods.push(method.clone());
                }
            }
            for method in &scanned_type.methods {
                if !merged_methods.contains(method) {
                    merged_methods.push(method.clone());
                }
            }
            scanned_type.methods = merged_methods;
        }
    }

    Ok(merged)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_impl_type() {
        assert_eq!(extract_impl_type("impl Foo {"), Some("Foo".to_string()));
        assert_eq!(extract_impl_type("impl Foo<T> {"), Some("Foo".to_string()));
        assert_eq!(extract_impl_type("impl Bar {"), Some("Bar".to_string()));
    }

    #[test]
    fn test_extract_type_name() {
        assert_eq!(
            extract_type_name("pub struct Foo {"),
            Some("Foo".to_string())
        );
        assert_eq!(
            extract_type_name("pub struct Bar<T> {"),
            Some("Bar".to_string())
        );
        assert_eq!(extract_type_name("pub enum Baz {"), Some("Baz".to_string()));
        assert_eq!(
            extract_type_name("pub struct Unit;"),
            Some("Unit".to_string())
        );
    }

    #[test]
    fn test_extract_fn_name() {
        assert_eq!(
            extract_fn_name("pub fn new() -> Self {"),
            Some("new".to_string())
        );
        assert_eq!(
            extract_fn_name("pub fn run<T>(x: T) {"),
            Some("run".to_string())
        );
        assert_eq!(
            extract_fn_name("pub async fn fetch() {"),
            Some("fetch".to_string())
        );
    }

    #[test]
    fn test_generate_yaml() {
        let mut api = ScannedApi::default();
        api.types.insert(
            "test::Foo".to_string(),
            ScannedType {
                methods: vec!["new".to_string(), "run".to_string()],
            },
        );
        api.public_functions
            .insert("test".to_string(), vec!["helper".to_string()]);

        let yaml = generate_yaml(&api);
        assert!(yaml.contains("types:"));
        assert!(yaml.contains("test::Foo:"));
        assert!(yaml.contains("methods: [new, run]"));
        assert!(yaml.contains("public_functions:"));
    }
}

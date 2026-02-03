//! Project context for multi-file compilation.
//!
//! This module provides project detection and context management
//! for compiling Simple projects with module resolution.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::aop_config::{parse_aop_config, AopConfig};
use crate::build_mode::DeterministicConfig;
use crate::di::{parse_di_config, DiConfig};
use crate::error::{codes, CompileError, ErrorContext};
use crate::hir::{LayoutAnchor, LayoutConfig, LayoutPhase};
use crate::lint::{LintConfig, LintLevel, LintName};
use crate::module_resolver::ModuleResolver;
use crate::type_inference_config::TypeInferenceConfig;

/// Project context holding all project-level configuration
#[derive(Debug)]
pub struct ProjectContext {
    /// Project root directory (where simple.toml lives)
    pub root: PathBuf,
    /// Source root directory (from simple.toml or default "src")
    pub source_root: PathBuf,
    /// Project name
    pub name: String,
    /// Module resolver for this project
    pub resolver: ModuleResolver,
    /// Enabled features
    pub features: HashSet<String>,
    /// Profile definitions: name -> (attributes, imports)
    pub profiles: HashMap<String, (Vec<String>, Vec<String>)>,
    /// Lint configuration from simple.toml
    pub lint_config: LintConfig,
    /// DI configuration from simple.toml
    pub di_config: Option<DiConfig>,
    /// Runtime AOP configuration from simple.toml
    pub aop_config: Option<AopConfig>,
    /// Deterministic build configuration from simple.toml
    pub deterministic: DeterministicConfig,
    /// Layout configuration for 4KB page locality optimization
    pub layout_config: Option<LayoutConfig>,
    /// Type inference configuration for empty collections
    pub type_inference_config: TypeInferenceConfig,
}

impl ProjectContext {
    /// Create a new project context from a project root directory
    pub fn new(root: PathBuf) -> Result<Self, CompileError> {
        let manifest_path = root.join("simple.toml");

        if manifest_path.exists() {
            Self::from_manifest(&root, &manifest_path)
        } else {
            // No manifest - use defaults
            Self::with_defaults(root)
        }
    }

    /// Create a project context with default settings
    fn with_defaults(root: PathBuf) -> Result<Self, CompileError> {
        let source_root = if root.join("src").exists() {
            root.join("src")
        } else {
            root.clone()
        };

        let name = root
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or("unnamed")
            .to_string();

        let resolver = ModuleResolver::new(root.clone(), source_root.clone());

        // Try to load layout.sdn if it exists
        let layout_config = Self::load_layout_config(&root);

        Ok(Self {
            root,
            source_root,
            name,
            resolver,
            features: HashSet::new(),
            profiles: HashMap::new(),
            lint_config: LintConfig::new(),
            di_config: None,
            aop_config: None,
            deterministic: DeterministicConfig::default(),
            layout_config,
            type_inference_config: TypeInferenceConfig::default(),
        })
    }

    /// Load layout configuration from layout.sdn if it exists
    fn load_layout_config(root: &Path) -> Option<LayoutConfig> {
        let layout_path = root.join("layout.sdn");
        if layout_path.exists() {
            match LayoutConfig::from_file(&layout_path) {
                Ok(config) => Some(config),
                Err(e) => {
                    tracing::warn!("Failed to load layout.sdn: {}", e);
                    None
                }
            }
        } else {
            None
        }
    }

    /// Create a project context from a manifest file
    fn from_manifest(root: &Path, manifest_path: &Path) -> Result<Self, CompileError> {
        let content = std::fs::read_to_string(manifest_path)
            .map_err(|e| CompileError::Io(format!("failed to read manifest: {}", e)))?;

        Self::parse_manifest(root, &content)
    }

    /// Parse a manifest string and create project context
    fn parse_manifest(root: &Path, content: &str) -> Result<Self, CompileError> {
        // Parse as TOML
        let toml: toml::Value = content
            .parse()
            .map_err(|e| crate::error::factory::invalid_config("manifest", &e))?;

        // Extract project/package section
        let project = toml.get("project").or_else(|| toml.get("package")).ok_or_else(|| {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("Add a [project] or [package] section to your manifest file");
            CompileError::semantic_with_context("manifest missing [project] or [package] section".to_string(), ctx)
        })?;

        // Get project name
        let name = project
            .get("name")
            .and_then(|v| v.as_str())
            .unwrap_or("unnamed")
            .to_string();

        // Get source root (default: "src")
        let source_root_str = project.get("root").and_then(|v| v.as_str()).unwrap_or("src");
        let source_root = root.join(source_root_str);

        // Parse features
        let mut features = HashSet::new();
        if let Some(features_table) = toml.get("features").and_then(|v| v.as_table()) {
            for (name, value) in features_table {
                if value.as_bool().unwrap_or(false) {
                    features.insert(name.clone());
                }
            }
        }

        // Parse profiles
        let mut profiles: HashMap<String, (Vec<String>, Vec<String>)> = HashMap::new();
        if let Some(profiles_table) = toml.get("profiles").and_then(|v| v.as_table()) {
            for (profile_name, profile_value) in profiles_table {
                let attrs = extract_string_array(profile_value, "attributes");
                let imports = extract_string_array(profile_value, "imports");
                profiles.insert(profile_name.clone(), (attrs, imports));
            }
        }

        // Parse lint configuration
        let mut lint_config = LintConfig::new();
        if let Some(lint_table) = toml.get("lint").and_then(|v| v.as_table()) {
            for (lint_name, level_value) in lint_table {
                if let Some(lint) = LintName::from_str(lint_name) {
                    if let Some(level_str) = level_value.as_str() {
                        if let Some(level) = LintLevel::from_str(level_str) {
                            lint_config.set_level(lint, level);
                        }
                    }
                }
            }
        }

        let di_config = parse_di_config(&toml).map_err(|e| crate::error::factory::invalid_config("di config", &e))?;
        let aop_config =
            parse_aop_config(&toml).map_err(|e| crate::error::factory::invalid_config("aop config", &e))?;

        // Parse deterministic build configuration
        let deterministic = if let Some(build_table) = toml.get("build").and_then(|v| v.as_table()) {
            let enabled = build_table
                .get("deterministic")
                .and_then(|v| v.as_bool())
                .unwrap_or(false);

            let timestamp = build_table
                .get("timestamp")
                .and_then(|v| v.as_str())
                .map(|s| s.to_string());

            let seed = build_table
                .get("seed")
                .and_then(|v| v.as_integer())
                .map(|n| n as u64)
                .unwrap_or(0);

            let normalize_paths = build_table
                .get("normalize_paths")
                .and_then(|v| v.as_bool())
                .unwrap_or(true);

            DeterministicConfig {
                enabled,
                timestamp,
                seed,
                normalize_paths,
            }
        } else {
            DeterministicConfig::default()
        };

        // Create resolver with features and profiles
        let resolver = ModuleResolver::new(root.to_path_buf(), source_root.clone())
            .with_features(features.clone())
            .with_profiles(profiles.clone());

        // Try to load layout.sdn if it exists
        let layout_config = Self::load_layout_config(root);

        // Parse type inference configuration
        let type_inference_config = if let Some(ti_table) = toml.get("type_inference").and_then(|v| v.as_table()) {
            TypeInferenceConfig::from_toml(ti_table)
                .map_err(|e| crate::error::factory::invalid_config("type_inference", &e))?
        } else {
            TypeInferenceConfig::default()
        };

        Ok(Self {
            root: root.to_path_buf(),
            source_root,
            name,
            resolver,
            features,
            profiles,
            lint_config,
            di_config,
            aop_config,
            deterministic,
            layout_config,
            type_inference_config,
        })
    }

    /// Create a context for single-file mode (no project)
    pub fn single_file(file_path: &Path) -> Self {
        let parent = file_path.parent().unwrap_or(Path::new(".")).to_path_buf();
        let name = file_path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("main")
            .to_string();

        Self {
            root: parent.clone(),
            source_root: parent.clone(),
            name,
            resolver: ModuleResolver::single_file(file_path),
            features: HashSet::new(),
            profiles: HashMap::new(),
            lint_config: LintConfig::new(),
            di_config: None,
            aop_config: None,
            deterministic: DeterministicConfig::default(),
            layout_config: None,
            type_inference_config: TypeInferenceConfig::default(),
        }
    }

    /// Detect project context by searching upward from a file
    ///
    /// Searches parent directories for simple.toml.
    /// If not found, returns single-file context.
    pub fn detect(file_path: &Path) -> Result<Self, CompileError> {
        let file_path = file_path.canonicalize().unwrap_or_else(|_| file_path.to_path_buf());

        // Search upward for simple.toml
        let mut current = file_path.parent();
        while let Some(dir) = current {
            let manifest = dir.join("simple.toml");
            if manifest.exists() {
                return Self::new(dir.to_path_buf());
            }
            current = dir.parent();
        }

        // No project found - use single-file mode
        Ok(Self::single_file(&file_path))
    }

    /// Check if a feature is enabled
    pub fn is_feature_enabled(&self, name: &str) -> bool {
        self.features.contains(name)
    }

    /// Get a profile definition
    pub fn get_profile(&self, name: &str) -> Option<&(Vec<String>, Vec<String>)> {
        self.profiles.get(name)
    }

    /// Get the main entry point file
    pub fn main_file(&self) -> PathBuf {
        self.source_root.join("main.spl")
    }

    /// Get the lint configuration
    pub fn lint_config(&self) -> &LintConfig {
        &self.lint_config
    }

    /// Get the layout configuration
    pub fn layout_config(&self) -> Option<&LayoutConfig> {
        self.layout_config.as_ref()
    }

    /// Get the layout phase for a function based on configuration
    pub fn get_layout_phase(&self, function_name: &str) -> LayoutPhase {
        if let Some(config) = &self.layout_config {
            config.get_phase(function_name)
        } else {
            LayoutPhase::Steady
        }
    }

    /// Check if a function is an anchor point
    pub fn is_layout_anchor(&self, function_name: &str) -> Option<LayoutAnchor> {
        self.layout_config.as_ref().and_then(|c| c.is_anchor(function_name))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_helpers::create_test_project;
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn test_detect_no_project() {
        let dir = create_test_project();
        let file = dir.path().join("test.spl");
        fs::write(&file, "main = 0").unwrap();

        let ctx = ProjectContext::detect(&file).unwrap();
        assert_eq!(ctx.name, "test");
        assert_eq!(ctx.root.canonicalize().ok(), dir.path().canonicalize().ok());
    }

    #[test]
    fn test_detect_with_project() {
        let dir = create_test_project();
        let manifest = r#"
[project]
name = "myproject"
root = "src"

[features]
strict_null = true
"#;
        fs::write(dir.path().join("simple.toml"), manifest).unwrap();

        let file = dir.path().join("src").join("main.spl");
        fs::write(&file, "main = 0").unwrap();

        let ctx = ProjectContext::detect(&file).unwrap();
        assert_eq!(ctx.name, "myproject");
        assert_eq!(
            ctx.source_root.canonicalize().ok(),
            dir.path().join("src").canonicalize().ok()
        );
        assert!(ctx.is_feature_enabled("strict_null"));
    }

    /// Helper to create test project context from TOML manifest
    fn create_test_project_with_manifest(manifest: &str) -> (TempDir, ProjectContext) {
        let dir = create_test_project();
        fs::write(dir.path().join("simple.toml"), manifest).unwrap();
        let ctx = ProjectContext::new(dir.path().to_path_buf()).unwrap();
        (dir, ctx)
    }

    #[test]
    fn test_parse_manifest_with_profiles() {
        let manifest = r#"
[project]
name = "server_app"
root = "src"

[profiles.server]
attributes = ["async", "strong"]
imports = ["crate.core.base.*", "crate.net.http.*"]

[profiles.embedded]
attributes = ["no_gc"]
imports = ["crate.core.base.*"]

[features]
strict_null = true
new_async = false
"#;
        let (_dir, ctx) = create_test_project_with_manifest(manifest);

        assert_eq!(ctx.name, "server_app");
        assert!(ctx.is_feature_enabled("strict_null"));
        assert!(!ctx.is_feature_enabled("new_async"));

        let server_profile = ctx.get_profile("server").unwrap();
        assert_eq!(server_profile.0, vec!["async", "strong"]);
        assert_eq!(server_profile.1, vec!["crate.core.base.*", "crate.net.http.*"]);

        let embedded_profile = ctx.get_profile("embedded").unwrap();
        assert_eq!(embedded_profile.0, vec!["no_gc"]);
    }

    #[test]
    fn test_single_file_mode() {
        let ctx = ProjectContext::single_file(Path::new("/tmp/test.spl"));
        assert_eq!(ctx.name, "test");
        assert_eq!(ctx.root, Path::new("/tmp"));
    }

    #[test]
    fn test_default_source_root() {
        let manifest = r#"
[project]
name = "myapp"
"#;
        let (dir, ctx) = create_test_project_with_manifest(manifest);
        assert_eq!(ctx.source_root, dir.path().join("src"));
    }

    #[test]
    fn test_package_alias() {
        // Test that [package] works as alias for [project]
        let dir = create_test_project();
        let manifest = r#"
[package]
name = "myapp"
version = "1.0.0"
"#;
        fs::write(dir.path().join("simple.toml"), manifest).unwrap();

        let ctx = ProjectContext::new(dir.path().to_path_buf()).unwrap();
        assert_eq!(ctx.name, "myapp");
    }

    #[test]
    fn test_lint_configuration() {
        let manifest = r#"
[project]
name = "myapp"

[lint]
primitive_api = "deny"
bare_bool = "allow"
"#;
        let (_dir, ctx) = create_test_project_with_manifest(manifest);
        assert_eq!(ctx.lint_config.get_level(LintName::PrimitiveApi), LintLevel::Deny);
        assert_eq!(ctx.lint_config.get_level(LintName::BareBool), LintLevel::Allow);
    }

    #[test]
    fn test_di_configuration() {
        let manifest = r#"
[project]
name = "myapp"

[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
  { on = "pc{ type(Foo) }", impl = "Bar", scope = "Singleton", priority = 10 }
]
"#;
        let (_dir, ctx) = create_test_project_with_manifest(manifest);
        let di = ctx.di_config.as_ref().expect("di config");
        let profile = di.profiles.get("default").unwrap();
        assert_eq!(profile.bindings.len(), 1);
        assert_eq!(profile.bindings[0].impl_type, "Bar");
        assert_eq!(profile.bindings[0].priority, 10);
    }

    #[test]
    fn test_lint_configuration_warn() {
        let manifest = r#"
[project]
name = "myapp"

[lint]
primitive_api = "warn"
"#;
        let (_dir, ctx) = create_test_project_with_manifest(manifest);
        assert_eq!(ctx.lint_config.get_level(LintName::PrimitiveApi), LintLevel::Warn);
        // bare_bool uses default (Warn)
        assert_eq!(ctx.lint_config.get_level(LintName::BareBool), LintLevel::Warn);
    }

    #[test]
    fn test_lint_default_without_section() {
        let manifest = r#"
[project]
name = "myapp"
"#;
        let (_dir, ctx) = create_test_project_with_manifest(manifest);
        // Without [lint] section, defaults apply
        assert_eq!(ctx.lint_config.get_level(LintName::PrimitiveApi), LintLevel::Warn);
    }
}

/// Helper to extract a string array from a TOML value
fn extract_string_array(value: &toml::Value, key: &str) -> Vec<String> {
    value
        .get(key)
        .and_then(|v| v.as_array())
        .map(|arr| arr.iter().filter_map(|v| v.as_str().map(String::from)).collect())
        .unwrap_or_default()
}

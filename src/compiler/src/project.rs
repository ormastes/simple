//! Project context for multi-file compilation.
//!
//! This module provides project detection and context management
//! for compiling Simple projects with module resolution.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use crate::error::CompileError;
use crate::module_resolver::ModuleResolver;

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

        Ok(Self {
            root,
            source_root,
            name,
            resolver,
            features: HashSet::new(),
            profiles: HashMap::new(),
        })
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
            .map_err(|e| CompileError::Semantic(format!("invalid manifest: {}", e)))?;

        // Extract project/package section
        let project = toml
            .get("project")
            .or_else(|| toml.get("package"))
            .ok_or_else(|| {
                CompileError::Semantic("manifest missing [project] or [package] section".into())
            })?;

        // Get project name
        let name = project
            .get("name")
            .and_then(|v| v.as_str())
            .unwrap_or("unnamed")
            .to_string();

        // Get source root (default: "src")
        let source_root_str = project
            .get("root")
            .and_then(|v| v.as_str())
            .unwrap_or("src");
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
                let attrs: Vec<String> = profile_value
                    .get("attributes")
                    .and_then(|v| v.as_array())
                    .map(|arr| {
                        arr.iter()
                            .filter_map(|v| v.as_str().map(String::from))
                            .collect()
                    })
                    .unwrap_or_default();

                let imports: Vec<String> = profile_value
                    .get("imports")
                    .and_then(|v| v.as_array())
                    .map(|arr| {
                        arr.iter()
                            .filter_map(|v| v.as_str().map(String::from))
                            .collect()
                    })
                    .unwrap_or_default();

                profiles.insert(profile_name.clone(), (attrs, imports));
            }
        }

        // Create resolver with features and profiles
        let resolver = ModuleResolver::new(root.to_path_buf(), source_root.clone())
            .with_features(features.clone())
            .with_profiles(profiles.clone());

        Ok(Self {
            root: root.to_path_buf(),
            source_root,
            name,
            resolver,
            features,
            profiles,
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
        }
    }

    /// Detect project context by searching upward from a file
    ///
    /// Searches parent directories for simple.toml.
    /// If not found, returns single-file context.
    pub fn detect(file_path: &Path) -> Result<Self, CompileError> {
        let file_path = file_path
            .canonicalize()
            .unwrap_or_else(|_| file_path.to_path_buf());

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
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    fn create_test_project() -> TempDir {
        let dir = TempDir::new().unwrap();
        let src = dir.path().join("src");
        fs::create_dir_all(&src).unwrap();
        dir
    }

    #[test]
    fn test_detect_no_project() {
        let dir = create_test_project();
        let file = dir.path().join("test.spl");
        fs::write(&file, "main = 0").unwrap();

        let ctx = ProjectContext::detect(&file).unwrap();
        assert_eq!(ctx.name, "test");
        assert_eq!(ctx.root, dir.path());
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
        assert_eq!(ctx.source_root, dir.path().join("src"));
        assert!(ctx.is_feature_enabled("strict_null"));
    }

    #[test]
    fn test_parse_manifest_with_profiles() {
        let dir = create_test_project();
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
        fs::write(dir.path().join("simple.toml"), manifest).unwrap();

        let ctx = ProjectContext::new(dir.path().to_path_buf()).unwrap();

        assert_eq!(ctx.name, "server_app");
        assert!(ctx.is_feature_enabled("strict_null"));
        assert!(!ctx.is_feature_enabled("new_async"));

        let server_profile = ctx.get_profile("server").unwrap();
        assert_eq!(server_profile.0, vec!["async", "strong"]);
        assert_eq!(
            server_profile.1,
            vec!["crate.core.base.*", "crate.net.http.*"]
        );

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
        let dir = create_test_project();
        let manifest = r#"
[project]
name = "myapp"
"#;
        fs::write(dir.path().join("simple.toml"), manifest).unwrap();

        let ctx = ProjectContext::new(dir.path().to_path_buf()).unwrap();
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
}

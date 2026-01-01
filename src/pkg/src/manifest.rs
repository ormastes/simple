//! Manifest (simple.toml) parsing and handling

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::Path;

use crate::error::{PkgError, PkgResult};

/// Project manifest (simple.toml)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Manifest {
    pub package: Package,
    #[serde(default)]
    pub dependencies: HashMap<String, Dependency>,
    #[serde(default, rename = "dev-dependencies")]
    pub dev_dependencies: HashMap<String, Dependency>,
    #[serde(default)]
    pub features: HashMap<String, Vec<String>>,
    #[serde(default)]
    pub registry: RegistryConfig,
    /// Lean verification configuration (#1876)
    #[serde(default)]
    pub verify: VerifyConfig,
}

/// Lean verification configuration (#1876)
///
/// Example in simple.toml:
/// ```toml
/// [verify]
/// enabled = true
/// lean_path = "/usr/local/bin/lean"
/// output_dir = "build/lean"
/// generate_stubs = true
/// modules = ["core", "math"]
/// ```
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VerifyConfig {
    /// Enable Lean verification for this package
    #[serde(default)]
    pub enabled: bool,
    /// Path to Lean executable (defaults to "lean" in PATH)
    #[serde(default)]
    pub lean_path: Option<String>,
    /// Output directory for generated Lean files (defaults to "build/lean")
    #[serde(default)]
    pub output_dir: Option<String>,
    /// Generate proof stubs (sorry) for unproven theorems
    #[serde(default = "default_generate_stubs")]
    pub generate_stubs: bool,
    /// Modules to verify (empty = all @verify modules)
    #[serde(default)]
    pub modules: Vec<String>,
    /// Check proofs with Lean (requires Lean 4 installed)
    #[serde(default)]
    pub check_proofs: bool,
    /// Strict mode: fail build on unproven theorems
    #[serde(default)]
    pub strict: bool,
}

fn default_generate_stubs() -> bool {
    true
}

impl Default for VerifyConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            lean_path: None,
            output_dir: None,
            generate_stubs: default_generate_stubs(),
            modules: Vec::new(),
            check_proofs: false,
            strict: false,
        }
    }
}

impl VerifyConfig {
    /// Get the Lean executable path
    pub fn lean_executable(&self) -> &str {
        self.lean_path.as_deref().unwrap_or("lean")
    }

    /// Get the output directory for Lean files
    pub fn lean_output_dir(&self) -> &str {
        self.output_dir.as_deref().unwrap_or("build/lean")
    }

    /// Check if a module should be verified
    pub fn should_verify_module(&self, module: &str) -> bool {
        if !self.enabled {
            return false;
        }
        if self.modules.is_empty() {
            return true; // Verify all modules
        }
        self.modules.iter().any(|m| module.starts_with(m))
    }
}

/// Package metadata
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Package {
    pub name: String,
    #[serde(default = "default_version")]
    pub version: String,
    #[serde(default)]
    pub authors: Vec<String>,
    #[serde(default)]
    pub description: Option<String>,
    #[serde(default)]
    pub license: Option<String>,
    #[serde(default)]
    pub repository: Option<String>,
    #[serde(default)]
    pub keywords: Vec<String>,
    #[serde(default = "default_main")]
    pub main: String,
}

fn default_version() -> String {
    "0.1.0".to_string()
}

fn default_main() -> String {
    "src/main.spl".to_string()
}

/// Dependency specification
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Dependency {
    /// Simple version string: `http = "1.0"`
    Version(String),
    /// Detailed specification
    Detailed(DependencyDetail),
}

/// Detailed dependency specification
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct DependencyDetail {
    #[serde(default)]
    pub version: Option<String>,
    #[serde(default)]
    pub git: Option<String>,
    #[serde(default)]
    pub branch: Option<String>,
    #[serde(default)]
    pub tag: Option<String>,
    #[serde(default)]
    pub rev: Option<String>,
    #[serde(default)]
    pub path: Option<String>,
    #[serde(default)]
    pub optional: bool,
    #[serde(default)]
    pub features: Vec<String>,
}

/// Registry configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegistryConfig {
    #[serde(default = "default_registry")]
    pub default: String,
}

fn default_registry() -> String {
    "https://github.com/simple-lang/registry".to_string()
}

impl Default for RegistryConfig {
    fn default() -> Self {
        RegistryConfig {
            default: default_registry(),
        }
    }
}

impl Manifest {
    /// Load manifest from a file
    pub fn load(path: &Path) -> PkgResult<Self> {
        let content = std::fs::read_to_string(path)
            .map_err(|_| PkgError::ManifestNotFound(path.display().to_string()))?;
        Self::parse(&content)
    }

    /// Parse manifest from string
    pub fn parse(content: &str) -> PkgResult<Self> {
        let manifest: Manifest = toml::from_str(content)?;
        Ok(manifest)
    }

    /// Save manifest to file
    pub fn save(&self, path: &Path) -> PkgResult<()> {
        let content = toml::to_string_pretty(self)?;
        std::fs::write(path, content)?;
        Ok(())
    }

    /// Create a new default manifest
    pub fn new(name: &str) -> Self {
        Manifest {
            package: Package {
                name: name.to_string(),
                version: "0.1.0".to_string(),
                authors: Vec::new(),
                description: None,
                license: Some("MIT".to_string()),
                repository: None,
                keywords: Vec::new(),
                main: "src/main.spl".to_string(),
            },
            dependencies: HashMap::new(),
            dev_dependencies: HashMap::new(),
            features: HashMap::new(),
            registry: RegistryConfig::default(),
            verify: VerifyConfig::default(),
        }
    }

    /// Check if verification is enabled for this package
    pub fn is_verification_enabled(&self) -> bool {
        self.verify.enabled
    }

    /// Add a dependency
    pub fn add_dependency(&mut self, name: &str, dep: Dependency) {
        self.dependencies.insert(name.to_string(), dep);
    }

    /// Remove a dependency
    pub fn remove_dependency(&mut self, name: &str) -> Option<Dependency> {
        self.dependencies.remove(name)
    }

    /// Check if a dependency exists
    pub fn has_dependency(&self, name: &str) -> bool {
        self.dependencies.contains_key(name)
    }
}

impl Dependency {
    /// Create a version dependency
    pub fn version(ver: &str) -> Self {
        Dependency::Version(ver.to_string())
    }

    /// Create a git dependency
    pub fn git(url: &str) -> Self {
        Dependency::Detailed(DependencyDetail {
            git: Some(url.to_string()),
            ..Default::default()
        })
    }

    /// Create a path dependency
    pub fn path(path: &str) -> Self {
        Dependency::Detailed(DependencyDetail {
            path: Some(path.to_string()),
            ..Default::default()
        })
    }

    /// Get the version string if this is a version dependency
    pub fn version_str(&self) -> Option<&str> {
        match self {
            Dependency::Version(v) => Some(v),
            Dependency::Detailed(d) => d.version.as_deref(),
        }
    }

    /// Check if this is a path dependency
    pub fn is_path(&self) -> bool {
        matches!(self, Dependency::Detailed(d) if d.path.is_some())
    }

    /// Check if this is a git dependency
    pub fn is_git(&self) -> bool {
        matches!(self, Dependency::Detailed(d) if d.git.is_some())
    }

    /// Get the path for path dependencies
    pub fn get_path(&self) -> Option<&str> {
        match self {
            Dependency::Detailed(d) => d.path.as_deref(),
            _ => None,
        }
    }

    /// Get the git URL for git dependencies
    pub fn get_git(&self) -> Option<&str> {
        match self {
            Dependency::Detailed(d) => d.git.as_deref(),
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_manifest() {
        let content = r#"
[package]
name = "myapp"
version = "0.1.0"

[dependencies]
http = "1.0"
"#;
        let manifest = Manifest::parse(content).unwrap();
        assert_eq!(manifest.package.name, "myapp");
        assert_eq!(manifest.package.version, "0.1.0");
        assert!(manifest.dependencies.contains_key("http"));
    }

    #[test]
    fn test_parse_detailed_dependencies() {
        let content = r#"
[package]
name = "myapp"

[dependencies]
mylib = { git = "https://github.com/user/mylib" }
utils = { path = "../utils" }
http = { version = "1.0", optional = true }
"#;
        let manifest = Manifest::parse(content).unwrap();

        let mylib = manifest.dependencies.get("mylib").unwrap();
        assert!(mylib.is_git());

        let utils = manifest.dependencies.get("utils").unwrap();
        assert!(utils.is_path());
    }

    #[test]
    fn test_new_manifest() {
        let manifest = Manifest::new("testpkg");
        assert_eq!(manifest.package.name, "testpkg");
        assert_eq!(manifest.package.version, "0.1.0");
        assert!(manifest.dependencies.is_empty());
    }

    #[test]
    fn test_add_remove_dependency() {
        let mut manifest = Manifest::new("testpkg");
        manifest.add_dependency("http", Dependency::version("1.0"));
        assert!(manifest.has_dependency("http"));

        manifest.remove_dependency("http");
        assert!(!manifest.has_dependency("http"));
    }

    #[test]
    fn test_serialize_manifest() {
        let manifest = Manifest::new("testpkg");
        let content = toml::to_string_pretty(&manifest).unwrap();
        assert!(content.contains("name = \"testpkg\""));
    }

    #[test]
    fn test_parse_verify_config() {
        let content = r#"
[package]
name = "verified_app"
version = "0.1.0"

[verify]
enabled = true
lean_path = "/opt/lean/bin/lean"
output_dir = "target/lean"
generate_stubs = false
modules = ["core", "math"]
check_proofs = true
strict = true
"#;
        let manifest = Manifest::parse(content).unwrap();
        assert!(manifest.verify.enabled);
        assert_eq!(manifest.verify.lean_path, Some("/opt/lean/bin/lean".to_string()));
        assert_eq!(manifest.verify.output_dir, Some("target/lean".to_string()));
        assert!(!manifest.verify.generate_stubs);
        assert_eq!(manifest.verify.modules, vec!["core", "math"]);
        assert!(manifest.verify.check_proofs);
        assert!(manifest.verify.strict);
    }

    #[test]
    fn test_verify_config_defaults() {
        let manifest = Manifest::new("testpkg");
        assert!(!manifest.verify.enabled);
        assert!(manifest.verify.generate_stubs);
        assert_eq!(manifest.verify.lean_executable(), "lean");
        assert_eq!(manifest.verify.lean_output_dir(), "build/lean");
    }

    #[test]
    fn test_should_verify_module() {
        let mut config = VerifyConfig::default();

        // Disabled - should not verify
        assert!(!config.should_verify_module("core"));

        // Enabled with no modules - verify all
        config.enabled = true;
        assert!(config.should_verify_module("core"));
        assert!(config.should_verify_module("math"));

        // Enabled with specific modules
        config.modules = vec!["core".to_string(), "math".to_string()];
        assert!(config.should_verify_module("core"));
        assert!(config.should_verify_module("core.types"));
        assert!(config.should_verify_module("math.vector"));
        assert!(!config.should_verify_module("io"));
    }
}

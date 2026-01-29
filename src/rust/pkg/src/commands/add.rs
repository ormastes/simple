//! `simple add` command - Add a dependency to the project

use std::path::Path;

use crate::error::{PkgError, PkgResult};
use crate::manifest::{Dependency, DependencyDetail, Manifest};

/// Load manifest from dir, returning error if not found
fn load_manifest(dir: &Path) -> PkgResult<(std::path::PathBuf, Manifest)> {
    let manifest_path =
        crate::find_manifest(dir).ok_or_else(|| PkgError::ManifestNotFound(dir.display().to_string()))?;
    let manifest = Manifest::load(&manifest_path)?;
    Ok((manifest_path, manifest))
}

/// Options for adding a dependency
#[derive(Debug, Default)]
pub struct AddOptions {
    /// Version constraint (e.g., "1.0", "^2.0")
    pub version: Option<String>,
    /// Git repository URL
    pub git: Option<String>,
    /// Git branch
    pub branch: Option<String>,
    /// Git tag
    pub tag: Option<String>,
    /// Git revision
    pub rev: Option<String>,
    /// Local path
    pub path: Option<String>,
    /// Add as dev dependency
    pub dev: bool,
    /// Features to enable
    pub features: Vec<String>,
}

/// Add a dependency to the project manifest
pub fn add_dependency(dir: &Path, name: &str, options: AddOptions) -> PkgResult<()> {
    let (manifest_path, mut manifest) = load_manifest(dir)?;

    // Create the dependency
    let dep = create_dependency(&options)?;

    // Add to appropriate section
    if options.dev {
        manifest.dev_dependencies.insert(name.to_string(), dep);
    } else {
        manifest.dependencies.insert(name.to_string(), dep);
    }

    // Save the manifest
    manifest.save(&manifest_path)?;

    Ok(())
}

/// Create a Dependency from options
fn create_dependency(options: &AddOptions) -> PkgResult<Dependency> {
    // Path dependency
    if let Some(path) = &options.path {
        return Ok(Dependency::Detailed(DependencyDetail {
            path: Some(path.clone()),
            features: options.features.clone(),
            ..Default::default()
        }));
    }

    // Git dependency
    if let Some(git) = &options.git {
        return Ok(Dependency::Detailed(DependencyDetail {
            git: Some(git.clone()),
            branch: options.branch.clone(),
            tag: options.tag.clone(),
            rev: options.rev.clone(),
            features: options.features.clone(),
            ..Default::default()
        }));
    }

    // Version dependency
    if let Some(version) = &options.version {
        if options.features.is_empty() {
            return Ok(Dependency::Version(version.clone()));
        } else {
            return Ok(Dependency::Detailed(DependencyDetail {
                version: Some(version.clone()),
                features: options.features.clone(),
                ..Default::default()
            }));
        }
    }

    // Default to latest
    Ok(Dependency::Version("*".to_string()))
}

/// Remove a dependency from the project manifest
pub fn remove_dependency(dir: &Path, name: &str, dev: bool) -> PkgResult<bool> {
    let (manifest_path, mut manifest) = load_manifest(dir)?;

    let removed = if dev {
        manifest.dev_dependencies.remove(name).is_some()
    } else {
        manifest.dependencies.remove(name).is_some()
    };

    if removed {
        manifest.save(&manifest_path)?;
    }

    Ok(removed)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commands::test_helpers::{cleanup_test_project, setup_test_project};
    use std::fs;

    #[test]
    fn test_add_version_dependency() {
        let temp_dir = setup_test_project("add", "version");

        add_dependency(
            &temp_dir,
            "http",
            AddOptions {
                version: Some("1.0".to_string()),
                ..Default::default()
            },
        )
        .unwrap();

        let manifest = Manifest::load(&crate::find_manifest(&temp_dir).unwrap()).unwrap();
        assert!(manifest.dependencies.contains_key("http"));
        let dep = manifest.dependencies.get("http").unwrap();
        assert_eq!(dep.version_str(), Some("1.0"));

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_add_path_dependency() {
        let temp_dir = setup_test_project("add", "path");

        add_dependency(
            &temp_dir,
            "mylib",
            AddOptions {
                path: Some("../mylib".to_string()),
                ..Default::default()
            },
        )
        .unwrap();

        let manifest = Manifest::load(&crate::find_manifest(&temp_dir).unwrap()).unwrap();
        let dep = manifest.dependencies.get("mylib").unwrap();
        assert!(dep.is_path());
        assert_eq!(dep.get_path(), Some("../mylib"));

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_add_git_dependency() {
        let temp_dir = setup_test_project("add", "git");

        add_dependency(
            &temp_dir,
            "json",
            AddOptions {
                git: Some("https://github.com/user/json".to_string()),
                branch: Some("main".to_string()),
                ..Default::default()
            },
        )
        .unwrap();

        let manifest = Manifest::load(&crate::find_manifest(&temp_dir).unwrap()).unwrap();
        let dep = manifest.dependencies.get("json").unwrap();
        assert!(dep.is_git());
        assert_eq!(dep.get_git(), Some("https://github.com/user/json"));

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_add_dev_dependency() {
        let temp_dir = setup_test_project("add", "dev");

        add_dependency(
            &temp_dir,
            "test-utils",
            AddOptions {
                version: Some("1.0".to_string()),
                dev: true,
                ..Default::default()
            },
        )
        .unwrap();

        let manifest = Manifest::load(&crate::find_manifest(&temp_dir).unwrap()).unwrap();
        assert!(!manifest.dependencies.contains_key("test-utils"));
        assert!(manifest.dev_dependencies.contains_key("test-utils"));

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_remove_dependency() {
        let temp_dir = setup_test_project("add", "remove");

        // Add a dependency first
        add_dependency(
            &temp_dir,
            "http",
            AddOptions {
                version: Some("1.0".to_string()),
                ..Default::default()
            },
        )
        .unwrap();

        // Remove it
        let removed = remove_dependency(&temp_dir, "http", false).unwrap();
        assert!(removed);

        let manifest = Manifest::load(&crate::find_manifest(&temp_dir).unwrap()).unwrap();
        assert!(!manifest.dependencies.contains_key("http"));

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_add_no_manifest() {
        let temp_dir = std::env::temp_dir().join(format!(
            "simple-add-test-no-manifest-{}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let _ = fs::remove_dir_all(&temp_dir);
        fs::create_dir_all(&temp_dir).unwrap();

        let result = add_dependency(&temp_dir, "http", AddOptions::default());
        assert!(matches!(result, Err(PkgError::ManifestNotFound(_))));

        let _ = fs::remove_dir_all(&temp_dir);
    }
}

//! `simple update` command - Update dependencies

use std::path::Path;

use crate::error::{PkgError, PkgResult};
use crate::linker::Linker;
use crate::lock::LockFile;
use crate::manifest::Manifest;

use super::install::install_dependencies;

/// Result of updating dependencies
#[derive(Debug, Default)]
pub struct UpdateResult {
    /// Packages that were updated
    pub updated: Vec<String>,
    /// Packages that remained unchanged
    pub unchanged: Vec<String>,
}

/// Update all dependencies
///
/// Removes the lock file and re-resolves all dependencies.
pub fn update_all(dir: &Path) -> PkgResult<UpdateResult> {
    let lock_path = dir.join("simple.lock");

    // Remove lock file to force re-resolution
    if lock_path.exists() {
        std::fs::remove_file(&lock_path)?;
    }

    // Clean deps/ directory
    let linker = Linker::new(dir);
    linker.clean()?;

    // Re-install everything
    let install_result = install_dependencies(dir)?;

    Ok(UpdateResult {
        updated: install_result.packages,
        unchanged: Vec::new(),
    })
}

/// Update a specific dependency
///
/// Removes only the specified package from the lock file and re-resolves.
pub fn update_package(dir: &Path, name: &str) -> PkgResult<UpdateResult> {
    let manifest_path = dir.join("simple.toml");
    let lock_path = dir.join("simple.lock");

    let manifest = Manifest::load(&manifest_path)?;

    // Check package exists in manifest
    if !manifest.has_dependency(name) && !manifest.dev_dependencies.contains_key(name) {
        return Err(PkgError::PackageNotFound(format!(
            "Dependency '{}' not found in manifest",
            name
        )));
    }

    // Remove only this package from lock file
    if lock_path.exists() {
        let mut lock = LockFile::load(&lock_path)?;
        lock.remove_package(name);
        lock.save(&lock_path)?;
    }

    // Remove the package from deps/
    let linker = Linker::new(dir);
    let _ = linker.unlink(name); // Ignore errors if not linked

    // Re-install
    let install_result = install_dependencies(dir)?;

    let updated = if install_result.packages.contains(&name.to_string()) {
        vec![name.to_string()]
    } else {
        Vec::new()
    };

    Ok(UpdateResult {
        updated,
        unchanged: Vec::new(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commands::test_helpers::{
        cleanup_test_project, setup_test_project, setup_two_path_deps, setup_with_path_dep,
    };

    #[test]
    fn test_update_all() {
        let (temp_dir, _dep_dir) = setup_with_path_dep("update", "update-all", "mylib");
        install_dependencies(&temp_dir).unwrap();

        // Update all
        let result = update_all(&temp_dir).unwrap();
        assert_eq!(result.updated.len(), 1);
        assert!(result.updated.contains(&"mylib".to_string()));

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_update_specific_package() {
        let (temp_dir, _lib_a, _lib_b) = setup_two_path_deps("update", "update-specific");
        install_dependencies(&temp_dir).unwrap();

        // Update just lib_a
        let result = update_package(&temp_dir, "lib_a").unwrap();
        assert!(result.updated.contains(&"lib_a".to_string()));

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_update_nonexistent_package() {
        let temp_dir = setup_test_project("update", "update-nonexistent");

        let result = update_package(&temp_dir, "nonexistent");
        assert!(matches!(result, Err(PkgError::PackageNotFound(_))));

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_update_removes_old_lock() {
        let (temp_dir, _dep_dir) = setup_with_path_dep("update", "update-lock", "mylib");
        install_dependencies(&temp_dir).unwrap();

        // Lock file should exist
        assert!(temp_dir.join("simple.lock").exists());

        // Update should recreate it
        update_all(&temp_dir).unwrap();

        assert!(temp_dir.join("simple.lock").exists());

        cleanup_test_project(&temp_dir);
    }
}

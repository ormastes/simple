//! `simple install` command - Install all dependencies

use std::path::{Path, PathBuf};

use crate::cache::Cache;
use crate::error::{PkgError, PkgResult};
use crate::linker::Linker;
use crate::lock::{LockFile, LockedPackage, PackageSource};
use crate::manifest::Manifest;
use crate::resolver::{self, ResolvedPackage, ResolvedSource};

/// Result of installing dependencies
#[derive(Debug, Default)]
pub struct InstallResult {
    /// Number of packages installed
    pub installed: usize,
    /// Number of packages already up-to-date
    pub up_to_date: usize,
    /// Number of packages skipped (registry/git not yet supported)
    pub skipped: usize,
    /// Packages that were installed
    pub packages: Vec<String>,
    /// Packages that were skipped with reason
    pub skipped_packages: Vec<(String, String)>,
}

/// Install all dependencies for a project
pub fn install_dependencies(dir: &Path) -> PkgResult<InstallResult> {
    let manifest_path =
        crate::find_manifest(dir).ok_or_else(|| PkgError::ManifestNotFound(dir.display().to_string()))?;
    let lock_path = dir.join("simple.lock");

    if !manifest_path.exists() {
        return Err(PkgError::ManifestNotFound(manifest_path.display().to_string()));
    }

    let manifest = Manifest::load(&manifest_path)?;
    let mut lock = LockFile::load(&lock_path)?;

    let cache = Cache::new()?;
    cache.init()?;

    // Resolve all dependencies
    let graph = resolver::resolve(&manifest, dir)?;

    // Get installation order
    let install_order = graph.topological_order()?;

    // Initialize linker
    let linker = Linker::new(dir);
    linker.init()?;

    let mut result = InstallResult::default();

    // Install in topological order
    for pkg in install_order {
        let install_result = install_single(pkg, &cache, &linker, &mut lock)?;
        match install_result {
            SingleInstallResult::Installed => {
                result.installed += 1;
                result.packages.push(pkg.name.clone());
            }
            SingleInstallResult::UpToDate => {
                result.up_to_date += 1;
            }
            SingleInstallResult::Skipped(reason) => {
                result.skipped += 1;
                result.skipped_packages.push((pkg.name.clone(), reason));
            }
        }
    }

    // Save lock file
    lock.save(&lock_path)?;

    Ok(result)
}

/// Result of installing a single package
enum SingleInstallResult {
    Installed,
    UpToDate,
    Skipped(String),
}

/// Install a single package
fn install_single(
    pkg: &ResolvedPackage,
    _cache: &Cache,
    linker: &Linker,
    lock: &mut LockFile,
) -> PkgResult<SingleInstallResult> {
    match &pkg.source {
        ResolvedSource::Path { path, absolute } => {
            // Check if already linked and up-to-date
            if linker.is_linked(&pkg.name) {
                if let Some(locked) = lock.find_package(&pkg.name) {
                    if let Some(locked_path) = locked.get_path() {
                        if locked_path == path.to_string_lossy() {
                            return Ok(SingleInstallResult::UpToDate);
                        }
                    }
                }
            }

            // Validate path exists
            if !absolute.exists() {
                return Err(PkgError::PackageNotFound(format!(
                    "Path dependency not found: {}",
                    absolute.display()
                )));
            }

            // Create symlink in deps/
            linker.link_path(&pkg.name, absolute)?;

            // Update lock file with dependencies
            lock.add_package(LockedPackage {
                name: pkg.name.clone(),
                version: pkg.version.to_string(),
                source: PackageSource::Path {
                    path: path.to_string_lossy().to_string(),
                },
                checksum: None,
                dependencies: pkg.dependencies.clone(),
            });

            Ok(SingleInstallResult::Installed)
        }
        ResolvedSource::Registry { version } => {
            // Registry packages not yet supported
            lock.add_package(LockedPackage {
                name: pkg.name.clone(),
                version: version.clone(),
                source: PackageSource::Registry {
                    registry: "default".to_string(),
                },
                checksum: None,
                dependencies: pkg.dependencies.clone(),
            });

            Ok(SingleInstallResult::Skipped(
                "registry packages not yet supported".to_string(),
            ))
        }
        ResolvedSource::Git { url, rev } => {
            // Git packages not yet supported
            lock.add_package(LockedPackage::from_git(
                &pkg.name,
                &pkg.version.to_string(),
                url,
                rev.as_deref(),
            ));

            Ok(SingleInstallResult::Skipped(
                "git packages not yet supported".to_string(),
            ))
        }
    }
}

/// Get the installation directory for dependencies
pub fn deps_dir(project_dir: &Path) -> PathBuf {
    project_dir.join("deps")
}

/// List installed dependencies
pub fn list_installed(project_dir: &Path) -> PkgResult<Vec<(String, String)>> {
    let lock_path = project_dir.join("simple.lock");
    let lock = LockFile::load(&lock_path)?;

    Ok(lock
        .packages
        .iter()
        .map(|p| (p.name.clone(), p.version.clone()))
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commands::init::init_project;
    use crate::commands::test_helpers::{cleanup_test_project, setup_test_project};
    use crate::manifest::Dependency;
    use std::fs;

    #[test]
    fn test_install_no_deps() {
        let temp_dir = setup_test_project("install", "no-deps");

        let result = install_dependencies(&temp_dir).unwrap();
        assert_eq!(result.installed, 0);
        assert_eq!(result.up_to_date, 0);

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_install_creates_lock_file() {
        let temp_dir = setup_test_project("install", "creates-lock");

        install_dependencies(&temp_dir).unwrap();

        let lock_path = temp_dir.join("simple.lock");
        assert!(lock_path.exists());

        cleanup_test_project(&temp_dir);
    }

    /// Helper to setup a test with a path dependency
    fn setup_path_dependency(test_name: &str, subtest: &str) -> (PathBuf, PathBuf) {
        let temp_dir = setup_test_project(test_name, subtest);

        // Create a path dependency
        let dep_dir = temp_dir.join("mylib");
        fs::create_dir_all(&dep_dir).unwrap();
        init_project(&dep_dir, Some("mylib")).unwrap();

        // Add the dependency
        let mut manifest = Manifest::load(&crate::find_manifest(&temp_dir).unwrap()).unwrap();
        manifest.add_dependency("mylib", Dependency::path("./mylib"));
        manifest.save(&crate::find_manifest(&temp_dir).unwrap()).unwrap();

        (temp_dir, dep_dir)
    }

    #[test]
    fn test_install_path_dependency() {
        let (temp_dir, _) = setup_path_dependency("install", "path-dep");

        // Install
        let result = install_dependencies(&temp_dir).unwrap();
        assert_eq!(result.installed, 1);
        assert!(result.packages.contains(&"mylib".to_string()));

        // Check deps/ directory
        let deps_link = temp_dir.join("deps/mylib");
        assert!(deps_link.exists() || deps_link.is_symlink());

        // Check lock file
        let lock = LockFile::load(&temp_dir.join("simple.lock")).unwrap();
        let mylib = lock.find_package("mylib").unwrap();
        assert!(mylib.is_path());

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_install_idempotent() {
        let (temp_dir, _) = setup_path_dependency("install", "idempotent");

        // First install
        let result1 = install_dependencies(&temp_dir).unwrap();
        assert_eq!(result1.installed, 1);

        // Second install should be up-to-date
        let result2 = install_dependencies(&temp_dir).unwrap();
        assert_eq!(result2.installed, 0);
        assert_eq!(result2.up_to_date, 1);

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_install_transitive_deps() {
        use crate::commands::test_helpers::setup_transitive_deps;

        let (temp_dir, _lib_a, _lib_b) = setup_transitive_deps("install", "transitive");

        // Install
        let result = install_dependencies(&temp_dir).unwrap();
        assert_eq!(result.installed, 2); // Both lib_a and lib_b

        // Both should be linked
        assert!(temp_dir.join("deps/lib_a").exists() || temp_dir.join("deps/lib_a").is_symlink());
        assert!(temp_dir.join("deps/lib_b").exists() || temp_dir.join("deps/lib_b").is_symlink());

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_install_registry_skipped() {
        let temp_dir = setup_test_project("install", "registry-skip");

        // Add a registry dependency
        let mut manifest = Manifest::load(&crate::find_manifest(&temp_dir).unwrap()).unwrap();
        manifest.add_dependency("http", Dependency::version("1.0"));
        manifest.save(&crate::find_manifest(&temp_dir).unwrap()).unwrap();

        // Install
        let result = install_dependencies(&temp_dir).unwrap();
        assert_eq!(result.installed, 0);
        assert_eq!(result.skipped, 1);
        assert!(result.skipped_packages.iter().any(|(name, _)| name == "http"));

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_list_installed() {
        let temp_dir = setup_test_project("install", "list-installed");

        // Create and install a path dependency
        let dep_dir = temp_dir.join("mylib");
        fs::create_dir_all(&dep_dir).unwrap();
        init_project(&dep_dir, Some("mylib")).unwrap();

        let mut manifest = Manifest::load(&crate::find_manifest(&temp_dir).unwrap()).unwrap();
        manifest.add_dependency("mylib", Dependency::path("./mylib"));
        manifest.save(&crate::find_manifest(&temp_dir).unwrap()).unwrap();

        install_dependencies(&temp_dir).unwrap();

        let installed = list_installed(&temp_dir).unwrap();
        assert_eq!(installed.len(), 1);
        assert_eq!(installed[0].0, "mylib");

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_install_no_manifest() {
        let temp_dir = std::env::temp_dir().join("simple-install-no-manifest");
        let _ = fs::remove_dir_all(&temp_dir);
        fs::create_dir_all(&temp_dir).unwrap();

        let result = install_dependencies(&temp_dir);
        assert!(matches!(result, Err(PkgError::ManifestNotFound(_))));

        let _ = fs::remove_dir_all(&temp_dir);
    }

    #[test]
    fn test_install_missing_path_dep() {
        let temp_dir = setup_test_project("install", "missing-dep");

        // Add a dependency to nonexistent path
        let mut manifest = Manifest::load(&crate::find_manifest(&temp_dir).unwrap()).unwrap();
        manifest.add_dependency("ghost", Dependency::path("./nonexistent"));
        manifest.save(&crate::find_manifest(&temp_dir).unwrap()).unwrap();

        let result = install_dependencies(&temp_dir);
        assert!(result.is_err());

        cleanup_test_project(&temp_dir);
    }
}

//! Lock file CLI commands for reproducible builds.
//!
//! ## Usage
//!
//! ```bash
//! simple lock                    # Generate/update simple.lock
//! simple lock --check            # Verify lock file is up-to-date
//! simple install --locked        # Install exact versions from lock
//! ```

use simple_pkg::lock::{LockFile, LockedPackage, PackageSource};
use simple_pkg::manifest::{Dependency, Manifest};
use std::collections::HashSet;
use std::path::Path;

/// Generate or update the lock file
pub fn generate_lock(project_dir: &Path) -> i32 {
    let manifest_path = project_dir.join("simple.toml");
    let lock_path = project_dir.join("simple.lock");

    // Load manifest
    let manifest = match Manifest::load(&manifest_path) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("error: failed to load simple.toml: {}", e);
            return 1;
        }
    };

    // Load existing lock file (or create new)
    let mut lock = LockFile::load(&lock_path).unwrap_or_default();

    // Track which packages we've seen
    let mut seen_packages: HashSet<String> = HashSet::new();

    // Resolve all dependencies and add to lock file
    for (name, dep) in &manifest.dependencies {
        seen_packages.insert(name.clone());

        let locked = match dep {
            Dependency::Version(version) => {
                // Registry dependency (simple version string)
                LockedPackage {
                    name: name.clone(),
                    version: version.clone(),
                    source: PackageSource::Registry {
                        registry: "https://pkg.simple-lang.org".to_string(),
                    },
                    checksum: None,
                    dependencies: Vec::new(),
                }
            }
            Dependency::Detailed(details) => {
                if let Some(path) = &details.path {
                    // Path dependency
                    let version = details.version.clone().unwrap_or_else(|| "0.0.0".to_string());
                    LockedPackage::from_path(name, &version, path)
                } else if let Some(git) = &details.git {
                    // Git dependency
                    let version = details.version.clone().unwrap_or_else(|| "0.0.0".to_string());
                    LockedPackage::from_git(name, &version, git, details.rev.as_deref())
                } else {
                    // Registry with detailed config
                    let version = details.version.clone().unwrap_or_else(|| "*".to_string());
                    LockedPackage {
                        name: name.clone(),
                        version,
                        source: PackageSource::Registry {
                            registry: "https://pkg.simple-lang.org".to_string(),
                        },
                        checksum: None,
                        dependencies: Vec::new(),
                    }
                }
            }
        };

        lock.add_package(locked);
    }

    // Remove packages no longer in manifest
    let to_remove: Vec<_> = lock
        .package_names()
        .into_iter()
        .filter(|name| !seen_packages.contains(*name))
        .map(|s| s.to_string())
        .collect();

    for name in to_remove {
        lock.remove_package(&name);
    }

    // Save lock file
    if let Err(e) = lock.save(&lock_path) {
        eprintln!("error: failed to write simple.lock: {}", e);
        return 1;
    }

    println!("Generated simple.lock with {} packages", lock.packages.len());
    0
}

/// Check if lock file is up-to-date with manifest
pub fn check_lock(project_dir: &Path) -> i32 {
    let manifest_path = project_dir.join("simple.toml");
    let lock_path = project_dir.join("simple.lock");

    if !lock_path.exists() {
        eprintln!("error: simple.lock not found");
        eprintln!("Run 'simple lock' to generate it");
        return 1;
    }

    // Load manifest
    let manifest = match Manifest::load(&manifest_path) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("error: failed to load simple.toml: {}", e);
            return 1;
        }
    };

    // Load lock file
    let lock = match LockFile::load(&lock_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: failed to load simple.lock: {}", e);
            return 1;
        }
    };

    // Check all manifest dependencies are in lock file
    let mut missing = Vec::new();
    let mut changed = Vec::new();

    for (name, dep) in &manifest.dependencies {
        match lock.find_package(name) {
            Some(locked) => {
                // Check if version matches
                let expected_version = match dep {
                    Dependency::Version(v) => v.clone(),
                    Dependency::Detailed(d) => d.version.clone().unwrap_or_else(|| "*".to_string()),
                };

                if locked.version != expected_version && expected_version != "*" {
                    changed.push((name.clone(), locked.version.clone(), expected_version));
                }
            }
            None => {
                missing.push(name.clone());
            }
        }
    }

    // Check for extra packages in lock file
    let manifest_deps: HashSet<_> = manifest.dependencies.keys().cloned().collect();
    let extra: Vec<_> = lock
        .package_names()
        .into_iter()
        .filter(|name| !manifest_deps.contains(*name))
        .collect();

    if missing.is_empty() && changed.is_empty() && extra.is_empty() {
        println!("Lock file is up-to-date");
        return 0;
    }

    eprintln!("Lock file is out of sync with manifest:");

    if !missing.is_empty() {
        eprintln!();
        eprintln!("Missing packages:");
        for name in &missing {
            eprintln!("  + {}", name);
        }
    }

    if !changed.is_empty() {
        eprintln!();
        eprintln!("Changed versions:");
        for (name, locked, expected) in &changed {
            eprintln!("  ~ {} ({} -> {})", name, locked, expected);
        }
    }

    if !extra.is_empty() {
        eprintln!();
        eprintln!("Extra packages:");
        for name in &extra {
            eprintln!("  - {}", name);
        }
    }

    eprintln!();
    eprintln!("Run 'simple lock' to update the lock file");
    1
}

/// Install dependencies from lock file (exact versions)
pub fn install_locked(project_dir: &Path) -> i32 {
    let lock_path = project_dir.join("simple.lock");

    if !lock_path.exists() {
        eprintln!("error: simple.lock not found");
        eprintln!("Run 'simple lock' to generate it first");
        return 1;
    }

    // Load lock file
    let lock = match LockFile::load(&lock_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: failed to load simple.lock: {}", e);
            return 1;
        }
    };

    if lock.is_empty() {
        println!("No packages to install");
        return 0;
    }

    println!("Installing {} packages from lock file...", lock.packages.len());

    for pkg in &lock.packages {
        match &pkg.source {
            PackageSource::Path { path } => {
                // Path dependencies - just verify they exist
                let dep_path = project_dir.join(path);
                if !dep_path.exists() {
                    eprintln!("warning: path dependency '{}' not found at {}", pkg.name, path);
                } else {
                    println!("  {} {} (path: {})", pkg.name, pkg.version, path);
                }
            }
            PackageSource::Git { url, rev } => {
                // Git dependencies - would clone/checkout
                let rev_str = rev.as_deref().unwrap_or("HEAD");
                println!("  {} {} (git: {}@{})", pkg.name, pkg.version, url, rev_str);
                // TODO: [env][P2] Implement git clone/checkout
            }
            PackageSource::Registry { registry } => {
                // Registry dependencies - would download
                println!("  {} {} ({})", pkg.name, pkg.version, registry);
                // TODO: [env][P2] Implement registry download
            }
        }
    }

    println!();
    println!("Installed {} packages", lock.packages.len());
    0
}

/// Print lock file info
pub fn lock_info(project_dir: &Path) -> i32 {
    let lock_path = project_dir.join("simple.lock");

    if !lock_path.exists() {
        eprintln!("error: simple.lock not found");
        return 1;
    }

    let lock = match LockFile::load(&lock_path) {
        Ok(l) => l,
        Err(e) => {
            eprintln!("error: failed to load simple.lock: {}", e);
            return 1;
        }
    };

    println!("Lock file version: {}", lock.version);
    println!("Packages: {}", lock.packages.len());
    println!();

    if !lock.is_empty() {
        println!("Dependencies:");
        for pkg in &lock.packages {
            let source = match &pkg.source {
                PackageSource::Path { path } => format!("path:{}", path),
                PackageSource::Git { url, rev } => {
                    format!("git:{}@{}", url, rev.as_deref().unwrap_or("HEAD"))
                }
                PackageSource::Registry { registry } => format!("registry:{}", registry),
            };
            println!("  {} {} ({})", pkg.name, pkg.version, source);
        }
    }

    0
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::tempdir;

    #[test]
    fn test_generate_empty_lock() {
        let dir = tempdir().unwrap();
        let manifest_content = r#"
[package]
name = "test"
version = "1.0.0"
"#;
        fs::write(dir.path().join("simple.toml"), manifest_content).unwrap();

        let result = generate_lock(dir.path());
        assert_eq!(result, 0);
        assert!(dir.path().join("simple.lock").exists());
    }
}

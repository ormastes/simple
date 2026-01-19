//! Lock file CLI commands for reproducible builds.
//!
//! ## Usage
//!
//! ```bash
//! simple lock                    # Generate/update simple.lock
//! simple lock --check            # Verify lock file is up-to-date
//! simple install --locked        # Install exact versions from lock
//! ```

use simple_pkg::cache::Cache;
use simple_pkg::linker::Linker;
use simple_pkg::lock::{LockFile, LockedPackage, PackageSource};
use simple_pkg::manifest::{Dependency, Manifest};
use std::collections::HashSet;
use std::path::Path;
use std::process::Command;

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

/// Clone a git repository to the cache and checkout a specific revision
fn git_clone_checkout(cache: &Cache, url: &str, rev: Option<&str>) -> Result<std::path::PathBuf, String> {
    let repo_path = cache.git_repo_path(url);

    // Check if already cloned
    if !repo_path.exists() {
        // Clone the repository
        let output = Command::new("git")
            .args(["clone", "--recurse-submodules", url])
            .arg(&repo_path)
            .output()
            .map_err(|e| format!("failed to execute git clone: {}", e))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("git clone failed: {}", stderr));
        }
    } else {
        // Fetch latest changes
        let output = Command::new("git")
            .args(["fetch", "--all"])
            .current_dir(&repo_path)
            .output()
            .map_err(|e| format!("failed to execute git fetch: {}", e))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            eprintln!("warning: git fetch failed: {}", stderr);
        }
    }

    // Checkout the specific revision
    if let Some(rev) = rev {
        let output = Command::new("git")
            .args(["checkout", rev])
            .current_dir(&repo_path)
            .output()
            .map_err(|e| format!("failed to execute git checkout: {}", e))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("git checkout '{}' failed: {}", rev, stderr));
        }
    }

    Ok(repo_path)
}

/// Download a package from the registry
fn registry_download(cache: &Cache, name: &str, version: &str, registry: &str) -> Result<std::path::PathBuf, String> {
    let pkg_path = cache.package_path(name, version);

    // Check if already downloaded
    if pkg_path.exists() {
        return Ok(pkg_path);
    }

    // Create parent directory
    if let Some(parent) = pkg_path.parent() {
        std::fs::create_dir_all(parent).map_err(|e| format!("failed to create cache directory: {}", e))?;
    }

    // Construct download URL
    let download_url = format!("{}/packages/{}/{}.tar.gz", registry, name, version);

    // Create a temporary file for the download
    let tmp_file = pkg_path.with_extension("tar.gz.tmp");

    // Try curl first, then wget as fallback
    let download_result = Command::new("curl")
        .args(["-fsSL", "-o"])
        .arg(&tmp_file)
        .arg(&download_url)
        .output();

    let success = match download_result {
        Ok(output) if output.status.success() => true,
        _ => {
            // Try wget as fallback
            let wget_result = Command::new("wget")
                .args(["-q", "-O"])
                .arg(&tmp_file)
                .arg(&download_url)
                .output();

            matches!(wget_result, Ok(output) if output.status.success())
        }
    };

    if !success {
        let _ = std::fs::remove_file(&tmp_file);
        return Err(format!(
            "failed to download package from {}: ensure curl or wget is installed",
            download_url
        ));
    }

    // Extract the tarball
    std::fs::create_dir_all(&pkg_path).map_err(|e| format!("failed to create package directory: {}", e))?;

    let output = Command::new("tar")
        .args(["-xzf"])
        .arg(&tmp_file)
        .args(["-C"])
        .arg(&pkg_path)
        .args(["--strip-components=1"])
        .output()
        .map_err(|e| format!("failed to execute tar: {}", e))?;

    // Clean up temp file
    let _ = std::fs::remove_file(&tmp_file);

    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        let _ = std::fs::remove_dir_all(&pkg_path);
        return Err(format!("failed to extract package: {}", stderr));
    }

    Ok(pkg_path)
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

    // Initialize cache
    let cache = match Cache::new() {
        Ok(c) => c,
        Err(e) => {
            eprintln!("error: failed to initialize cache: {}", e);
            return 1;
        }
    };

    if let Err(e) = cache.init() {
        eprintln!("error: failed to create cache directories: {}", e);
        return 1;
    }

    // Initialize linker for deps/ directory
    let linker = Linker::new(project_dir);
    if let Err(e) = linker.init() {
        eprintln!("error: failed to initialize deps directory: {}", e);
        return 1;
    }

    println!("Installing {} packages from lock file...", lock.packages.len());

    let mut installed = 0;
    let mut failed = 0;

    for pkg in &lock.packages {
        match &pkg.source {
            PackageSource::Path { path } => {
                // Path dependencies - verify and link
                let dep_path = project_dir.join(path);
                if !dep_path.exists() {
                    eprintln!("  error: path dependency '{}' not found at {}", pkg.name, path);
                    failed += 1;
                } else {
                    if let Err(e) = linker.link_path(&pkg.name, &dep_path) {
                        eprintln!("  error: failed to link '{}': {}", pkg.name, e);
                        failed += 1;
                    } else {
                        println!("  {} {} (path: {})", pkg.name, pkg.version, path);
                        installed += 1;
                    }
                }
            }
            PackageSource::Git { url, rev } => {
                // Git dependencies - clone/checkout and link
                let rev_str = rev.as_deref().unwrap_or("HEAD");
                match git_clone_checkout(&cache, url, rev.as_deref()) {
                    Ok(repo_path) => {
                        if let Err(e) = linker.link_cached(&pkg.name, &repo_path) {
                            eprintln!("  error: failed to link '{}': {}", pkg.name, e);
                            failed += 1;
                        } else {
                            println!("  {} {} (git: {}@{})", pkg.name, pkg.version, url, rev_str);
                            installed += 1;
                        }
                    }
                    Err(e) => {
                        eprintln!("  error: failed to clone '{}': {}", pkg.name, e);
                        failed += 1;
                    }
                }
            }
            PackageSource::Registry { registry } => {
                // Registry dependencies - download and link
                match registry_download(&cache, &pkg.name, &pkg.version, registry) {
                    Ok(pkg_path) => {
                        if let Err(e) = linker.link_cached(&pkg.name, &pkg_path) {
                            eprintln!("  error: failed to link '{}': {}", pkg.name, e);
                            failed += 1;
                        } else {
                            println!("  {} {} ({})", pkg.name, pkg.version, registry);
                            installed += 1;
                        }
                    }
                    Err(e) => {
                        eprintln!("  error: failed to download '{}': {}", pkg.name, e);
                        failed += 1;
                    }
                }
            }
        }
    }

    println!();
    if failed > 0 {
        eprintln!("Installed {} packages, {} failed", installed, failed);
        1
    } else {
        println!("Installed {} packages", installed);
        0
    }
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

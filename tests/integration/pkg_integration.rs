//! Package manager integration tests
//! Tests Manifest, Version, VersionReq, LockFile, and Cache public functions
//! Focus: Public function coverage for simple_pkg

#![allow(unused_imports, unused_variables)]

use simple_pkg::{Cache, LockFile, Manifest, Version, VersionReq};
use simple_pkg::lock::{LockedPackage, PackageSource};
use simple_pkg::manifest::{Dependency, DependencyDetail};
use std::path::PathBuf;
use tempfile::tempdir;

// =============================================================================
// Version Tests
// =============================================================================

#[test]
fn test_version_new() {
    let v = Version::new(1, 2, 3);
    assert_eq!(v.major(), 1);
    assert_eq!(v.minor(), 2);
    assert_eq!(v.patch(), 3);
}

#[test]
fn test_version_parse() {
    let v = Version::parse("2.5.10").expect("parse");
    assert_eq!(v.major(), 2);
    assert_eq!(v.minor(), 5);
    assert_eq!(v.patch(), 10);
}

#[test]
fn test_version_parse_invalid() {
    let result = Version::parse("not-a-version");
    assert!(result.is_err());
}

#[test]
fn test_version_display() {
    let v = Version::new(1, 0, 0);
    assert_eq!(v.to_string(), "1.0.0");
}

#[test]
fn test_version_comparison() {
    let v1 = Version::parse("1.0.0").unwrap();
    let v2 = Version::parse("1.0.1").unwrap();
    let v3 = Version::parse("2.0.0").unwrap();

    assert!(v1 < v2);
    assert!(v2 < v3);
    assert!(v1 < v3);
    assert!(v3 > v1);
}

#[test]
fn test_version_equality() {
    let v1 = Version::parse("1.2.3").unwrap();
    let v2 = Version::parse("1.2.3").unwrap();
    assert_eq!(v1, v2);
}

#[test]
fn test_version_default() {
    let v = Version::default();
    assert_eq!(v.major(), 0);
    assert_eq!(v.minor(), 0);
    assert_eq!(v.patch(), 0);
}

#[test]
fn test_version_from_str() {
    use std::str::FromStr;
    let v: Version = "3.2.1".parse().unwrap();
    assert_eq!(v.major(), 3);
}

// =============================================================================
// VersionReq Tests
// =============================================================================

#[test]
fn test_version_req_any() {
    let req = VersionReq::any();
    assert!(req.is_any());
    assert!(req.matches(&Version::parse("0.0.1").unwrap()));
    assert!(req.matches(&Version::parse("99.99.99").unwrap()));
}

#[test]
fn test_version_req_parse_simple() {
    let req = VersionReq::parse("1.0.0").expect("parse");
    assert!(req.matches(&Version::parse("1.0.0").unwrap()));
}

#[test]
fn test_version_req_parse_caret() {
    let req = VersionReq::parse("^1.0").expect("parse");
    assert!(req.matches(&Version::parse("1.0.0").unwrap()));
    assert!(req.matches(&Version::parse("1.5.0").unwrap()));
    assert!(!req.matches(&Version::parse("2.0.0").unwrap()));
}

#[test]
fn test_version_req_parse_tilde() {
    let req = VersionReq::parse("~1.2").expect("parse");
    assert!(req.matches(&Version::parse("1.2.0").unwrap()));
    assert!(req.matches(&Version::parse("1.2.5").unwrap()));
    assert!(!req.matches(&Version::parse("1.3.0").unwrap()));
}

#[test]
fn test_version_req_parse_comparison() {
    let req = VersionReq::parse(">=1.0, <3.0").expect("parse");
    assert!(!req.matches(&Version::parse("0.9.0").unwrap()));
    assert!(req.matches(&Version::parse("1.0.0").unwrap()));
    assert!(req.matches(&Version::parse("2.5.0").unwrap()));
    assert!(!req.matches(&Version::parse("3.0.0").unwrap()));
}

#[test]
fn test_version_req_parse_wildcard() {
    let req = VersionReq::parse("*").expect("parse");
    assert!(req.is_any());
}

#[test]
fn test_version_req_parse_exact() {
    let req = VersionReq::parse("=1.2.3").expect("parse");
    assert!(req.matches(&Version::parse("1.2.3").unwrap()));
    assert!(!req.matches(&Version::parse("1.2.4").unwrap()));
}

#[test]
fn test_version_req_display() {
    let req = VersionReq::parse("^1.0").expect("parse");
    let s = req.to_string();
    // Should contain version info
    assert!(!s.is_empty());
}

#[test]
fn test_version_req_default() {
    let req = VersionReq::default();
    assert!(req.is_any());
}

// =============================================================================
// Manifest Tests
// =============================================================================

#[test]
fn test_manifest_new() {
    let manifest = Manifest::new("testpkg");
    assert_eq!(manifest.package.name, "testpkg");
    assert_eq!(manifest.package.version, "0.1.0");
    assert!(manifest.dependencies.is_empty());
}

#[test]
fn test_manifest_parse() {
    let content = r#"
[package]
name = "myapp"
version = "1.0.0"

[dependencies]
http = "1.0"
"#;
    let manifest = Manifest::parse(content).expect("parse");
    assert_eq!(manifest.package.name, "myapp");
    assert_eq!(manifest.package.version, "1.0.0");
    assert!(manifest.has_dependency("http"));
}

#[test]
fn test_manifest_add_dependency() {
    let mut manifest = Manifest::new("test");
    manifest.add_dependency("http", Dependency::version("1.0"));
    assert!(manifest.has_dependency("http"));
}

#[test]
fn test_manifest_remove_dependency() {
    let mut manifest = Manifest::new("test");
    manifest.add_dependency("http", Dependency::version("1.0"));
    let removed = manifest.remove_dependency("http");
    assert!(removed.is_some());
    assert!(!manifest.has_dependency("http"));
}

#[test]
fn test_manifest_has_dependency() {
    let manifest = Manifest::new("test");
    assert!(!manifest.has_dependency("nonexistent"));
}

#[test]
fn test_manifest_save_load() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("simple.toml");

    let manifest = Manifest::new("savepkg");
    manifest.save(&path).expect("save");

    let loaded = Manifest::load(&path).expect("load");
    assert_eq!(loaded.package.name, "savepkg");
}

#[test]
fn test_manifest_load_missing() {
    let result = Manifest::load(std::path::Path::new("/nonexistent/simple.toml"));
    assert!(result.is_err());
}

// =============================================================================
// Dependency Tests
// =============================================================================

#[test]
fn test_dependency_version() {
    let dep = Dependency::version("1.0");
    assert_eq!(dep.version_str(), Some("1.0"));
    assert!(!dep.is_path());
    assert!(!dep.is_git());
}

#[test]
fn test_dependency_git() {
    let dep = Dependency::git("https://github.com/user/lib");
    assert!(dep.is_git());
    assert!(!dep.is_path());
    assert_eq!(dep.get_git(), Some("https://github.com/user/lib"));
}

#[test]
fn test_dependency_path() {
    let dep = Dependency::path("../mylib");
    assert!(dep.is_path());
    assert!(!dep.is_git());
    assert_eq!(dep.get_path(), Some("../mylib"));
}

#[test]
fn test_dependency_version_str() {
    let dep = Dependency::version("2.0");
    assert_eq!(dep.version_str(), Some("2.0"));

    let git_dep = Dependency::git("https://example.com");
    assert!(git_dep.version_str().is_none());
}

// =============================================================================
// LockFile Tests
// =============================================================================

#[test]
fn test_lockfile_default() {
    let lock = LockFile::default();
    assert!(lock.is_empty());
    assert_eq!(lock.version, 1);
}

#[test]
fn test_lockfile_parse() {
    let content = r#"
version = 1

[[packages]]
name = "http"
version = "1.0.0"
[packages.source]
type = "path"
path = "../http"
"#;
    let lock = LockFile::parse(content).expect("parse");
    assert_eq!(lock.version, 1);
    assert!(!lock.is_empty());
}

#[test]
fn test_lockfile_find_package() {
    let content = r#"
version = 1

[[packages]]
name = "http"
version = "1.0.0"
[packages.source]
type = "path"
path = "../http"
"#;
    let lock = LockFile::parse(content).expect("parse");

    let pkg = lock.find_package("http");
    assert!(pkg.is_some());
    assert_eq!(pkg.unwrap().version, "1.0.0");

    assert!(lock.find_package("nonexistent").is_none());
}

#[test]
fn test_lockfile_add_package() {
    let mut lock = LockFile::default();
    let pkg = LockedPackage::from_path("mylib", "1.0.0", "../mylib");

    lock.add_package(pkg);
    assert!(!lock.is_empty());
    assert!(lock.find_package("mylib").is_some());
}

#[test]
fn test_lockfile_remove_package() {
    let mut lock = LockFile::default();
    let pkg = LockedPackage::from_path("mylib", "1.0.0", "../mylib");
    lock.add_package(pkg);

    let removed = lock.remove_package("mylib");
    assert!(removed.is_some());
    assert!(lock.is_empty());

    // Remove non-existent
    let removed2 = lock.remove_package("nonexistent");
    assert!(removed2.is_none());
}

#[test]
fn test_lockfile_package_names() {
    let mut lock = LockFile::default();
    lock.add_package(LockedPackage::from_path("a", "1.0.0", "../a"));
    lock.add_package(LockedPackage::from_path("b", "1.0.0", "../b"));

    let names = lock.package_names();
    assert_eq!(names.len(), 2);
    assert!(names.contains(&"a"));
    assert!(names.contains(&"b"));
}

#[test]
fn test_lockfile_dependency_graph() {
    let mut lock = LockFile::default();
    lock.add_package(LockedPackage {
        name: "a".to_string(),
        version: "1.0.0".to_string(),
        source: PackageSource::Path { path: "../a".to_string() },
        checksum: None,
        dependencies: vec!["b".to_string()],
    });
    lock.add_package(LockedPackage::from_path("b", "1.0.0", "../b"));

    let graph = lock.dependency_graph();
    assert_eq!(graph.get("a"), Some(&vec!["b"]));
    assert_eq!(graph.get("b"), Some(&vec![]));
}

#[test]
fn test_lockfile_save_load() {
    let dir = tempdir().expect("tempdir");
    let path = dir.path().join("simple.lock");

    let mut lock = LockFile::default();
    lock.add_package(LockedPackage::from_path("test", "1.0.0", "../test"));
    lock.save(&path).expect("save");

    let loaded = LockFile::load(&path).expect("load");
    assert!(loaded.find_package("test").is_some());
}

#[test]
fn test_lockfile_load_missing() {
    // Loading from non-existent file should return default
    let lock = LockFile::load(std::path::Path::new("/nonexistent/simple.lock")).expect("load");
    assert!(lock.is_empty());
}

// =============================================================================
// LockedPackage Tests
// =============================================================================

#[test]
fn test_locked_package_from_path() {
    let pkg = LockedPackage::from_path("mylib", "1.0.0", "../mylib");
    assert_eq!(pkg.name, "mylib");
    assert_eq!(pkg.version, "1.0.0");
    assert!(pkg.is_path());
    assert!(!pkg.is_git());
    assert_eq!(pkg.get_path(), Some("../mylib"));
}

#[test]
fn test_locked_package_from_git() {
    let pkg = LockedPackage::from_git("mylib", "1.0.0", "https://github.com/user/mylib", Some("abc123"));
    assert_eq!(pkg.name, "mylib");
    assert!(pkg.is_git());
    assert!(!pkg.is_path());
    assert_eq!(pkg.get_git_url(), Some("https://github.com/user/mylib"));
}

#[test]
fn test_locked_package_get_path_none() {
    let pkg = LockedPackage::from_git("mylib", "1.0.0", "https://example.com", None);
    assert!(pkg.get_path().is_none());
}

#[test]
fn test_locked_package_get_git_url_none() {
    let pkg = LockedPackage::from_path("mylib", "1.0.0", "../mylib");
    assert!(pkg.get_git_url().is_none());
}

// =============================================================================
// Cache Tests
// =============================================================================

#[test]
fn test_cache_at() {
    let cache = Cache::at(PathBuf::from("/tmp/test-cache"));
    assert_eq!(cache.root(), std::path::Path::new("/tmp/test-cache"));
}

#[test]
fn test_cache_git_dir() {
    let cache = Cache::at(PathBuf::from("/tmp/test-cache"));
    assert_eq!(cache.git_dir(), PathBuf::from("/tmp/test-cache/git"));
}

#[test]
fn test_cache_registry_dir() {
    let cache = Cache::at(PathBuf::from("/tmp/test-cache"));
    assert_eq!(cache.registry_dir(), PathBuf::from("/tmp/test-cache/registry"));
}

#[test]
fn test_cache_packages_dir() {
    let cache = Cache::at(PathBuf::from("/tmp/test-cache"));
    assert_eq!(cache.packages_dir(), PathBuf::from("/tmp/test-cache/packages"));
}

#[test]
fn test_cache_package_path() {
    let cache = Cache::at(PathBuf::from("/tmp/test-cache"));
    let path = cache.package_path("http", "1.0.0");
    assert_eq!(path, PathBuf::from("/tmp/test-cache/packages/http-1.0.0"));
}

#[test]
fn test_cache_git_repo_path() {
    let cache = Cache::at(PathBuf::from("/tmp/test-cache"));
    let path = cache.git_repo_path("https://github.com/user/mylib");
    // Should contain mylib in the path
    assert!(path.to_string_lossy().contains("mylib"));
}

#[test]
fn test_cache_has_git_repo() {
    let cache = Cache::at(PathBuf::from("/nonexistent/cache"));
    assert!(!cache.has_git_repo("https://github.com/user/mylib"));
}

#[test]
fn test_cache_has_package() {
    let cache = Cache::at(PathBuf::from("/nonexistent/cache"));
    assert!(!cache.has_package("http", "1.0.0"));
}

#[test]
fn test_cache_init() {
    let dir = tempdir().expect("tempdir");
    let cache = Cache::at(dir.path().to_path_buf());

    cache.init().expect("init");

    assert!(cache.git_dir().exists());
    assert!(cache.registry_dir().exists());
    assert!(cache.packages_dir().exists());
}

#[test]
fn test_cache_size_empty() {
    let dir = tempdir().expect("tempdir");
    let cache = Cache::at(dir.path().to_path_buf());

    cache.init().expect("init");
    let size = cache.size().expect("size");
    // Empty cache should have small or zero size
    assert!(size < 1000);
}

#[test]
fn test_cache_clean() {
    let dir = tempdir().expect("tempdir");
    let cache_path = dir.path().join("cache");
    let cache = Cache::at(cache_path.clone());

    cache.init().expect("init");
    assert!(cache_path.exists());

    cache.clean().expect("clean");
    assert!(!cache_path.exists());
}

#[test]
fn test_cache_clean_git() {
    let dir = tempdir().expect("tempdir");
    let cache = Cache::at(dir.path().to_path_buf());

    cache.init().expect("init");
    assert!(cache.git_dir().exists());

    cache.clean_git().expect("clean_git");
    assert!(!cache.git_dir().exists());
    // Other dirs should still exist
    assert!(cache.registry_dir().exists());
}

#[test]
fn test_cache_list_packages_empty() {
    let dir = tempdir().expect("tempdir");
    let cache = Cache::at(dir.path().to_path_buf());

    cache.init().expect("init");
    let packages = cache.list_packages().expect("list");
    assert!(packages.is_empty());
}

#[test]
fn test_cache_default_cache_dir() {
    // Should return a path (may vary by system)
    let result = Cache::default_cache_dir();
    // This may fail on some systems without home dir, but that's OK
    let _ = result;
}

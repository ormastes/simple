//! Package Manager System Tests
//!
//! Tests for simple_pkg crate: Manifest, LockFile, Version, VersionReq, Dependency

use simple_pkg::{
    Manifest, LockFile, Version, VersionReq,
    lock::{LockedPackage, PackageSource},
    manifest::Dependency,
};

// ============================================================================
// Version Tests (#8a)
// ============================================================================

#[test]
fn test_pkg_version_new() {
    let v = Version::new(1, 2, 3);
    assert_eq!(v.major(), 1);
    assert_eq!(v.minor(), 2);
    assert_eq!(v.patch(), 3);
}

#[test]
fn test_pkg_version_parse() {
    let v = Version::parse("1.2.3").unwrap();
    assert_eq!(v.major(), 1);
    assert_eq!(v.minor(), 2);
    assert_eq!(v.patch(), 3);
}

#[test]
fn test_pkg_version_parse_error() {
    let result = Version::parse("not-a-version");
    assert!(result.is_err());
}

#[test]
fn test_pkg_version_comparison() {
    let v1 = Version::parse("1.0.0").unwrap();
    let v2 = Version::parse("1.0.1").unwrap();
    let v3 = Version::parse("2.0.0").unwrap();

    assert!(v1 < v2);
    assert!(v2 < v3);
    assert!(v1 < v3);
    assert!(v1 == v1);
}

#[test]
fn test_pkg_version_display() {
    let v = Version::new(1, 2, 3);
    assert_eq!(v.to_string(), "1.2.3");
}

#[test]
fn test_pkg_version_from_str() {
    let v: Version = "1.2.3".parse().unwrap();
    assert_eq!(v.major(), 1);
}

#[test]
fn test_pkg_version_default() {
    let v = Version::default();
    assert_eq!(v.major(), 0);
    assert_eq!(v.minor(), 0);
    assert_eq!(v.patch(), 0);
}

// ============================================================================
// VersionReq Tests (#8b)
// ============================================================================

#[test]
fn test_pkg_version_req_any() {
    let req = VersionReq::any();
    assert!(req.is_any());
    assert!(req.matches(&Version::parse("0.0.1").unwrap()));
    assert!(req.matches(&Version::parse("99.99.99").unwrap()));
}

#[test]
fn test_pkg_version_req_parse_caret() {
    let req = VersionReq::parse("^1.0").unwrap();
    assert!(req.matches(&Version::parse("1.0.0").unwrap()));
    assert!(req.matches(&Version::parse("1.5.0").unwrap()));
    assert!(!req.matches(&Version::parse("2.0.0").unwrap()));
}

#[test]
fn test_pkg_version_req_parse_tilde() {
    let req = VersionReq::parse("~1.2").unwrap();
    assert!(req.matches(&Version::parse("1.2.0").unwrap()));
    assert!(req.matches(&Version::parse("1.2.5").unwrap()));
    assert!(!req.matches(&Version::parse("1.3.0").unwrap()));
}

#[test]
fn test_pkg_version_req_parse_comparison() {
    let req = VersionReq::parse(">=1.0, <3.0").unwrap();
    assert!(!req.matches(&Version::parse("0.9.0").unwrap()));
    assert!(req.matches(&Version::parse("1.0.0").unwrap()));
    assert!(req.matches(&Version::parse("2.5.0").unwrap()));
    assert!(!req.matches(&Version::parse("3.0.0").unwrap()));
}

#[test]
fn test_pkg_version_req_parse_wildcard() {
    let req = VersionReq::parse("*").unwrap();
    assert!(req.is_any());
}

#[test]
fn test_pkg_version_req_parse_exact() {
    let req = VersionReq::parse("=1.2.3").unwrap();
    assert!(req.matches(&Version::parse("1.2.3").unwrap()));
    assert!(!req.matches(&Version::parse("1.2.4").unwrap()));
}

#[test]
fn test_pkg_version_req_display() {
    let req = VersionReq::parse("^1.0").unwrap();
    let s = req.to_string();
    assert!(s.contains("1.0") || s.contains("1"));
}

#[test]
fn test_pkg_version_req_default() {
    let req = VersionReq::default();
    assert!(req.is_any());
}

// ============================================================================
// Manifest Tests (#8c)
// ============================================================================

#[test]
fn test_pkg_manifest_new() {
    let manifest = Manifest::new("testpkg");
    assert_eq!(manifest.package.name, "testpkg");
    assert_eq!(manifest.package.version, "0.1.0");
    assert!(manifest.dependencies.is_empty());
}

#[test]
fn test_pkg_manifest_parse_simple() {
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
fn test_pkg_manifest_parse_detailed() {
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
fn test_pkg_manifest_add_dependency() {
    let mut manifest = Manifest::new("testpkg");
    manifest.add_dependency("http", Dependency::version("1.0"));
    assert!(manifest.has_dependency("http"));
}

#[test]
fn test_pkg_manifest_remove_dependency() {
    let mut manifest = Manifest::new("testpkg");
    manifest.add_dependency("http", Dependency::version("1.0"));
    assert!(manifest.has_dependency("http"));

    let removed = manifest.remove_dependency("http");
    assert!(removed.is_some());
    assert!(!manifest.has_dependency("http"));
}

#[test]
fn test_pkg_manifest_has_dependency() {
    let mut manifest = Manifest::new("testpkg");
    assert!(!manifest.has_dependency("http"));

    manifest.add_dependency("http", Dependency::version("1.0"));
    assert!(manifest.has_dependency("http"));
}

// ============================================================================
// Dependency Tests (#8d)
// ============================================================================

#[test]
fn test_pkg_dependency_version() {
    let dep = Dependency::version("1.0");
    assert_eq!(dep.version_str(), Some("1.0"));
    assert!(!dep.is_path());
    assert!(!dep.is_git());
}

#[test]
fn test_pkg_dependency_path() {
    let dep = Dependency::path("../mylib");
    assert!(dep.is_path());
    assert!(!dep.is_git());
    assert_eq!(dep.get_path(), Some("../mylib"));
}

#[test]
fn test_pkg_dependency_git() {
    let dep = Dependency::git("https://github.com/user/repo");
    assert!(dep.is_git());
    assert!(!dep.is_path());
    assert_eq!(dep.get_git(), Some("https://github.com/user/repo"));
}

// ============================================================================
// LockFile Tests (#8e)
// ============================================================================

#[test]
fn test_pkg_lockfile_default() {
    let lock = LockFile::default();
    assert!(lock.is_empty());
    assert_eq!(lock.version, 1);
}

#[test]
fn test_pkg_lockfile_parse() {
    let content = r#"
version = 1

[[packages]]
name = "http"
version = "1.0.0"
[packages.source]
type = "path"
path = "../http"

[[packages]]
name = "json"
version = "2.0.0"
dependencies = ["http"]
[packages.source]
type = "git"
url = "https://github.com/user/json"
rev = "abc123"
"#;
    let lock = LockFile::parse(content).unwrap();
    assert_eq!(lock.version, 1);
    assert_eq!(lock.packages.len(), 2);
}

#[test]
fn test_pkg_lockfile_find_package() {
    let content = r#"
version = 1

[[packages]]
name = "http"
version = "1.0.0"
[packages.source]
type = "path"
path = "../http"
"#;
    let lock = LockFile::parse(content).unwrap();

    let http = lock.find_package("http");
    assert!(http.is_some());
    assert_eq!(http.unwrap().version, "1.0.0");

    let missing = lock.find_package("nonexistent");
    assert!(missing.is_none());
}

#[test]
fn test_pkg_lockfile_add_package() {
    let mut lock = LockFile::default();
    assert!(lock.is_empty());

    let pkg = LockedPackage::from_path("mylib", "1.0.0", "../mylib");
    lock.add_package(pkg);

    assert!(!lock.is_empty());
    assert!(lock.find_package("mylib").is_some());
}

#[test]
fn test_pkg_lockfile_remove_package() {
    let mut lock = LockFile::default();
    lock.add_package(LockedPackage::from_path("mylib", "1.0.0", "../mylib"));

    let removed = lock.remove_package("mylib");
    assert!(removed.is_some());
    assert!(lock.is_empty());

    let removed_again = lock.remove_package("mylib");
    assert!(removed_again.is_none());
}

#[test]
fn test_pkg_lockfile_is_empty() {
    let lock = LockFile::default();
    assert!(lock.is_empty());
}

#[test]
fn test_pkg_lockfile_package_names() {
    let mut lock = LockFile::default();
    lock.add_package(LockedPackage::from_path("a", "1.0.0", "../a"));
    lock.add_package(LockedPackage::from_path("b", "1.0.0", "../b"));

    let names = lock.package_names();
    assert_eq!(names.len(), 2);
    assert!(names.contains(&"a"));
    assert!(names.contains(&"b"));
}

#[test]
fn test_pkg_lockfile_dependency_graph() {
    let mut lock = LockFile::default();
    lock.add_package(LockedPackage {
        name: "a".to_string(),
        version: "1.0.0".to_string(),
        source: PackageSource::Path { path: "../a".to_string() },
        checksum: None,
        dependencies: vec!["b".to_string(), "c".to_string()],
    });
    lock.add_package(LockedPackage::from_path("b", "1.0.0", "../b"));
    lock.add_package(LockedPackage::from_path("c", "1.0.0", "../c"));

    let graph = lock.dependency_graph();
    assert_eq!(graph.get("a"), Some(&vec!["b", "c"]));
    assert_eq!(graph.get("b"), Some(&vec![]));
}

// ============================================================================
// LockedPackage Tests (#8f)
// ============================================================================

#[test]
fn test_pkg_locked_package_from_path() {
    let pkg = LockedPackage::from_path("mylib", "1.0.0", "../mylib");
    assert_eq!(pkg.name, "mylib");
    assert_eq!(pkg.version, "1.0.0");
    assert!(pkg.is_path());
    assert!(!pkg.is_git());
    assert_eq!(pkg.get_path(), Some("../mylib"));
}

#[test]
fn test_pkg_locked_package_from_git() {
    let pkg = LockedPackage::from_git("mylib", "1.0.0", "https://github.com/user/repo", Some("abc123"));
    assert_eq!(pkg.name, "mylib");
    assert_eq!(pkg.version, "1.0.0");
    assert!(pkg.is_git());
    assert!(!pkg.is_path());
    assert_eq!(pkg.get_git_url(), Some("https://github.com/user/repo"));
}

#[test]
fn test_pkg_locked_package_from_git_no_rev() {
    let pkg = LockedPackage::from_git("mylib", "1.0.0", "https://github.com/user/repo", None);
    assert!(pkg.is_git());
    assert_eq!(pkg.get_git_url(), Some("https://github.com/user/repo"));
}

// ============================================================================
// PackageSource Tests (#8g)
// ============================================================================

#[test]
fn test_pkg_package_source_path() {
    let pkg = LockedPackage::from_path("test", "1.0.0", "../test");
    match &pkg.source {
        PackageSource::Path { path } => assert_eq!(path, "../test"),
        _ => panic!("Expected Path source"),
    }
}

#[test]
fn test_pkg_package_source_git() {
    let pkg = LockedPackage::from_git("test", "1.0.0", "https://example.com/repo", Some("rev123"));
    match &pkg.source {
        PackageSource::Git { url, rev } => {
            assert_eq!(url, "https://example.com/repo");
            assert_eq!(rev.as_deref(), Some("rev123"));
        }
        _ => panic!("Expected Git source"),
    }
}

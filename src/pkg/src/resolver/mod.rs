//! Dependency resolution for the package manager
//!
//! Resolves all dependencies from a manifest, building a dependency graph
//! with topological ordering for installation.

mod graph;

pub use graph::{DependencyGraph, ResolvedPackage, ResolvedSource};

use std::collections::HashSet;
use std::path::{Path, PathBuf};

use crate::error::{PkgError, PkgResult};
use crate::manifest::{Dependency, Manifest};
use crate::version::Version;

/// Resolve all dependencies from a manifest
///
/// Walks the dependency tree, loading transitive dependencies from path
/// dependencies. Returns a graph with all packages in topological order.
pub fn resolve(manifest: &Manifest, project_dir: &Path) -> PkgResult<DependencyGraph> {
    let mut graph = DependencyGraph::new();
    let mut visited: HashSet<String> = HashSet::new();
    let mut to_process: Vec<(String, Dependency, PathBuf)> = Vec::new();

    // Add direct dependencies
    for (name, dep) in &manifest.dependencies {
        to_process.push((name.clone(), dep.clone(), project_dir.to_path_buf()));
    }

    // Add dev dependencies
    for (name, dep) in &manifest.dev_dependencies {
        to_process.push((name.clone(), dep.clone(), project_dir.to_path_buf()));
    }

    // Process transitively
    while let Some((name, dep, context_dir)) = to_process.pop() {
        if visited.contains(&name) {
            continue;
        }
        visited.insert(name.clone());

        let resolved = resolve_single(&name, &dep, &context_dir)?;

        // If path dependency, load its manifest for transitive deps
        if let ResolvedSource::Path { absolute, .. } = &resolved.source {
            let dep_manifest_path = absolute.join("simple.toml");
            if dep_manifest_path.exists() {
                if let Ok(dep_manifest) = Manifest::load(&dep_manifest_path) {
                    for (sub_name, sub_dep) in &dep_manifest.dependencies {
                        if !visited.contains(sub_name) {
                            to_process.push((sub_name.clone(), sub_dep.clone(), absolute.clone()));
                        }
                    }
                }
            }
        }

        graph.add(resolved)?;
    }

    Ok(graph)
}

/// Resolve a single dependency
fn resolve_single(name: &str, dep: &Dependency, context_dir: &Path) -> PkgResult<ResolvedPackage> {
    match dep {
        Dependency::Version(v) => {
            // Registry package - placeholder for now
            Ok(ResolvedPackage {
                name: name.to_string(),
                version: Version::parse(v).unwrap_or_default(),
                source: ResolvedSource::Registry { version: v.clone() },
                dependencies: Vec::new(),
            })
        }
        Dependency::Detailed(d) => {
            if let Some(path) = &d.path {
                // Path dependency - resolve relative to context
                let path_buf = PathBuf::from(path);
                let abs_path = if path_buf.is_absolute() {
                    path_buf.clone()
                } else {
                    context_dir.join(&path_buf)
                };

                let abs_path = abs_path.canonicalize().map_err(|e| {
                    PkgError::PackageNotFound(format!(
                        "Path dependency '{}' not found at {}: {}",
                        name,
                        abs_path.display(),
                        e
                    ))
                })?;

                // Validate path dependency has simple.toml
                let manifest_path = abs_path.join("simple.toml");
                if !manifest_path.exists() {
                    return Err(PkgError::ManifestNotFound(format!(
                        "Path dependency '{}' missing simple.toml at {}",
                        name,
                        abs_path.display()
                    )));
                }

                // Load dependency manifest to get version and sub-deps
                let dep_manifest = Manifest::load(&manifest_path)?;

                Ok(ResolvedPackage {
                    name: name.to_string(),
                    version: Version::parse(&dep_manifest.package.version).unwrap_or_default(),
                    source: ResolvedSource::Path {
                        path: path_buf,
                        absolute: abs_path,
                    },
                    dependencies: dep_manifest.dependencies.keys().cloned().collect(),
                })
            } else if let Some(git) = &d.git {
                // Git dependency - placeholder (no fetching in MVP)
                Ok(ResolvedPackage {
                    name: name.to_string(),
                    version: Version::default(),
                    source: ResolvedSource::Git {
                        url: git.clone(),
                        rev: d
                            .rev
                            .clone()
                            .or_else(|| d.tag.clone())
                            .or_else(|| d.branch.clone()),
                    },
                    dependencies: Vec::new(),
                })
            } else {
                // Registry with options
                let version = d.version.clone().unwrap_or_else(|| "*".to_string());
                Ok(ResolvedPackage {
                    name: name.to_string(),
                    version: Version::parse(&version).unwrap_or_default(),
                    source: ResolvedSource::Registry { version },
                    dependencies: Vec::new(),
                })
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn temp_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "simple-resolver-test-{}-{}",
            name,
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn create_manifest(dir: &Path, name: &str, deps: &[(&str, &str)]) {
        let mut content = format!(
            r#"[package]
name = "{}"
version = "1.0.0"

[dependencies]
"#,
            name
        );

        for (dep_name, dep_path) in deps {
            content.push_str(&format!("{} = {{ path = \"{}\" }}\n", dep_name, dep_path));
        }

        fs::create_dir_all(dir).unwrap();
        fs::write(dir.join("simple.toml"), content).unwrap();
    }

    /// Load manifest and resolve dependencies
    fn resolve_from_dir(dir: &Path) -> DependencyGraph {
        let manifest = Manifest::load(&dir.join("simple.toml")).unwrap();
        resolve(&manifest, dir).unwrap()
    }

    #[test]
    fn test_resolve_no_deps() {
        let temp = temp_dir("no-deps");
        create_manifest(&temp, "myapp", &[]);

        let graph = resolve_from_dir(&temp);

        assert!(graph.is_empty());

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn test_resolve_single_path_dep() {
        let temp = temp_dir("single-dep");
        let lib_dir = temp.join("mylib");

        create_manifest(&temp, "myapp", &[("mylib", "./mylib")]);
        create_manifest(&lib_dir, "mylib", &[]);

        let graph = resolve_from_dir(&temp);

        assert_eq!(graph.len(), 1);
        assert!(graph.contains("mylib"));

        let pkg = graph.get("mylib").unwrap();
        assert!(pkg.is_path());

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn test_resolve_transitive_deps() {
        let temp = temp_dir("transitive");
        let lib_a = temp.join("lib_a");
        let lib_b = temp.join("lib_b");

        // myapp -> lib_a -> lib_b
        create_manifest(&temp, "myapp", &[("lib_a", "./lib_a")]);
        create_manifest(&lib_a, "lib_a", &[("lib_b", "../lib_b")]);
        create_manifest(&lib_b, "lib_b", &[]);

        let graph = resolve_from_dir(&temp);

        assert_eq!(graph.len(), 2);
        assert!(graph.contains("lib_a"));
        assert!(graph.contains("lib_b"));

        // Check order
        let order = graph.topological_order().unwrap();
        let names: Vec<_> = order.iter().map(|p| p.name.as_str()).collect();
        let pos_a = names.iter().position(|&n| n == "lib_a").unwrap();
        let pos_b = names.iter().position(|&n| n == "lib_b").unwrap();
        assert!(pos_b < pos_a);

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn test_resolve_circular_dependency() {
        let temp = temp_dir("circular");
        let lib_a = temp.join("lib_a");
        let lib_b = temp.join("lib_b");

        // myapp -> lib_a -> lib_b -> lib_a (cycle!)
        create_manifest(&temp, "myapp", &[("lib_a", "./lib_a")]);
        create_manifest(&lib_a, "lib_a", &[("lib_b", "../lib_b")]);
        create_manifest(&lib_b, "lib_b", &[("lib_a", "../lib_a")]);

        let manifest = Manifest::load(&temp.join("simple.toml")).unwrap();

        // Resolution should either:
        // 1. Return the graph, which will have a cycle
        // 2. Return an error if cycle is detected early
        let result = resolve(&manifest, &temp);
        assert!(matches!(result, Err(PkgError::CircularDependency(_))));

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn test_resolve_missing_path_dep() {
        let temp = temp_dir("missing");
        create_manifest(&temp, "myapp", &[("mylib", "./nonexistent")]);

        let manifest = Manifest::load(&temp.join("simple.toml")).unwrap();
        let result = resolve(&manifest, &temp);

        assert!(result.is_err());

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn test_resolve_version_dependency() {
        let temp = temp_dir("version-dep");

        let content = r#"[package]
name = "myapp"
version = "1.0.0"

[dependencies]
http = "1.0"
json = "^2.0"
"#;
        fs::write(temp.join("simple.toml"), content).unwrap();

        let graph = resolve_from_dir(&temp);

        assert_eq!(graph.len(), 2);
        assert!(graph.contains("http"));
        assert!(graph.contains("json"));

        let http = graph.get("http").unwrap();
        assert!(http.is_registry());

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn test_resolve_diamond_dependency() {
        let temp = temp_dir("diamond");
        let lib_a = temp.join("lib_a");
        let lib_b = temp.join("lib_b");
        let lib_c = temp.join("lib_c");

        // myapp -> lib_a, lib_b; lib_a -> lib_c; lib_b -> lib_c
        create_manifest(
            &temp,
            "myapp",
            &[("lib_a", "./lib_a"), ("lib_b", "./lib_b")],
        );
        create_manifest(&lib_a, "lib_a", &[("lib_c", "../lib_c")]);
        create_manifest(&lib_b, "lib_b", &[("lib_c", "../lib_c")]);
        create_manifest(&lib_c, "lib_c", &[]);

        let graph = resolve_from_dir(&temp);

        // lib_c should only appear once
        assert_eq!(graph.len(), 3);

        let order = graph.topological_order().unwrap();
        let names: Vec<_> = order.iter().map(|p| p.name.as_str()).collect();

        // lib_c should come before lib_a and lib_b
        let pos_a = names.iter().position(|&n| n == "lib_a").unwrap();
        let pos_b = names.iter().position(|&n| n == "lib_b").unwrap();
        let pos_c = names.iter().position(|&n| n == "lib_c").unwrap();

        assert!(pos_c < pos_a);
        assert!(pos_c < pos_b);

        let _ = fs::remove_dir_all(&temp);
    }
}

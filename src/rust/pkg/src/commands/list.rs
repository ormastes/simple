//! `simple list` and `simple tree` commands

use std::collections::HashMap;
use std::path::Path;

use crate::error::{PkgError, PkgResult};
use crate::linker::Linker;
use crate::lock::{LockFile, PackageSource};
use crate::manifest::Manifest;

/// Installed package information
#[derive(Debug)]
pub struct InstalledPackage {
    /// Package name
    pub name: String,
    /// Package version
    pub version: String,
    /// Source type ("path", "git", "registry")
    pub source_type: String,
    /// Whether the package is linked in deps/
    pub is_linked: bool,
}

/// List installed dependencies
pub fn list_dependencies(dir: &Path) -> PkgResult<Vec<InstalledPackage>> {
    let lock_path = dir.join("simple.lock");
    let lock = LockFile::load(&lock_path)?;

    let linker = Linker::new(dir);
    let linked = linker.list().unwrap_or_default();
    let linked_names: std::collections::HashSet<_> = linked.iter().map(|p| p.name.as_str()).collect();

    let packages: Vec<_> = lock
        .packages
        .iter()
        .map(|p| {
            let source_type = match &p.source {
                PackageSource::Path { .. } => "path",
                PackageSource::Git { .. } => "git",
                PackageSource::Registry { .. } => "registry",
            };

            InstalledPackage {
                name: p.name.clone(),
                version: p.version.clone(),
                source_type: source_type.to_string(),
                is_linked: linked_names.contains(p.name.as_str()),
            }
        })
        .collect();

    Ok(packages)
}

/// Dependency tree node
#[derive(Debug)]
pub struct TreeNode {
    /// Package name
    pub name: String,
    /// Package version
    pub version: String,
    /// Child dependencies
    pub children: Vec<TreeNode>,
}

/// Build a dependency tree
pub fn dependency_tree(dir: &Path) -> PkgResult<TreeNode> {
    let manifest_path = crate::find_manifest(dir)
        .ok_or_else(|| PkgError::ManifestNotFound(dir.display().to_string()))?;
    let lock_path = dir.join("simple.lock");

    let manifest = Manifest::load(&manifest_path)?;
    let lock = LockFile::load(&lock_path)?;

    // Build lookup maps
    let dep_graph = lock.dependency_graph();
    let version_map: HashMap<&str, &str> = lock
        .packages
        .iter()
        .map(|p| (p.name.as_str(), p.version.as_str()))
        .collect();

    let root_name = manifest.package.name.clone();
    let root_version = manifest.package.version.clone();

    // Build children from direct dependencies
    let children: Vec<TreeNode> = manifest
        .dependencies
        .keys()
        .map(|name| build_subtree(name, &version_map, &dep_graph, &mut std::collections::HashSet::new()))
        .collect();

    Ok(TreeNode {
        name: root_name,
        version: root_version,
        children,
    })
}

/// Build a subtree for a package
fn build_subtree<'a>(
    name: &str,
    version_map: &HashMap<&'a str, &'a str>,
    dep_graph: &HashMap<&'a str, Vec<&'a str>>,
    visited: &mut std::collections::HashSet<String>,
) -> TreeNode {
    let version = version_map
        .get(name)
        .map(|v| v.to_string())
        .unwrap_or_else(|| "?".to_string());

    // Prevent infinite recursion for circular dependencies
    if visited.contains(name) {
        return TreeNode {
            name: format!("{} (circular)", name),
            version,
            children: Vec::new(),
        };
    }
    visited.insert(name.to_string());

    let children: Vec<TreeNode> = dep_graph
        .get(name)
        .map(|deps| {
            deps.iter()
                .map(|d| build_subtree(d, version_map, dep_graph, visited))
                .collect()
        })
        .unwrap_or_default();

    visited.remove(name);

    TreeNode {
        name: name.to_string(),
        version,
        children,
    }
}

/// Format a dependency tree for display
pub fn format_tree(node: &TreeNode, prefix: &str, is_last: bool) -> String {
    let mut output = String::new();

    let connector = if prefix.is_empty() {
        // Root node - no connector
        ""
    } else if is_last {
        "└── "
    } else {
        "├── "
    };

    output.push_str(&format!("{}{}{} ({})\n", prefix, connector, node.name, node.version));

    let child_prefix = if prefix.is_empty() {
        String::new()
    } else if is_last {
        format!("{}    ", prefix)
    } else {
        format!("{}│   ", prefix)
    };

    for (i, child) in node.children.iter().enumerate() {
        let is_last_child = i == node.children.len() - 1;
        output.push_str(&format_tree(child, &child_prefix, is_last_child));
    }

    output
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::commands::install::install_dependencies;
    use crate::commands::test_helpers::{cleanup_test_project, setup_test_project};

    #[test]
    fn test_list_no_deps() {
        let temp_dir = setup_test_project("list", "list-empty");

        // Create empty lock file
        let lock = LockFile::default();
        lock.save(&temp_dir.join("simple.lock")).unwrap();

        let packages = list_dependencies(&temp_dir).unwrap();
        assert!(packages.is_empty());

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_list_with_deps() {
        use crate::commands::test_helpers::setup_with_path_dep;

        let (temp_dir, _dep_dir) = setup_with_path_dep("list", "list-deps", "mylib");
        install_dependencies(&temp_dir).unwrap();

        let packages = list_dependencies(&temp_dir).unwrap();
        assert_eq!(packages.len(), 1);
        assert_eq!(packages[0].name, "mylib");
        assert_eq!(packages[0].source_type, "path");
        assert!(packages[0].is_linked);

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_tree_simple() {
        use crate::commands::test_helpers::setup_with_path_dep;

        let (temp_dir, _dep_dir) = setup_with_path_dep("list", "tree-simple", "mylib");
        install_dependencies(&temp_dir).unwrap();

        let tree = dependency_tree(&temp_dir).unwrap();
        assert_eq!(tree.name, "tree-simple");
        assert_eq!(tree.children.len(), 1);
        assert_eq!(tree.children[0].name, "mylib");

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_tree_transitive() {
        use crate::commands::test_helpers::setup_transitive_deps;

        let (temp_dir, _lib_a, _lib_b) = setup_transitive_deps("list", "tree-trans");
        install_dependencies(&temp_dir).unwrap();

        let tree = dependency_tree(&temp_dir).unwrap();
        assert_eq!(tree.children.len(), 1);
        assert_eq!(tree.children[0].name, "lib_a");
        assert_eq!(tree.children[0].children.len(), 1);
        assert_eq!(tree.children[0].children[0].name, "lib_b");

        cleanup_test_project(&temp_dir);
    }

    #[test]
    fn test_format_tree() {
        let tree = TreeNode {
            name: "myapp".to_string(),
            version: "1.0.0".to_string(),
            children: vec![
                TreeNode {
                    name: "lib_a".to_string(),
                    version: "2.0.0".to_string(),
                    children: vec![TreeNode {
                        name: "lib_c".to_string(),
                        version: "1.0.0".to_string(),
                        children: Vec::new(),
                    }],
                },
                TreeNode {
                    name: "lib_b".to_string(),
                    version: "3.0.0".to_string(),
                    children: Vec::new(),
                },
            ],
        };

        let output = format_tree(&tree, "", true);
        assert!(output.contains("myapp (1.0.0)"));
        assert!(output.contains("lib_a (2.0.0)"));
        assert!(output.contains("lib_b (3.0.0)"));
        assert!(output.contains("lib_c (1.0.0)"));
    }
}

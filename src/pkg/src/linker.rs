//! Dependency linking - manages the deps/ folder in projects
//!
//! Creates symlinks for path dependencies and hard links for cached packages.

use std::path::{Path, PathBuf};

use crate::error::{PkgError, PkgResult};

/// Type of link used for a dependency
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LinkType {
    /// Symbolic link (for path dependencies)
    Symlink,
    /// Hard link (for cached packages on same filesystem)
    HardLink,
    /// Copy (fallback for cross-device)
    Copy,
}

/// Information about a linked package
#[derive(Debug, Clone)]
pub struct LinkedPackage {
    /// Package name
    pub name: String,
    /// Type of link
    pub link_type: LinkType,
    /// Target path the link points to
    pub target: PathBuf,
}

/// Manages the deps/ folder for a project
#[derive(Debug, Clone)]
pub struct Linker {
    /// Project directory
    project_dir: PathBuf,
    /// Dependencies directory (project_dir/deps)
    deps_dir: PathBuf,
}

impl Linker {
    /// Create a new linker for a project directory
    pub fn new(project_dir: &Path) -> Self {
        let deps_dir = project_dir.join("deps");
        Linker {
            project_dir: project_dir.to_path_buf(),
            deps_dir,
        }
    }

    /// Get the deps directory path
    pub fn deps_dir(&self) -> &Path {
        &self.deps_dir
    }

    /// Initialize the deps/ directory
    pub fn init(&self) -> PkgResult<()> {
        if !self.deps_dir.exists() {
            std::fs::create_dir_all(&self.deps_dir)?;
        }
        Ok(())
    }

    /// Link a path dependency as a symlink
    ///
    /// Creates: deps/<name> -> <source_path>
    pub fn link_path(&self, name: &str, source_path: &Path) -> PkgResult<()> {
        let dest = self.deps_dir.join(name);

        // Remove existing link if present
        if dest.exists() || dest.is_symlink() {
            self.unlink(name)?;
        }

        // Resolve source path to absolute
        let abs_source = if source_path.is_absolute() {
            source_path.to_path_buf()
        } else {
            self.project_dir
                .join(source_path)
                .canonicalize()
                .map_err(|e| PkgError::Link(format!("Failed to resolve path '{}': {}", source_path.display(), e)))?
        };

        // Create symlink
        create_symlink(&abs_source, &dest)?;

        Ok(())
    }

    /// Link a cached package (hard link or copy)
    ///
    /// Creates: deps/<name> -> <cache_path> (hard link or copy)
    pub fn link_cached(&self, name: &str, cache_path: &Path) -> PkgResult<()> {
        let dest = self.deps_dir.join(name);

        // Remove existing link if present
        if dest.exists() || dest.is_symlink() {
            self.unlink(name)?;
        }

        // Try hard link first, fall back to copy
        if try_hard_link_dir(cache_path, &dest).is_ok() {
            return Ok(());
        }

        // Fall back to copy
        copy_dir_all(cache_path, &dest)?;

        Ok(())
    }

    /// Remove a linked dependency
    pub fn unlink(&self, name: &str) -> PkgResult<()> {
        let dest = self.deps_dir.join(name);

        if dest.is_symlink() {
            // Remove symlink
            #[cfg(unix)]
            std::fs::remove_file(&dest)?;
            #[cfg(windows)]
            {
                // Windows: junctions are directories
                if dest.is_dir() {
                    std::fs::remove_dir(&dest)?;
                } else {
                    std::fs::remove_file(&dest)?;
                }
            }
        } else if dest.exists() {
            // Remove directory (hard links or copies)
            std::fs::remove_dir_all(&dest)?;
        }

        Ok(())
    }

    /// Clean the entire deps/ directory
    pub fn clean(&self) -> PkgResult<()> {
        if self.deps_dir.exists() {
            std::fs::remove_dir_all(&self.deps_dir)?;
        }
        Ok(())
    }

    /// List all linked dependencies
    pub fn list(&self) -> PkgResult<Vec<LinkedPackage>> {
        let mut packages = Vec::new();

        if !self.deps_dir.exists() {
            return Ok(packages);
        }

        for entry in std::fs::read_dir(&self.deps_dir)? {
            let entry = entry?;
            let name = entry.file_name().to_string_lossy().to_string();
            let path = entry.path();

            let (link_type, target) = if path.is_symlink() {
                let target = std::fs::read_link(&path).unwrap_or_else(|_| PathBuf::from("unknown"));
                (LinkType::Symlink, target)
            } else if path.is_dir() {
                // Hard link or copy - can't easily distinguish
                (LinkType::Copy, path.clone())
            } else {
                continue;
            };

            packages.push(LinkedPackage {
                name,
                link_type,
                target,
            });
        }

        Ok(packages)
    }

    /// Check if a package is linked
    pub fn is_linked(&self, name: &str) -> bool {
        let dest = self.deps_dir.join(name);
        dest.exists() || dest.is_symlink()
    }
}

/// Create a symlink (platform-specific)
#[cfg(unix)]
fn create_symlink(src: &Path, dst: &Path) -> PkgResult<()> {
    std::os::unix::fs::symlink(src, dst).map_err(|e| {
        PkgError::Link(format!(
            "Failed to create symlink {} -> {}: {}",
            dst.display(),
            src.display(),
            e
        ))
    })
}

#[cfg(windows)]
fn create_symlink(src: &Path, dst: &Path) -> PkgResult<()> {
    // On Windows, prefer junction for directories (no admin required)
    if src.is_dir() {
        // Try junction first
        match std::process::Command::new("cmd")
            .args(["/C", "mklink", "/J"])
            .arg(dst)
            .arg(src)
            .output()
        {
            Ok(output) if output.status.success() => return Ok(()),
            _ => {}
        }

        // Fall back to directory symlink (may require admin)
        std::os::windows::fs::symlink_dir(src, dst).map_err(|e| {
            PkgError::Link(format!(
                "Failed to create symlink {} -> {}: {}",
                dst.display(),
                src.display(),
                e
            ))
        })
    } else {
        std::os::windows::fs::symlink_file(src, dst).map_err(|e| {
            PkgError::Link(format!(
                "Failed to create symlink {} -> {}: {}",
                dst.display(),
                src.display(),
                e
            ))
        })
    }
}

/// Walk a directory and apply a file operation to each file.
/// Creates directories automatically.
fn walk_dir_apply<F>(src: &Path, dst: &Path, file_op: F) -> PkgResult<()>
where
    F: Fn(&Path, &Path) -> PkgResult<()>,
{
    std::fs::create_dir_all(dst)?;

    for entry in walkdir::WalkDir::new(src) {
        let entry = entry.map_err(|e| PkgError::Link(e.to_string()))?;
        let src_path = entry.path();
        let rel_path = src_path.strip_prefix(src).map_err(|e| PkgError::Link(e.to_string()))?;
        let dst_path = dst.join(rel_path);

        if entry.file_type().is_dir() {
            std::fs::create_dir_all(&dst_path)?;
        } else if entry.file_type().is_file() {
            file_op(src_path, &dst_path)?;
        }
    }

    Ok(())
}

/// Try to create hard links for all files in a directory
fn try_hard_link_dir(src: &Path, dst: &Path) -> PkgResult<()> {
    walk_dir_apply(src, dst, |src_path, dst_path| {
        std::fs::hard_link(src_path, dst_path).map_err(|e| {
            let _ = std::fs::remove_dir_all(dst);
            PkgError::Link(format!("Hard link failed for {}: {}", src_path.display(), e))
        })
    })
}

/// Copy a directory recursively
fn copy_dir_all(src: &Path, dst: &Path) -> PkgResult<()> {
    walk_dir_apply(src, dst, |src_path, dst_path| {
        std::fs::copy(src_path, dst_path)?;
        Ok(())
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn temp_dir(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "simple-linker-test-{}-{}",
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

    /// Helper to setup test linker with a linked dependency
    fn setup_linked_linker(test_name: &str, lib_name: &str) -> (PathBuf, Linker) {
        let temp = temp_dir(test_name);
        let project_dir = temp.join("project");
        let dep_dir = temp.join(lib_name);

        fs::create_dir_all(&project_dir).unwrap();
        fs::create_dir_all(&dep_dir).unwrap();

        let linker = Linker::new(&project_dir);
        linker.init().unwrap();
        linker.link_path(lib_name, &dep_dir).unwrap();

        (temp, linker)
    }

    #[test]
    fn test_linker_init() {
        let temp = temp_dir("init");
        let project_dir = temp.join("project");
        fs::create_dir_all(&project_dir).unwrap();

        let linker = Linker::new(&project_dir);
        linker.init().unwrap();

        assert!(linker.deps_dir().exists());

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn test_link_path_dependency() {
        let temp = temp_dir("link-path");
        let project_dir = temp.join("project");
        let dep_dir = temp.join("mylib");

        fs::create_dir_all(&project_dir).unwrap();
        fs::create_dir_all(&dep_dir).unwrap();

        // Create a file in the dependency
        fs::write(dep_dir.join("lib.spl"), "// lib").unwrap();

        let linker = Linker::new(&project_dir);
        linker.init().unwrap();
        linker.link_path("mylib", &dep_dir).unwrap();

        let link_path = linker.deps_dir().join("mylib");
        assert!(link_path.exists() || link_path.is_symlink());

        // Should be able to read through the link
        let content = fs::read_to_string(link_path.join("lib.spl")).unwrap();
        assert_eq!(content, "// lib");

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn test_unlink() {
        let (temp, linker) = setup_linked_linker("unlink", "mylib");

        assert!(linker.is_linked("mylib"));

        linker.unlink("mylib").unwrap();

        assert!(!linker.is_linked("mylib"));

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn test_list_linked() {
        let temp = temp_dir("list");
        let project_dir = temp.join("project");
        let dep1 = temp.join("lib1");
        let dep2 = temp.join("lib2");

        fs::create_dir_all(&project_dir).unwrap();
        fs::create_dir_all(&dep1).unwrap();
        fs::create_dir_all(&dep2).unwrap();

        let linker = Linker::new(&project_dir);
        linker.init().unwrap();
        linker.link_path("lib1", &dep1).unwrap();
        linker.link_path("lib2", &dep2).unwrap();

        let linked = linker.list().unwrap();
        assert_eq!(linked.len(), 2);

        let names: Vec<_> = linked.iter().map(|p| p.name.as_str()).collect();
        assert!(names.contains(&"lib1"));
        assert!(names.contains(&"lib2"));

        let _ = fs::remove_dir_all(&temp);
    }

    #[test]
    fn test_clean() {
        let (_temp, linker) = setup_linked_linker("clean", "mylib");

        assert!(linker.deps_dir().exists());

        linker.clean().unwrap();

        assert!(!linker.deps_dir().exists());
    }

    #[test]
    fn test_link_overwrites_existing() {
        let temp = temp_dir("overwrite");
        let project_dir = temp.join("project");
        let dep1 = temp.join("lib1");
        let dep2 = temp.join("lib2");

        fs::create_dir_all(&project_dir).unwrap();
        fs::create_dir_all(&dep1).unwrap();
        fs::create_dir_all(&dep2).unwrap();

        fs::write(dep1.join("file.txt"), "version1").unwrap();
        fs::write(dep2.join("file.txt"), "version2").unwrap();

        let linker = Linker::new(&project_dir);
        linker.init().unwrap();

        // Link to first version
        linker.link_path("mylib", &dep1).unwrap();
        let content = fs::read_to_string(linker.deps_dir().join("mylib/file.txt")).unwrap();
        assert_eq!(content, "version1");

        // Link to second version (should overwrite)
        linker.link_path("mylib", &dep2).unwrap();
        let content = fs::read_to_string(linker.deps_dir().join("mylib/file.txt")).unwrap();
        assert_eq!(content, "version2");

        let _ = fs::remove_dir_all(&temp);
    }
}

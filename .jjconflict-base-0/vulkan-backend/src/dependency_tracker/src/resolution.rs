//! # Module Resolution
//!
//! This module implements the module path resolution semantics from
//! `verification/module_resolution/src/ModuleResolution.lean`.
//!
//! ## Proven Properties (Lean theorems)
//!
//! 1. `wellformed_not_ambiguous`: In well-formed filesystems, resolution never returns ambiguous
//! 2. `unique_path_form`: Unique resolution returns one of the two expected path forms
//! 3. `unique_implies_exists`: Unique resolution implies the file exists
//! 4. `notfound_means_neither`: Not found means neither file nor directory exists

use std::collections::HashSet;
use std::path::{Path, PathBuf};

/// A module path segment is a non-empty string identifier.
///
/// Corresponds to Lean: `structure Segment where name : String; nonEmpty : name ≠ ""`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Segment {
    name: String,
}

impl Segment {
    /// Create a new segment. Returns None if the name is empty.
    pub fn new(name: impl Into<String>) -> Option<Self> {
        let name = name.into();
        if name.is_empty() {
            None
        } else {
            Some(Self { name })
        }
    }

    /// Get the segment name.
    pub fn name(&self) -> &str {
        &self.name
    }
}

/// A module path is a non-empty list of segments (e.g., `crate.sys.http`).
///
/// Corresponds to Lean: `structure ModPath where segments : List Segment; nonEmpty : segments ≠ []`
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ModPath {
    segments: Vec<Segment>,
}

impl ModPath {
    /// Create a new module path. Returns None if segments is empty.
    pub fn new(segments: Vec<Segment>) -> Option<Self> {
        if segments.is_empty() {
            None
        } else {
            Some(Self { segments })
        }
    }

    /// Parse a dot-separated module path string (e.g., "crate.sys.http").
    pub fn parse(path: &str) -> Option<Self> {
        let segments: Vec<Segment> = path.split('.').filter_map(Segment::new).collect();
        Self::new(segments)
    }

    /// Get the segments.
    pub fn segments(&self) -> &[Segment] {
        &self.segments
    }

    /// Check if this path starts with "crate".
    pub fn is_absolute(&self) -> bool {
        self.segments.first().map_or(false, |s| s.name() == "crate")
    }

    /// Get the path without the leading "crate" segment.
    pub fn without_crate_prefix(&self) -> Option<ModPath> {
        if self.is_absolute() && self.segments.len() > 1 {
            ModPath::new(self.segments[1..].to_vec())
        } else if !self.is_absolute() {
            Some(self.clone())
        } else {
            None
        }
    }
}

/// Module can be either a file or a directory with __init__.spl.
///
/// Corresponds to Lean: `inductive FileKind | file | directory`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileKind {
    /// foo.spl
    File,
    /// foo/__init__.spl
    Directory,
}

/// The result of resolving a module path.
///
/// Corresponds to Lean: `inductive ResolutionResult`
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolutionResult {
    /// Successfully resolved to a unique path.
    Unique { kind: FileKind, path: PathBuf },
    /// Ambiguous: both file and directory forms exist.
    Ambiguous {
        file_path: PathBuf,
        dir_path: PathBuf,
    },
    /// Module not found.
    NotFound,
}

/// File system state: tracks which files exist.
///
/// Corresponds to Lean: `structure FileSystem where files : List String`
#[derive(Debug, Clone, Default)]
pub struct FileSystem {
    files: HashSet<PathBuf>,
}

impl FileSystem {
    /// Create a new empty filesystem.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a filesystem from an iterator of paths.
    pub fn from_paths(paths: impl IntoIterator<Item = impl Into<PathBuf>>) -> Self {
        Self {
            files: paths.into_iter().map(Into::into).collect(),
        }
    }

    /// Add a file to the filesystem.
    pub fn add_file(&mut self, path: impl Into<PathBuf>) {
        self.files.insert(path.into());
    }

    /// Check if a file exists in the filesystem.
    ///
    /// Corresponds to Lean: `def FileSystem.exists (fs : FileSystem) (path : String) : Bool`
    pub fn exists(&self, path: &Path) -> bool {
        self.files.contains(path)
    }

    /// Create a filesystem from the actual filesystem.
    pub fn from_directory(root: &Path) -> std::io::Result<Self> {
        let mut fs = Self::new();
        Self::scan_directory(root, &mut fs)?;
        Ok(fs)
    }

    fn scan_directory(dir: &Path, fs: &mut FileSystem) -> std::io::Result<()> {
        if dir.is_dir() {
            for entry in std::fs::read_dir(dir)? {
                let entry = entry?;
                let path = entry.path();
                if path.is_dir() {
                    Self::scan_directory(&path, fs)?;
                } else if path.extension().map_or(false, |e| e == "spl") {
                    fs.add_file(path);
                }
            }
        }
        Ok(())
    }
}

/// Convert a module path to a filesystem path for file resolution.
///
/// Corresponds to Lean: `def toFilePath (root : String) (mp : ModPath) : String`
pub fn to_file_path(root: &Path, mp: &ModPath) -> PathBuf {
    let mut path = root.to_path_buf();
    for segment in mp.segments() {
        path.push(segment.name());
    }
    path.set_extension("spl");
    path
}

/// Convert a module path to a filesystem path for directory resolution.
///
/// Corresponds to Lean: `def toDirPath (root : String) (mp : ModPath) : String`
pub fn to_dir_path(root: &Path, mp: &ModPath) -> PathBuf {
    let mut path = root.to_path_buf();
    for segment in mp.segments() {
        path.push(segment.name());
    }
    path.push("__init__.spl");
    path
}

/// Resolve a module path in a filesystem.
///
/// Corresponds to Lean: `def resolve (fs : FileSystem) (root : String) (mp : ModPath) : ResolutionResult`
///
/// ## Resolution Rules
///
/// 1. Try `<path>.spl` (file module)
/// 2. Try `<path>/__init__.spl` (directory module)
/// 3. If both exist, return Ambiguous
/// 4. If one exists, return Unique
/// 5. If neither exists, return NotFound
pub fn resolve(fs: &FileSystem, root: &Path, mp: &ModPath) -> ResolutionResult {
    let file_path = to_file_path(root, mp);
    let dir_path = to_dir_path(root, mp);

    let file_exists = fs.exists(&file_path);
    let dir_exists = fs.exists(&dir_path);

    match (file_exists, dir_exists) {
        (true, true) => ResolutionResult::Ambiguous {
            file_path,
            dir_path,
        },
        (true, false) => ResolutionResult::Unique {
            kind: FileKind::File,
            path: file_path,
        },
        (false, true) => ResolutionResult::Unique {
            kind: FileKind::Directory,
            path: dir_path,
        },
        (false, false) => ResolutionResult::NotFound,
    }
}

/// A filesystem is well-formed if no module has both file and directory forms.
///
/// Corresponds to Lean: `def wellFormed (fs : FileSystem) (root : String) : Prop`
///
/// This is the key invariant that ensures resolution is unambiguous.
pub fn well_formed(fs: &FileSystem, _root: &Path) -> bool {
    // For a filesystem to be well-formed, we need to check that no module
    // path resolves to both a file and directory.
    // We check this by looking at all .spl files and ensuring no foo.spl
    // coexists with foo/__init__.spl
    for file_path in &fs.files {
        if file_path.file_name().map_or(false, |n| n == "__init__.spl") {
            // This is a directory module; check if sibling file exists
            if let Some(parent) = file_path.parent() {
                let mut file_version = parent.to_path_buf();
                file_version.set_extension("spl");
                if fs.exists(&file_version) {
                    return false;
                }
            }
        } else if file_path.extension().map_or(false, |e| e == "spl") {
            // This is a file module; check if directory version exists
            let stem = file_path.with_extension("");
            let dir_version = stem.join("__init__.spl");
            if fs.exists(&dir_version) {
                return false;
            }
        }
    }
    true
}

/// Resolve using the actual filesystem.
///
/// This is a convenience function that creates a FileSystem from the actual
/// filesystem and resolves the path.
pub fn resolve_on_disk(root: &Path, mp: &ModPath) -> std::io::Result<ResolutionResult> {
    let file_path = to_file_path(root, mp);
    let dir_path = to_dir_path(root, mp);

    let file_exists = file_path.exists();
    let dir_exists = dir_path.exists();

    Ok(match (file_exists, dir_exists) {
        (true, true) => ResolutionResult::Ambiguous {
            file_path,
            dir_path,
        },
        (true, false) => ResolutionResult::Unique {
            kind: FileKind::File,
            path: file_path,
        },
        (false, true) => ResolutionResult::Unique {
            kind: FileKind::Directory,
            path: dir_path,
        },
        (false, false) => ResolutionResult::NotFound,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn segment_rejects_empty() {
        assert!(Segment::new("").is_none());
    }

    #[test]
    fn segment_accepts_nonempty() {
        assert!(Segment::new("foo").is_some());
    }

    #[test]
    fn modpath_rejects_empty() {
        assert!(ModPath::new(vec![]).is_none());
    }

    #[test]
    fn modpath_parse_simple() {
        let mp = ModPath::parse("crate.sys.http").unwrap();
        assert_eq!(mp.segments().len(), 3);
        assert_eq!(mp.segments()[0].name(), "crate");
        assert_eq!(mp.segments()[1].name(), "sys");
        assert_eq!(mp.segments()[2].name(), "http");
    }

    #[test]
    fn modpath_is_absolute() {
        let abs = ModPath::parse("crate.foo").unwrap();
        let rel = ModPath::parse("foo.bar").unwrap();
        assert!(abs.is_absolute());
        assert!(!rel.is_absolute());
    }

    #[test]
    fn to_file_path_test() {
        let root = Path::new("/project/src");
        let mp = ModPath::parse("sys.http").unwrap();
        let path = to_file_path(root, &mp);
        assert_eq!(path, PathBuf::from("/project/src/sys/http.spl"));
    }

    #[test]
    fn to_dir_path_test() {
        let root = Path::new("/project/src");
        let mp = ModPath::parse("sys.http").unwrap();
        let path = to_dir_path(root, &mp);
        assert_eq!(path, PathBuf::from("/project/src/sys/http/__init__.spl"));
    }

    // Theorem: wellformed_not_ambiguous
    // In a well-formed filesystem, resolution never returns ambiguous.
    #[test]
    fn theorem_wellformed_not_ambiguous() {
        let root = Path::new("/project/src");
        let mp = ModPath::parse("foo").unwrap();

        // Well-formed: only file exists
        let mut fs = FileSystem::new();
        fs.add_file("/project/src/foo.spl");
        assert!(well_formed(&fs, root));
        assert!(matches!(
            resolve(&fs, root, &mp),
            ResolutionResult::Unique {
                kind: FileKind::File,
                ..
            }
        ));

        // Well-formed: only directory exists
        let mut fs = FileSystem::new();
        fs.add_file("/project/src/foo/__init__.spl");
        assert!(well_formed(&fs, root));
        assert!(matches!(
            resolve(&fs, root, &mp),
            ResolutionResult::Unique {
                kind: FileKind::Directory,
                ..
            }
        ));

        // Not well-formed: both exist
        let mut fs = FileSystem::new();
        fs.add_file("/project/src/foo.spl");
        fs.add_file("/project/src/foo/__init__.spl");
        assert!(!well_formed(&fs, root));
        assert!(matches!(
            resolve(&fs, root, &mp),
            ResolutionResult::Ambiguous { .. }
        ));
    }

    // Theorem: unique_path_form
    // Unique resolution returns one of the two expected path forms.
    #[test]
    fn theorem_unique_path_form() {
        let root = Path::new("/project/src");
        let mp = ModPath::parse("foo.bar").unwrap();

        let mut fs = FileSystem::new();
        fs.add_file("/project/src/foo/bar.spl");

        if let ResolutionResult::Unique { kind, path } = resolve(&fs, root, &mp) {
            assert!(
                (kind == FileKind::File && path == to_file_path(root, &mp))
                    || (kind == FileKind::Directory && path == to_dir_path(root, &mp))
            );
        } else {
            panic!("Expected Unique result");
        }
    }

    // Theorem: unique_implies_exists
    // Unique resolution implies the file exists.
    #[test]
    fn theorem_unique_implies_exists() {
        let root = Path::new("/project/src");
        let mp = ModPath::parse("foo").unwrap();

        let mut fs = FileSystem::new();
        fs.add_file("/project/src/foo.spl");

        if let ResolutionResult::Unique { path, .. } = resolve(&fs, root, &mp) {
            assert!(fs.exists(&path));
        } else {
            panic!("Expected Unique result");
        }
    }

    // Theorem: notfound_means_neither
    // Not found means neither file nor directory exists.
    #[test]
    fn theorem_notfound_means_neither() {
        let root = Path::new("/project/src");
        let mp = ModPath::parse("nonexistent").unwrap();

        let fs = FileSystem::new();

        assert!(matches!(
            resolve(&fs, root, &mp),
            ResolutionResult::NotFound
        ));
        assert!(!fs.exists(&to_file_path(root, &mp)));
        assert!(!fs.exists(&to_dir_path(root, &mp)));
    }

    #[test]
    fn resolve_deterministic() {
        let root = Path::new("/project/src");
        let mp = ModPath::parse("foo").unwrap();

        let mut fs = FileSystem::new();
        fs.add_file("/project/src/foo.spl");

        // Same path always resolves the same way
        let r1 = resolve(&fs, root, &mp);
        let r2 = resolve(&fs, root, &mp);
        assert_eq!(r1, r2);
    }
}

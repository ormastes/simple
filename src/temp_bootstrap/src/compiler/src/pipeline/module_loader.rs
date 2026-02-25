//! Module loading and import resolution utilities.
//!
//! This module handles resolving `use` statements to filesystem paths and
//! loading the corresponding modules. It supports:
//!
//! - Numbered directory prefixes: `compiler.common` -> `src/compiler/00.common/`
//! - Standard library imports: `std.X` -> `src/lib/*/X/` (searches subdirs)
//! - Relative imports: `use ..X` (parent directory)
//! - Sibling imports: `use X` (same directory)
//! - Directory modules: `mod.spl` or `__init__.spl`
//! - Deep search: `use parser.*` from anywhere finds `10.frontend/parser/`

use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

use simple_parser::ast::{ImportTarget, Module, Node, UseStmt};

use crate::CompileError;

// ========== Directory Index for fast deep search ==========

/// Pre-built index mapping logical directory and file names to their full paths
/// within the compiler source tree. Built once and cached.
struct DirIndex {
    /// Maps directory names (stripped of NN. prefix) to their full paths
    dirs: HashMap<String, Vec<PathBuf>>,
    /// Maps file names (without .spl extension) to their full paths
    files: HashMap<String, Vec<PathBuf>>,
}

impl DirIndex {
    fn build(root: &Path) -> Self {
        let mut idx = DirIndex {
            dirs: HashMap::new(),
            files: HashMap::new(),
        };
        idx.scan(root);
        idx
    }

    fn scan(&mut self, dir: &Path) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let name = entry.file_name().to_string_lossy().to_string();
                if name.starts_with('.') {
                    continue;
                }
                // Skip symlinks to avoid infinite loops
                if entry.path().read_link().is_ok() {
                    continue;
                }

                if entry.file_type().map_or(false, |ft| ft.is_dir()) {
                    let logical = strip_numbered_prefix(&name);
                    self.dirs.entry(logical).or_default().push(entry.path());
                    self.scan(&entry.path());
                } else if name.ends_with(".spl") {
                    let base = name.strip_suffix(".spl").unwrap().to_string();
                    self.files.entry(base).or_default().push(entry.path());
                }
            }
        }
    }

    /// Try to resolve segments using the pre-built index.
    fn resolve(&self, segments: &[String], target_names: &[String]) -> Option<PathBuf> {
        if segments.is_empty() {
            if let Some(name) = target_names.first() {
                if let Some(paths) = self.files.get(name.as_str()) {
                    return paths.first().cloned();
                }
            }
            return None;
        }

        let first = &segments[0];

        // Try finding the first segment as a directory in our index
        if let Some(dirs) = self.dirs.get(first.as_str()) {
            for dir in dirs {
                if let Some(resolved) = resolve_from_segments(dir, &segments[1..], target_names) {
                    return Some(resolved);
                }
            }
        }

        // Try finding the first segment as a file (target is a symbol within it)
        if let Some(paths) = self.files.get(first.as_str()) {
            if !paths.is_empty() {
                return paths.first().cloned();
            }
        }

        None
    }
}

fn strip_numbered_prefix(name: &str) -> String {
    if let Some(dot_pos) = name.find('.') {
        let prefix = &name[..dot_pos];
        if prefix.chars().all(|c| c.is_ascii_digit()) {
            return name[dot_pos + 1..].to_string();
        }
    }
    name.to_string()
}

/// Get or build the compiler directory index. The index is built once per
/// project root and cached in a global OnceLock.
static COMPILER_INDEX: OnceLock<Option<DirIndex>> = OnceLock::new();

fn get_compiler_index(project_root: Option<&Path>) -> Option<&'static DirIndex> {
    COMPILER_INDEX
        .get_or_init(|| {
            project_root.and_then(|root| {
                let compiler_dir = root.join("src").join("compiler");
                if compiler_dir.is_dir() {
                    Some(DirIndex::build(&compiler_dir))
                } else {
                    None
                }
            })
        })
        .as_ref()
}

/// Find the project root by walking up from a file path looking for
/// a directory that contains `src/compiler/` or `src/lib/`.
fn find_project_root(start: &Path) -> Option<PathBuf> {
    let mut current = if start.is_file() {
        start.parent()?.to_path_buf()
    } else {
        start.to_path_buf()
    };

    loop {
        // Check if this looks like the project root
        if current.join("src").join("compiler").exists() || current.join("src").join("lib").exists()
        {
            return Some(current);
        }
        if !current.pop() {
            return None;
        }
    }
}

/// Build a mapping from logical names to actual directory names for a given parent directory.
/// E.g., for `src/compiler/`:
///   "common" -> ["00.common"] (numbered form only; "common" dir is handled by exact match)
///   "frontend" -> ["10.frontend"]
///   "types" -> ["30.types"]
/// A logical name can map to multiple directories when both numbered and non-numbered exist.
fn build_numbered_dir_mapping(parent: &Path) -> HashMap<String, Vec<String>> {
    let mut mapping: HashMap<String, Vec<String>> = HashMap::new();

    if let Ok(entries) = fs::read_dir(parent) {
        for entry in entries.flatten() {
            if entry.file_type().map_or(false, |ft| ft.is_dir()) {
                let dir_name = entry.file_name().to_string_lossy().to_string();

                // Check if the directory has a numbered prefix like "00.common"
                if let Some(dot_pos) = dir_name.find('.') {
                    let prefix = &dir_name[..dot_pos];
                    if prefix.chars().all(|c| c.is_ascii_digit()) {
                        // This is a numbered directory
                        let logical_name = dir_name[dot_pos + 1..].to_string();
                        mapping
                            .entry(logical_name)
                            .or_default()
                            .push(dir_name.clone());
                    }
                }
            }
        }
    }

    mapping
}

/// Resolve a file within a directory, trying various extensions and patterns.
/// Tries: `name.spl`, `name/mod.spl`, `name/__init__.spl`, `name/name.spl`
fn resolve_file_in_dir(dir: &Path, name: &str) -> Option<PathBuf> {
    // Try direct file
    let spl_file = dir.join(format!("{}.spl", name));
    if spl_file.is_file() {
        return Some(spl_file);
    }

    // Try directory with mod.spl
    let mod_file = dir.join(name).join("mod.spl");
    if mod_file.is_file() {
        return Some(mod_file);
    }

    // Try directory with __init__.spl
    let init_file = dir.join(name).join("__init__.spl");
    if init_file.is_file() {
        return Some(init_file);
    }

    // Try numbered directory alternatives
    let mapping = build_numbered_dir_mapping(dir);
    if let Some(actual_names) = mapping.get(name) {
        for actual_name in actual_names {
            let spl_file = dir.join(format!("{}.spl", actual_name));
            if spl_file.is_file() {
                return Some(spl_file);
            }
            let mod_file = dir.join(actual_name).join("mod.spl");
            if mod_file.is_file() {
                return Some(mod_file);
            }
            let init_file = dir.join(actual_name).join("__init__.spl");
            if init_file.is_file() {
                return Some(init_file);
            }
        }
    }

    // Try name/name.spl (common pattern in Simple: a directory `foo/` with main file `foo/foo.spl`)
    let same_name = dir.join(name).join(format!("{}.spl", name));
    if same_name.is_file() {
        return Some(same_name);
    }

    None
}

/// Recursively loads a module and all its imports, flattening imported items
/// into the root module.
pub fn load_module_with_imports(
    path: &Path,
    visited: &mut HashSet<PathBuf>,
) -> Result<Module, CompileError> {
    let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    if !visited.insert(path.clone()) {
        return Ok(Module {
            name: None,
            items: Vec::new(),
        });
    }

    let source = fs::read_to_string(&path).map_err(|e| CompileError::Io(format!("{e}")))?;
    let mut parser = simple_parser::Parser::new(&source);
    let module = parser
        .parse()
        .map_err(|e| CompileError::Parse(format!("{e}")))?;

    let project_root = find_project_root(&path);
    let file_dir = path.parent().unwrap_or(Path::new("."));

    let mut items = Vec::new();
    for item in module.items {
        match &item {
            Node::UseStmt(use_stmt) => {
                if let Some(resolved) =
                    resolve_use_to_path(use_stmt, file_dir, project_root.as_deref())
                {
                    match load_module_with_imports(&resolved, visited) {
                        Ok(imported) => {
                            items.extend(imported.items);
                            continue;
                        }
                        Err(_) => {
                            // If the imported module fails to load (parse error, etc.),
                            // skip it silently and keep the use statement as-is.
                            // The interpreter will treat it as a no-op.
                        }
                    }
                }
                // Keep the use statement node (will be a no-op in interpreter)
                items.push(item);
            }
            Node::CommonUseStmt(common_use) => {
                // common use statements - try to resolve and load
                let use_stmt = UseStmt {
                    span: common_use.span.clone(),
                    path: common_use.path.clone(),
                    target: common_use.target.clone(),
                };
                if let Some(resolved) =
                    resolve_use_to_path(&use_stmt, file_dir, project_root.as_deref())
                {
                    match load_module_with_imports(&resolved, visited) {
                        Ok(imported) => {
                            items.extend(imported.items);
                            continue;
                        }
                        Err(_) => {}
                    }
                }
                items.push(item);
            }
            _ => {
                items.push(item);
            }
        }
    }

    Ok(Module {
        name: module.name,
        items,
    })
}

/// Resolve a `use` statement to a filesystem path.
///
/// Handles these patterns:
/// 1. `use compiler.common.X` -> `src/compiler/00.common/X.spl` (numbered prefix)
/// 2. `use std.X.Y` / `use lib.X.Y` -> searches `src/lib/*/X/Y.spl`
/// 3. `use ..X` -> parent directory relative import
/// 4. `use X` -> sibling import (same directory)
/// 5. `use app.X.Y` -> `src/app/X/Y.spl`
fn resolve_use_to_path(
    use_stmt: &UseStmt,
    file_dir: &Path,
    project_root: Option<&Path>,
) -> Option<PathBuf> {
    let segments = &use_stmt.path.segments;
    if segments.is_empty() {
        return resolve_target_only(use_stmt, file_dir, project_root);
    }

    // Collect all path components: segments + target name(s)
    let target_names = extract_target_names(&use_stmt.target);

    // Handle relative imports
    let first = &segments[0];

    // "." prefix means current directory
    if first == "." {
        return resolve_from_segments(file_dir, &segments[1..], &target_names);
    }

    // ".." prefix means parent directory
    if first == ".." || first.starts_with("..") {
        return resolve_relative_import(segments, &target_names, file_dir);
    }

    // "..." prefix means grandparent directory
    if first == "..." {
        if let Some(grandparent) = file_dir.parent().and_then(|p| p.parent()) {
            return resolve_from_segments(grandparent, &segments[1..], &target_names);
        }
    }

    // Handle well-known top-level modules
    if let Some(root) = project_root {
        let src_dir = root.join("src");

        match first.as_str() {
            "crate" => {
                // Absolute path from project source root
                return resolve_from_segments(&src_dir, &segments[1..], &target_names);
            }
            "compiler" => {
                if let Some(resolved) =
                    resolve_from_segments(&src_dir.join("compiler"), &segments[1..], &target_names)
                {
                    return Some(resolved);
                }
            }
            "std" | "lib" => {
                if let Some(resolved) =
                    resolve_std_import(&src_dir.join("lib"), &segments[1..], &target_names)
                {
                    return Some(resolved);
                }
            }
            "app" => {
                if let Some(resolved) =
                    resolve_from_segments(&src_dir.join("app"), &segments[1..], &target_names)
                {
                    return Some(resolved);
                }
            }
            "runtime" => {
                if let Some(resolved) =
                    resolve_from_segments(&src_dir.join("runtime"), &segments[1..], &target_names)
                {
                    return Some(resolved);
                }
            }
            _ => {}
        }
    }

    // Walk up the directory tree from file_dir, trying to resolve at each level.
    // This handles cases like `use parser.*` from deep within the compiler tree,
    // where `parser` is a sibling or cousin directory at some ancestor level.
    {
        let mut search_dir = Some(file_dir.to_path_buf());
        while let Some(dir) = search_dir {
            if let Some(resolved) = resolve_from_segments(&dir, segments, &target_names) {
                return Some(resolved);
            }

            // Stop walking up once we reach the project root or src directory
            if let Some(root) = project_root {
                if dir == root.join("src") || dir == *root {
                    break;
                }
            }
            search_dir = dir.parent().map(|p| p.to_path_buf());
        }
    }

    // Use the cached DirIndex for fast deep search within compiler tree.
    // This handles `use parser.*` from anywhere, finding `10.frontend/parser/`.
    if let Some(idx) = get_compiler_index(project_root) {
        if let Some(resolved) = idx.resolve(segments, &target_names) {
            return Some(resolved);
        }
    }

    if let Some(root) = project_root {
        // Also try from src/ directly
        let src_dir = root.join("src");
        if let Some(resolved) = resolve_from_segments(&src_dir, segments, &target_names) {
            return Some(resolved);
        }

        // Last resort: try as a stdlib import without std/lib prefix.
        // This handles `use testing.{describe, it, expect}` which lives in src/lib/.
        let lib_dir = src_dir.join("lib");
        if lib_dir.is_dir() {
            if let Some(resolved) = resolve_std_import(&lib_dir, segments, &target_names) {
                return Some(resolved);
            }
        }
    }

    // Fallback: old-style simple resolution (original behavior)
    resolve_use_to_path_simple(use_stmt, file_dir)
}

/// Extract target file names from an ImportTarget.
fn extract_target_names(target: &ImportTarget) -> Vec<String> {
    match target {
        ImportTarget::Single(name) => vec![name.clone()],
        ImportTarget::Aliased { name, .. } => vec![name.clone()],
        ImportTarget::Group(targets) => targets
            .iter()
            .filter_map(|t| match t {
                ImportTarget::Single(name) => Some(name.clone()),
                ImportTarget::Aliased { name, .. } => Some(name.clone()),
                _ => None,
            })
            .collect(),
        ImportTarget::Glob => vec![],
    }
}

/// Resolve when there are no path segments, only a target.
/// E.g., `use {X, Y}` or `use X`
/// These are typically same-directory or same-module-tree imports.
fn resolve_target_only(
    use_stmt: &UseStmt,
    file_dir: &Path,
    project_root: Option<&Path>,
) -> Option<PathBuf> {
    let target_names = extract_target_names(&use_stmt.target);
    if let Some(name) = target_names.first() {
        // Try current directory first
        if let Some(file) = resolve_file_in_dir(file_dir, name) {
            return Some(file);
        }

        // Walk up the directory tree
        let mut search_dir = file_dir.parent().map(|p| p.to_path_buf());
        while let Some(dir) = search_dir {
            if let Some(file) = resolve_file_in_dir(&dir, name) {
                return Some(file);
            }
            if let Some(root) = project_root {
                if dir == root.join("src") || dir == *root {
                    break;
                }
            }
            search_dir = dir.parent().map(|p| p.to_path_buf());
        }

        // Use cached index for deep search within compiler tree
        if let Some(idx) = get_compiler_index(project_root) {
            let segments = vec![name.clone()];
            if let Some(resolved) = idx.resolve(&segments, &[]) {
                return Some(resolved);
            }
        }
    }
    None
}

/// Resolve relative imports using ".." segments.
fn resolve_relative_import(
    segments: &[String],
    target_names: &[String],
    file_dir: &Path,
) -> Option<PathBuf> {
    let mut current = file_dir.to_path_buf();

    // Count and consume ".." segments
    let mut remaining_start = 0;
    for (i, seg) in segments.iter().enumerate() {
        if seg == ".." {
            current = current.parent()?.to_path_buf();
            remaining_start = i + 1;
        } else if seg.starts_with("..") {
            // Handle "...X" (multiple dots)
            let dots = seg.chars().take_while(|c| *c == '.').count();
            for _ in 0..dots - 1 {
                current = current.parent()?.to_path_buf();
            }
            let rest = &seg[dots..];
            if !rest.is_empty() {
                let remaining = std::iter::once(rest.to_string())
                    .chain(segments[i + 1..].iter().cloned())
                    .collect::<Vec<_>>();
                return resolve_from_segments(&current, &remaining, target_names);
            }
            remaining_start = i + 1;
        } else {
            break;
        }
    }

    resolve_from_segments(&current, &segments[remaining_start..], target_names)
}

/// Resolve imports from a base directory through path segments.
fn resolve_from_segments(
    base: &Path,
    segments: &[String],
    target_names: &[String],
) -> Option<PathBuf> {
    resolve_from_segments_inner(base, segments, target_names, 0)
}

/// Inner recursive function for segment resolution with backtracking.
fn resolve_from_segments_inner(
    base: &Path,
    segments: &[String],
    target_names: &[String],
    depth: usize,
) -> Option<PathBuf> {
    if !base.is_dir() {
        return None;
    }

    let mut current = base.to_path_buf();

    for (i, segment) in segments.iter().enumerate() {
        // Collect all candidate directories for this segment
        let candidates = resolve_dir_segment_candidates(&current, segment);

        if candidates.is_empty() {
            // Segment is not a directory - try as a file
            if let Some(file) = resolve_file_in_dir(&current, segment) {
                return Some(file);
            }
            return None;
        }

        // Try each candidate directory, with backtracking
        if candidates.len() == 1 {
            current = candidates[0].clone();
        } else {
            // Multiple candidates - try each one
            for candidate in &candidates {
                if let Some(result) = resolve_from_segments_inner(
                    candidate,
                    &segments[i + 1..],
                    target_names,
                    depth + 1,
                ) {
                    return Some(result);
                }
            }
            return None;
        }
    }

    // All segments resolved as directories
    // Now try resolving target names as files within the current directory
    if target_names.is_empty() {
        // Glob import: try mod.spl or __init__.spl in the directory
        let mod_file = current.join("mod.spl");
        if mod_file.is_file() {
            return Some(mod_file);
        }
        let init_file = current.join("__init__.spl");
        if init_file.is_file() {
            return Some(init_file);
        }
        return None;
    }

    // Try the first target name as a file in the resolved directory
    if let Some(name) = target_names.first() {
        if let Some(file) = resolve_file_in_dir(&current, name) {
            return Some(file);
        }
    }

    // If target names are symbol names (not files), return the directory's
    // mod.spl/__init__.spl as the module containing those symbols
    let mod_file = current.join("mod.spl");
    if mod_file.is_file() {
        return Some(mod_file);
    }
    let init_file = current.join("__init__.spl");
    if init_file.is_file() {
        return Some(init_file);
    }

    None
}

/// Get all candidate directories for a segment, including numbered alternatives.
fn resolve_dir_segment_candidates(parent: &Path, segment: &str) -> Vec<PathBuf> {
    let mut candidates = Vec::new();

    // Try exact match first
    let exact = parent.join(segment);
    if exact.is_dir() {
        candidates.push(exact);
    }

    // Try numbered prefix matches
    let mapping = build_numbered_dir_mapping(parent);
    if let Some(actual_names) = mapping.get(segment) {
        for actual_name in actual_names {
            let numbered = parent.join(actual_name);
            if numbered.is_dir() && !candidates.contains(&numbered) {
                candidates.push(numbered);
            }
        }
    }

    candidates
}

/// Resolve `std.X.Y` imports by searching through `src/lib/` subdirectories.
/// The lib directory has multiple subdirectories (common/, nogc_sync_mut/, etc.)
/// that contain modules.
fn resolve_std_import(
    lib_dir: &Path,
    segments: &[String],
    target_names: &[String],
) -> Option<PathBuf> {
    if !lib_dir.is_dir() {
        return None;
    }

    // First try direct resolution from lib_dir
    if let Some(resolved) = resolve_from_segments(lib_dir, segments, target_names) {
        return Some(resolved);
    }

    // Search through lib subdirectories
    if let Ok(entries) = fs::read_dir(lib_dir) {
        for entry in entries.flatten() {
            if entry.file_type().map_or(false, |ft| ft.is_dir()) {
                let subdir = entry.path();
                if let Some(resolved) = resolve_from_segments(&subdir, segments, target_names) {
                    return Some(resolved);
                }
            }
        }
    }

    None
}

/// Original simple resolution: try to resolve as sibling file.
fn resolve_use_to_path_simple(use_stmt: &UseStmt, base: &Path) -> Option<PathBuf> {
    let mut parts: Vec<String> = use_stmt
        .path
        .segments
        .iter()
        .filter(|s| s.as_str() != "crate")
        .cloned()
        .collect();

    let target_name = match &use_stmt.target {
        ImportTarget::Single(name) => Some(name.clone()),
        ImportTarget::Aliased { name, .. } => Some(name.clone()),
        _ => None,
    }?;

    parts.push(target_name);
    let mut resolved = base.to_path_buf();
    for part in parts {
        resolved = resolved.join(part);
    }
    resolved.set_extension("spl");
    if resolved.exists() {
        Some(resolved)
    } else {
        None
    }
}

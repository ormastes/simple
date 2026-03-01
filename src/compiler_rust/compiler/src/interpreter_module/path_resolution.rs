//! Module path resolution for the Simple interpreter.
//!
//! This module handles resolving module paths from import statements to actual file paths.
//! It supports:
//! - Relative imports (sibling files)
//! - Project-root-relative imports
//! - Standard library imports
//! - __init__.spl directory modules
//! - Numbered directory matching (e.g., 10.frontend → "frontend")

use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

use tracing::trace;

use crate::error::CompileError;

/// Find a numbered directory matching the pattern `NN.name` or `NNN.name`.
///
/// The Simple compiler organizes source into numbered layers like:
///   src/compiler/00.common/
///   src/compiler/10.frontend/
///   src/compiler/70.backend/
///
/// When resolving `compiler.frontend`, this function finds `10.frontend` for segment `frontend`.
fn find_numbered_dir(parent: &Path, segment: &str) -> Option<PathBuf> {
    let entries = std::fs::read_dir(parent).ok()?;
    for entry in entries.flatten() {
        let name = entry.file_name();
        let name_str = name.to_string_lossy();
        // Match pattern: 1-3 digits, dot, then the segment name
        if let Some(after_dot) = name_str.find('.') {
            let prefix = &name_str[..after_dot];
            let suffix = &name_str[after_dot + 1..];
            if suffix == segment
                && prefix.len() <= 3
                && prefix.chars().all(|c| c.is_ascii_digit())
            {
                let path = parent.join(&*name_str);
                if path.is_dir() {
                    return Some(path);
                }
            }
        }
    }
    None
}

/// Find a segment as a subdirectory inside any numbered directory.
///
/// For `compiler.core.parser`, when "core" is not found as `NN.core`,
/// this searches inside each numbered dir (like `10.frontend/`) for
/// a subdirectory named "core". Returns all matches sorted by numbered prefix.
fn find_segment_in_numbered_dirs(parent: &Path, segment: &str) -> Vec<PathBuf> {
    let mut results = Vec::new();
    if let Ok(entries) = std::fs::read_dir(parent) {
        for entry in entries.flatten() {
            let name = entry.file_name();
            let name_str = name.to_string_lossy();
            // Check if this is a numbered directory (NN.name pattern)
            if let Some(after_dot) = name_str.find('.') {
                let prefix = &name_str[..after_dot];
                if prefix.len() <= 3 && prefix.chars().all(|c| c.is_ascii_digit()) {
                    let numbered_path = parent.join(&*name_str);
                    if numbered_path.is_dir() {
                        let sub = numbered_path.join(segment);
                        if sub.is_dir() {
                            results.push(sub);
                        }
                    }
                }
            }
        }
    }
    results.sort();
    results
}

/// Try to resolve the last segment from a given directory.
/// Checks .spl file, .ssh file, __init__.spl, and numbered directory variants.
fn try_resolve_last_segment(current: &Path, last: &str) -> Option<PathBuf> {
    // Try .spl file
    let file_path = current.join(format!("{}.spl", last));
    if file_path.exists() && file_path.is_file() {
        return Some(file_path);
    }

    // Try .ssh file
    let ssh_path = current.join(format!("{}.ssh", last));
    if ssh_path.exists() && ssh_path.is_file() {
        return Some(ssh_path);
    }

    // Try directory with __init__.spl
    let dir_path = current.join(last);
    let init_path = dir_path.join("__init__.spl");
    if init_path.exists() && init_path.is_file() {
        return Some(init_path);
    }

    // Try numbered directory for the last segment
    if let Some(numbered_dir) = find_numbered_dir(current, last) {
        let numbered_init = numbered_dir.join("__init__.spl");
        if numbered_init.exists() && numbered_init.is_file() {
            return Some(numbered_init);
        }
        let numbered_file = numbered_dir.join(format!("{}.spl", last));
        if numbered_file.exists() && numbered_file.is_file() {
            return Some(numbered_file);
        }
    }

    None
}

/// Resolve a path through segments, supporting numbered directories at each level.
///
/// For each intermediate segment, tries direct match first, then numbered directory fallback.
/// When a direct match exists but doesn't lead to a final resolution, backtracks and tries
/// the numbered directory alternative. This handles cases like `compiler.core.X` where
/// `src/compiler/core/` exists but doesn't contain X, while `src/compiler/10.frontend/core/`
/// does contain X.
fn resolve_with_numbered_dirs(base: &Path, parts: &[String]) -> Option<PathBuf> {
    if parts.is_empty() {
        return None;
    }

    // Numbered directory resolution is disabled for now.
    // Loading compiler source via numbered dirs (e.g., 10.frontend → frontend)
    // causes the interpreter to load the entire compiler tree (~600K lines),
    // consuming 4+ GB RAM per test and OOMing the test runner.
    // TODO: Re-enable with a module loading depth/size limit.
    let _ = base;
    None
}

fn resolve_with_numbered_dirs_recursive(
    current: &Path,
    parts: &[String],
    depth: usize,
) -> Option<PathBuf> {
    if depth >= parts.len() {
        return None;
    }

    let segment = &parts[depth];

    // Base case: last segment
    if depth == parts.len() - 1 {
        return try_resolve_last_segment(current, segment);
    }

    // Recursive case: intermediate segment
    // Strategy 1: Try direct path first
    let direct = current.join(segment);
    if direct.exists() && direct.is_dir() {
        if let Some(found) = resolve_with_numbered_dirs_recursive(&direct, parts, depth + 1) {
            return Some(found);
        }
    }

    // Strategy 2: Try numbered directory matching segment (e.g., 10.frontend for "frontend")
    if let Some(numbered) = find_numbered_dir(current, segment) {
        if let Some(found) = resolve_with_numbered_dirs_recursive(&numbered, parts, depth + 1) {
            return Some(found);
        }
    }

    // Strategy 3: Try segment as subdirectory inside numbered directories.
    // For `compiler.core.parser`, "core" is inside `10.frontend/core/`, not `NN.core/`.
    for sub_dir in find_segment_in_numbered_dirs(current, segment) {
        if let Some(found) = resolve_with_numbered_dirs_recursive(&sub_dir, parts, depth + 1) {
            return Some(found);
        }
    }

    None
}

// Thread-local cache for resolved module paths to avoid repeated filesystem probing
thread_local! {
    static PATH_RESOLUTION_CACHE: RefCell<HashMap<(Vec<String>, PathBuf), Option<PathBuf>>> = RefCell::new(HashMap::new());
}

/// Clear the path resolution cache (called between test runs)
pub fn clear_path_resolution_cache() {
    PATH_RESOLUTION_CACHE.with(|cache| cache.borrow_mut().clear());
}

/// Resolve module path from segments
///
/// Attempts to resolve a module path by trying multiple strategies in order:
/// 1. Relative to base directory (sibling files)
/// 2. __init__.spl in directory (package modules)
/// 3. Parent directories (project-root-relative imports)
/// 4. Standard library locations
///
/// # Arguments
/// * `parts` - Module path segments (e.g., ["std", "spec"])
/// * `base_dir` - Base directory to resolve from (usually parent of current file)
///
/// # Returns
/// Absolute path to the module file, or an error if not found
pub fn resolve_module_path(parts: &[String], base_dir: &Path) -> Result<PathBuf, CompileError> {
    // Check cache first
    let cache_key = (parts.to_vec(), base_dir.to_path_buf());
    let cached = PATH_RESOLUTION_CACHE.with(|cache| cache.borrow().get(&cache_key).cloned());
    if let Some(cached_result) = cached {
        return cached_result.ok_or_else(|| crate::error::factory::cannot_resolve_module(&parts.join(".")));
    }

    let result = resolve_module_path_uncached(parts, base_dir);

    // Cache the result
    let cache_value = result.as_ref().ok().cloned();
    PATH_RESOLUTION_CACHE.with(|cache| {
        cache.borrow_mut().insert(cache_key, cache_value);
    });

    result
}

fn resolve_module_path_uncached(parts: &[String], base_dir: &Path) -> Result<PathBuf, CompileError> {
    // Try resolving from base directory first (sibling files)
    let mut resolved = base_dir.to_path_buf();
    for part in parts {
        resolved = resolved.join(part);
    }
    resolved.set_extension("spl");
    if resolved.exists() && resolved.is_file() {
        return Ok(resolved);
    }

    // Try .ssh extension (Simple shell scripts)
    resolved.set_extension("ssh");
    if resolved.exists() && resolved.is_file() {
        return Ok(resolved);
    }

    // Try __init__.spl in directory
    let mut init_resolved = base_dir.to_path_buf();
    for part in parts {
        init_resolved = init_resolved.join(part);
    }
    init_resolved = init_resolved.join("__init__");
    init_resolved.set_extension("spl");
    if init_resolved.exists() && init_resolved.is_file() {
        return Ok(init_resolved);
    }

    // Try with numbered directory support from base directory
    if let Some(found) = resolve_with_numbered_dirs(base_dir, parts) {
        return Ok(found);
    }

    // Try resolving from parent directories (for project-root-relative imports)
    // This handles cases like importing "verification.lean.codegen" from within
    // "verification/regenerate/" - we need to go up to find the "verification/" root
    let mut parent_dir = base_dir.to_path_buf();
    for _ in 0..10 {
        if let Some(parent) = parent_dir.parent() {
            parent_dir = parent.to_path_buf();

            // Try module.spl
            let mut parent_resolved = parent_dir.clone();
            for part in parts {
                parent_resolved = parent_resolved.join(part);
            }
            parent_resolved.set_extension("spl");
            if parent_resolved.exists() && parent_resolved.is_file() {
                trace!(path = ?parent_resolved, "Found module in parent directory");
                return Ok(parent_resolved);
            }

            // Try __init__.spl
            let mut parent_init_resolved = parent_dir.clone();
            for part in parts {
                parent_init_resolved = parent_init_resolved.join(part);
            }
            parent_init_resolved = parent_init_resolved.join("__init__");
            parent_init_resolved.set_extension("spl");
            if parent_init_resolved.exists() && parent_init_resolved.is_file() {
                trace!(path = ?parent_init_resolved, "Found module __init__.spl in parent directory");
                return Ok(parent_init_resolved);
            }

            // Try with numbered directory support from parent
            if let Some(found) = resolve_with_numbered_dirs(&parent_dir, parts) {
                trace!(path = ?found, "Found module via numbered directory in parent");
                return Ok(found);
            }
        } else {
            break;
        }
    }

    // Try stdlib location - walk up directory tree
    let mut current = base_dir.to_path_buf();
    for _ in 0..10 {
        // Try various stdlib locations
        for stdlib_subpath in &[
            // Preferred: repo layout uses src/std/* (symlink to src/lib)
            "src/std",
            // Also try src/lib directly
            "src/lib",
            // Legacy layouts kept for compatibility
            "src/std/src",
            "src/lib/std/src",
            "lib/std/src",
            "rust/lib/std/src",
            "simple/std_lib/src",
            "std_lib/src",
        ] {
            let stdlib_candidate = current.join(stdlib_subpath);
            if stdlib_candidate.exists() {
                // When importing from stdlib, "std" / "lib" / "std_lib" represent the stdlib root itself,
                // not a subdirectory. Strip the prefix if present.
                let stdlib_parts: Vec<String> = if !parts.is_empty() && parts[0] == "std" {
                    parts[1..].to_vec()
                } else if !parts.is_empty() && parts[0] == "lib" {
                    parts[1..].to_vec()
                } else if !parts.is_empty() && parts[0] == "std_lib" {
                    parts[1..].to_vec()
                } else {
                    parts.to_vec()
                };

                // Try resolving from stdlib (only if we have parts after stripping "std")
                if !stdlib_parts.is_empty() {
                    let mut stdlib_path = stdlib_candidate.clone();
                    for part in &stdlib_parts {
                        stdlib_path = stdlib_path.join(part);
                    }
                    stdlib_path.set_extension("spl");
                    if stdlib_path.exists() && stdlib_path.is_file() {
                        return Ok(stdlib_path);
                    }

                    // Also try __init__.spl in stdlib
                    let mut stdlib_init_path = stdlib_candidate.clone();
                    for part in &stdlib_parts {
                        stdlib_init_path = stdlib_init_path.join(part);
                    }
                    stdlib_init_path = stdlib_init_path.join("__init__");
                    stdlib_init_path.set_extension("spl");
                    if stdlib_init_path.exists() && stdlib_init_path.is_file() {
                        return Ok(stdlib_init_path);
                    }

                    // Search lib subdirectories (mirrors module_loader.spl strategy)
                    // For `use std.format.{...}`, the file might be at lib/common/format.spl
                    // Search order: nogc_async_mut > nogc_sync_mut > common > gc_async_mut > nogc_async_mut_noalloc
                    for subdir in &["nogc_async_mut", "nogc_sync_mut", "common", "gc_async_mut", "nogc_async_mut_noalloc"] {
                        let mut sub_path = stdlib_candidate.join(subdir);
                        for part in &stdlib_parts {
                            sub_path = sub_path.join(part);
                        }
                        sub_path.set_extension("spl");
                        if sub_path.exists() && sub_path.is_file() {
                            return Ok(sub_path);
                        }
                        // Also try __init__.spl in subdirectory
                        let mut sub_init = stdlib_candidate.join(subdir);
                        for part in &stdlib_parts {
                            sub_init = sub_init.join(part);
                        }
                        sub_init = sub_init.join("__init__");
                        sub_init.set_extension("spl");
                        if sub_init.exists() && sub_init.is_file() {
                            return Ok(sub_init);
                        }
                    }

                    // Try with numbered directory support in stdlib
                    if let Some(found) = resolve_with_numbered_dirs(&stdlib_candidate, &stdlib_parts) {
                        return Ok(found);
                    }
                }
            } // End of if stdlib_candidate.exists()
        } // End of for stdlib_subpath

        // Try src/ directory (for app modules like app.lsp.server)
        let src_candidate = current.join("src");
        if src_candidate.exists() {
            // Try module.spl in src/
            let mut src_path = src_candidate.clone();
            for part in parts {
                src_path = src_path.join(part);
            }
            src_path.set_extension("spl");
            if src_path.exists() && src_path.is_file() {
                return Ok(src_path);
            }

            // Try __init__.spl in src/
            let mut src_init_path = src_candidate.clone();
            for part in parts {
                src_init_path = src_init_path.join(part);
            }
            src_init_path = src_init_path.join("__init__");
            src_init_path.set_extension("spl");
            if src_init_path.exists() && src_init_path.is_file() {
                return Ok(src_init_path);
            }

            // Try with numbered directory support in src/
            if let Some(found) = resolve_with_numbered_dirs(&src_candidate, parts) {
                return Ok(found);
            }

            // Strategy: "compiler.*" → src/compiler/ with numbered prefix support
            // This mirrors the compiler's Strategy 2 for resolving compiler internal modules
            if parts.len() > 1 && parts[0] == "compiler" {
                let compiler_dir = src_candidate.join("compiler");
                if compiler_dir.is_dir() {
                    if let Some(found) = resolve_with_numbered_dirs(&compiler_dir, &parts[1..]) {
                        return Ok(found);
                    }
                }
            }

            // Strategy: "app.*" → src/compiler/ with numbered prefix support
            // The self-hosted compiler maps app.build.X to src/app/build/X.smf (compiled),
            // but the .spl source lives at src/compiler/80.driver/build/X.spl.
            // This allows the Rust driver to resolve app.* imports to source files.
            if parts.len() > 1 && parts[0] == "app" {
                let compiler_dir = src_candidate.join("compiler");
                if compiler_dir.is_dir() {
                    if let Some(found) = resolve_with_numbered_dirs(&compiler_dir, &parts[1..]) {
                        return Ok(found);
                    }
                }
            }
        }

        if let Some(parent) = current.parent() {
            current = parent.to_path_buf();
        } else {
            break;
        }
    }

    Err(crate::error::factory::cannot_resolve_module(&parts.join(".")))
}

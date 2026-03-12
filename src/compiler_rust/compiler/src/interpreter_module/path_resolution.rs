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
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use tracing::trace;

use crate::error::CompileError;

// Profiling counters (active when SIMPLE_PROFILE env var is set)
static RESOLVE_CALLS: AtomicU64 = AtomicU64::new(0);
static CACHE_HITS: AtomicU64 = AtomicU64::new(0);
static DIR_LIST_CALLS: AtomicU64 = AtomicU64::new(0);

/// Print resolution statistics if SIMPLE_PROFILE env var is set.
pub fn print_resolve_stats() {
    if std::env::var("SIMPLE_PROFILE").is_ok() {
        let calls = RESOLVE_CALLS.load(Ordering::Relaxed);
        let hits = CACHE_HITS.load(Ordering::Relaxed);
        let dir_lists = DIR_LIST_CALLS.load(Ordering::Relaxed);
        let hit_rate = if calls > 0 { (hits * 100) / calls } else { 0 };
        eprintln!(
            "[resolve-stats] calls={} cache_hits={} hit_rate={}% dir_list={}",
            calls, hits, hit_rate, dir_lists
        );
    }
}

/// Reset profiling counters.
pub fn reset_resolve_stats() {
    RESOLVE_CALLS.store(0, Ordering::Relaxed);
    CACHE_HITS.store(0, Ordering::Relaxed);
    DIR_LIST_CALLS.store(0, Ordering::Relaxed);
}

/// Compute a u64 cache key from parts + base_dir without allocating.
fn compute_cache_key(parts: &[String], base_dir: &Path) -> u64 {
    let mut hasher = ahash::AHasher::default();
    parts.hash(&mut hasher);
    base_dir.hash(&mut hasher);
    hasher.finish()
}

// Thread-local cache for directory listings to avoid repeated read_dir calls.
thread_local! {
    static DIR_LISTING_CACHE: RefCell<HashMap<PathBuf, Vec<(String, PathBuf)>>> = RefCell::new(HashMap::new());
}

/// Get cached directory listing. Each entry is (name, full_path).
fn cached_read_dir(dir: &Path) -> Vec<(String, PathBuf)> {
    let cached = DIR_LISTING_CACHE.with(|cache| cache.borrow().get(dir).cloned());
    if let Some(entries) = cached {
        return entries;
    }

    DIR_LIST_CALLS.fetch_add(1, Ordering::Relaxed);
    let mut entries = Vec::new();
    if let Ok(read_dir) = std::fs::read_dir(dir) {
        for entry in read_dir.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            let path = entry.path();
            entries.push((name, path));
        }
    }

    DIR_LISTING_CACHE.with(|cache| {
        cache.borrow_mut().insert(dir.to_path_buf(), entries.clone());
    });
    entries
}

/// Find a numbered directory matching the pattern `NN.name` or `NNN.name`.
///
/// The Simple compiler organizes source into numbered layers like:
///   src/compiler/00.common/
///   src/compiler/10.frontend/
///   src/compiler/70.backend/
///
/// When resolving `compiler.frontend`, this function finds `10.frontend` for segment `frontend`.
fn find_numbered_dir(parent: &Path, segment: &str) -> Option<PathBuf> {
    for (name_str, path) in cached_read_dir(parent) {
        // Match pattern: 1-3 digits, dot, then the segment name
        if let Some(after_dot) = name_str.find('.') {
            let prefix = &name_str[..after_dot];
            let suffix = &name_str[after_dot + 1..];
            if suffix == segment && prefix.len() <= 3 && prefix.chars().all(|c| c.is_ascii_digit()) && path.is_dir() {
                return Some(path);
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
    for (name_str, numbered_path) in cached_read_dir(parent) {
        // Check if this is a numbered directory (NN.name pattern)
        if let Some(after_dot) = name_str.find('.') {
            let prefix = &name_str[..after_dot];
            if prefix.len() <= 3 && prefix.chars().all(|c| c.is_ascii_digit()) && numbered_path.is_dir() {
                let sub = numbered_path.join(segment);
                if sub.is_dir() {
                    results.push(sub);
                }
            }
        }
    }
    results.sort();
    results
}

/// Try to resolve the last segment from a given directory.
/// Checks .spl file, .shs file, __init__.spl, and numbered directory variants.
fn try_resolve_last_segment(current: &Path, last: &str) -> Option<PathBuf> {
    // Try .spl file
    let file_path = current.join(format!("{}.spl", last));
    if file_path.exists() && file_path.is_file() {
        return Some(file_path);
    }

    // Try .shs file
    let shs_path = current.join(format!("{}.shs", last));
    if shs_path.exists() && shs_path.is_file() {
        return Some(shs_path);
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

    // Depth limit: avoid deep recursion that could trigger compiler tree loading.
    // Most legitimate imports have <= 5 segments.
    if parts.len() > 5 {
        return None;
    }

    // Only attempt numbered dir resolution if base is within a project source tree.
    // Scanning arbitrary dirs like /tmp or / for numbered subdirs wastes ~90 syscalls.
    let base_str = base.to_string_lossy();
    let in_src = base_str.contains("/src/") || base_str.ends_with("/src")
        || base_str.starts_with("src/") || base_str == "src";
    if !in_src {
        return None;
    }

    let result = resolve_with_numbered_dirs_recursive(base, parts, 0);

    // Blocklist: prevent test files (outside src/compiler) from accidentally loading
    // the entire compiler tree (~600K lines) via package __init__.spl imports.
    // Individual module file imports (e.g., ast.spl, wide_public.spl) are allowed
    // since they're small and won't cause OOM.
    if let Some(ref resolved) = result {
        if is_blocked_compiler_resolution(base, resolved) {
            return None;
        }
    }

    result
}

/// Check if a resolved path would pull in the compiler tree from an external caller.
/// Only blocks package-level imports (__init__.spl) which could trigger loading entire
/// subtrees. Individual module file imports are allowed.
fn is_blocked_compiler_resolution(base: &Path, resolved: &Path) -> bool {
    let base_str = base.to_string_lossy();
    let resolved_str = resolved.to_string_lossy();
    // Only block if: caller is NOT in src/compiler, resolved IS in src/compiler,
    // AND the resolved path is a package __init__.spl (which loads entire subtrees).
    // Individual .spl files are safe to load.
    if !base_str.contains("src/compiler") && resolved_str.contains("src/compiler") {
        return resolved_str.ends_with("__init__.spl");
    }
    false
}

fn resolve_with_numbered_dirs_recursive(current: &Path, parts: &[String], depth: usize) -> Option<PathBuf> {
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

// Thread-local cache for resolved module paths to avoid repeated filesystem probing.
// Keyed by u64 hash of (parts, base_dir) to avoid cloning Vec<String> + PathBuf on every lookup.
thread_local! {
    static PATH_RESOLUTION_CACHE: RefCell<HashMap<u64, Option<PathBuf>>> = RefCell::new(HashMap::new());
    // Cached project root to avoid re-discovering it per import.
    static PROJECT_ROOT_CACHE: RefCell<HashMap<PathBuf, Option<PathBuf>>> = RefCell::new(HashMap::new());
}

/// Find the project root by walking up from `start` looking for `src/` or `Cargo.toml`.
fn find_project_root(start: &Path) -> Option<PathBuf> {
    // Check thread-local cache first
    let cached = PROJECT_ROOT_CACHE.with(|cache| cache.borrow().get(start).cloned());
    if let Some(result) = cached {
        return result;
    }

    let mut dir = start.to_path_buf();
    let result = loop {
        if dir.join("src").is_dir() || dir.join("Cargo.toml").is_file() {
            break Some(dir.clone());
        }
        if !dir.pop() {
            break None;
        }
    };

    PROJECT_ROOT_CACHE.with(|cache| {
        cache.borrow_mut().insert(start.to_path_buf(), result.clone());
    });
    result
}

/// Check if parts represent a stdlib-prefixed import.
fn is_stdlib_import(parts: &[String]) -> bool {
    !parts.is_empty() && matches!(parts[0].as_str(), "std" | "lib" | "std_lib")
}

/// Clear the path resolution cache (called between test runs)
pub fn clear_path_resolution_cache() {
    PATH_RESOLUTION_CACHE.with(|cache| cache.borrow_mut().clear());
    PROJECT_ROOT_CACHE.with(|cache| cache.borrow_mut().clear());
    DIR_LISTING_CACHE.with(|cache| cache.borrow_mut().clear());
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
    RESOLVE_CALLS.fetch_add(1, Ordering::Relaxed);

    // Check cache first — O(1) hash lookup, no allocation
    let cache_key = compute_cache_key(parts, base_dir);
    let cached = PATH_RESOLUTION_CACHE.with(|cache| cache.borrow().get(&cache_key).cloned());
    if let Some(cached_result) = cached {
        CACHE_HITS.fetch_add(1, Ordering::Relaxed);
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
    // Pre-compute the relative path segments once — reused across all strategies
    let relative: PathBuf = parts.iter().collect();

    // Try resolving from base directory first (sibling files)
    let mut resolved = base_dir.join(&relative);
    resolved.set_extension("spl");
    if resolved.exists() && resolved.is_file() {
        return Ok(resolved);
    }

    // Try .shs extension (Simple shell scripts)
    resolved.set_extension("shs");
    if resolved.exists() && resolved.is_file() {
        return Ok(resolved);
    }

    // Try __init__.spl in directory
    let mut init_resolved = base_dir.join(&relative);
    init_resolved.push("__init__.spl");
    if init_resolved.exists() && init_resolved.is_file() {
        return Ok(init_resolved);
    }

    // Try with numbered directory support from base directory
    if let Some(found) = resolve_with_numbered_dirs(base_dir, parts) {
        return Ok(found);
    }

    // Determine project root once for early break in parent traversal
    let project_root = find_project_root(base_dir);

    // Try resolving from parent directories (for project-root-relative imports)
    let mut parent_dir = base_dir.to_path_buf();
    for _ in 0..10 {
        if let Some(parent) = parent_dir.parent() {
            parent_dir = parent.to_path_buf();

            // Try module.spl
            let mut parent_resolved = parent_dir.join(&relative);
            parent_resolved.set_extension("spl");
            if parent_resolved.exists() && parent_resolved.is_file() {
                trace!(path = ?parent_resolved, "Found module in parent directory");
                return Ok(parent_resolved);
            }

            // Try __init__.spl
            let mut parent_init_resolved = parent_dir.join(&relative);
            parent_init_resolved.push("__init__.spl");
            if parent_init_resolved.exists() && parent_init_resolved.is_file() {
                trace!(path = ?parent_init_resolved, "Found module __init__.spl in parent directory");
                return Ok(parent_init_resolved);
            }

            // Try with numbered directory support from parent
            if let Some(found) = resolve_with_numbered_dirs(&parent_dir, parts) {
                trace!(path = ?found, "Found module via numbered directory in parent");
                return Ok(found);
            }

            // Early break: stop at project root or filesystem root
            if let Some(ref root) = project_root {
                if parent_dir == *root || parent_dir.parent().is_none() {
                    break;
                }
            }
        } else {
            break;
        }
    }

    // Stdlib search: try canonical paths first, then legacy.
    // Skip stdlib search entirely for non-stdlib imports (parts[0] != std/lib/std_lib).
    let is_stdlib = is_stdlib_import(parts);

    // Strip stdlib prefix once if applicable
    let stdlib_parts: &[String] = if is_stdlib { &parts[1..] } else { parts };

    // Walk up from project root (or base_dir) to find stdlib/src locations
    let search_start = project_root.as_deref().unwrap_or(base_dir);
    let mut current = search_start.to_path_buf();
    for _ in 0..10 {
        // Only search stdlib paths if this looks like a stdlib import
        if is_stdlib && !stdlib_parts.is_empty() {
            // Canonical paths first (most likely to hit), then legacy
            for stdlib_subpath in &[
                "src/std",
                "src/lib",
                "src/std/src",
                "src/lib/std/src",
                "lib/std/src",
                "rust/lib/std/src",
                "simple/std_lib/src",
                "std_lib/src",
            ] {
                let stdlib_candidate = current.join(stdlib_subpath);
                if !stdlib_candidate.exists() {
                    continue;
                }

                let stdlib_relative: PathBuf = stdlib_parts.iter().collect();

                // Try module.spl
                let mut stdlib_path = stdlib_candidate.join(&stdlib_relative);
                stdlib_path.set_extension("spl");
                if stdlib_path.exists() && stdlib_path.is_file() {
                    return Ok(stdlib_path);
                }

                // Try __init__.spl in stdlib
                let mut stdlib_init_path = stdlib_candidate.join(&stdlib_relative);
                stdlib_init_path.push("__init__.spl");
                if stdlib_init_path.exists() && stdlib_init_path.is_file() {
                    return Ok(stdlib_init_path);
                }

                // Search lib subdirectories (mirrors module_loader.spl strategy)
                for subdir in &[
                    "nogc_async_mut",
                    "nogc_sync_mut",
                    "nogc_async_immut",
                    "common",
                    "gc_async_mut",
                    "nogc_async_mut_noalloc",
                ] {
                    let mut sub_path = stdlib_candidate.join(subdir).join(&stdlib_relative);
                    sub_path.set_extension("spl");
                    if sub_path.exists() && sub_path.is_file() {
                        return Ok(sub_path);
                    }
                    // Also try __init__.spl in subdirectory
                    let mut sub_init = stdlib_candidate.join(subdir).join(&stdlib_relative);
                    sub_init.push("__init__.spl");
                    if sub_init.exists() && sub_init.is_file() {
                        return Ok(sub_init);
                    }
                }

                // Try with numbered directory support in stdlib
                if let Some(found) = resolve_with_numbered_dirs(&stdlib_candidate, stdlib_parts) {
                    return Ok(found);
                }
            }
        }

        // Try src/ directory (for app modules like app.lsp.server)
        let src_candidate = current.join("src");
        if src_candidate.exists() {
            // Try module.spl in src/
            let mut src_path = src_candidate.join(&relative);
            src_path.set_extension("spl");
            if src_path.exists() && src_path.is_file() {
                return Ok(src_path);
            }

            // Try __init__.spl in src/
            let mut src_init_path = src_candidate.join(&relative);
            src_init_path.push("__init__.spl");
            if src_init_path.exists() && src_init_path.is_file() {
                return Ok(src_init_path);
            }

            // Try with numbered directory support in src/
            if let Some(found) = resolve_with_numbered_dirs(&src_candidate, parts) {
                return Ok(found);
            }

            // Strategy: "compiler.*" → src/compiler/ with numbered prefix support
            if parts.len() > 1 && parts[0] == "compiler" {
                let compiler_dir = src_candidate.join("compiler");
                if compiler_dir.is_dir() {
                    if let Some(found) = resolve_with_numbered_dirs(&compiler_dir, &parts[1..]) {
                        return Ok(found);
                    }
                }
            }

            // Strategy: "app.*" → src/compiler/ with numbered prefix support
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

    // Final fallback for non-stdlib imports: search lib subdirectories
    // This handles imports like `use sdn.parser.{parse}` where the module lives
    // under src/lib/common/sdn/parser.spl but doesn't have a `std.` prefix.
    if !is_stdlib {
        let search_start = project_root.as_deref().unwrap_or(base_dir);
        let mut current = search_start.to_path_buf();
        for _ in 0..10 {
            for stdlib_subpath in &["src/lib", "src/std"] {
                let stdlib_candidate = current.join(stdlib_subpath);
                if !stdlib_candidate.exists() {
                    continue;
                }

                // Search lib subdirectories for the original parts
                for subdir in &[
                    "common",
                    "nogc_sync_mut",
                    "nogc_async_mut",
                    "nogc_async_immut",
                    "gc_async_mut",
                    "nogc_async_mut_noalloc",
                ] {
                    let non_std_relative: PathBuf = parts.iter().collect();
                    let mut sub_path = stdlib_candidate.join(subdir).join(&non_std_relative);
                    sub_path.set_extension("spl");
                    if sub_path.exists() && sub_path.is_file() {
                        trace!(path = ?sub_path, "Found non-stdlib import in lib subdirectory");
                        return Ok(sub_path);
                    }
                    // Also try __init__.spl in subdirectory
                    let mut sub_init = stdlib_candidate.join(subdir).join(&non_std_relative);
                    sub_init.push("__init__.spl");
                    if sub_init.exists() && sub_init.is_file() {
                        trace!(path = ?sub_init, "Found non-stdlib import __init__.spl in lib subdirectory");
                        return Ok(sub_init);
                    }
                }
            }

            if let Some(parent) = current.parent() {
                current = parent.to_path_buf();
            } else {
                break;
            }
        }
    }

    Err(crate::error::factory::cannot_resolve_module(&parts.join(".")))
}

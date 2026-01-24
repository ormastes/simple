//! Module path resolution for the Simple interpreter.
//!
//! This module handles resolving module paths from import statements to actual file paths.
//! It supports:
//! - Relative imports (sibling files)
//! - Project-root-relative imports
//! - Standard library imports
//! - __init__.spl directory modules

use std::path::{Path, PathBuf};

use tracing::trace;

use crate::error::CompileError;

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
    // Try resolving from base directory first (sibling files)
    let mut resolved = base_dir.to_path_buf();
    for part in parts {
        resolved = resolved.join(part);
    }
    resolved.set_extension("spl");
    if resolved.exists() {
        return Ok(resolved);
    }

    // Try __init__.spl in directory
    let mut init_resolved = base_dir.to_path_buf();
    for part in parts {
        init_resolved = init_resolved.join(part);
    }
    init_resolved = init_resolved.join("__init__");
    init_resolved.set_extension("spl");
    if init_resolved.exists() {
        return Ok(init_resolved);
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
            if parent_resolved.exists() {
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
            if parent_init_resolved.exists() {
                trace!(path = ?parent_init_resolved, "Found module __init__.spl in parent directory");
                return Ok(parent_init_resolved);
            }
        } else {
            break;
        }
    }

    // Try stdlib location - walk up directory tree
    let mut current = base_dir.to_path_buf();
    for _ in 0..10 {
        // Try various stdlib locations
        for stdlib_subpath in &["src/lib/std/src", "lib/std/src", "simple/std_lib/src", "std_lib/src"] {
            let stdlib_candidate = current.join(stdlib_subpath);
            if stdlib_candidate.exists() {
                // When importing from stdlib, "std" represents the stdlib root itself, not a subdirectory.
                // So "import std.spec" should resolve to "lib/std/src/spec/__init__.spl", not "lib/std/src/std/spec/__init__.spl".
                // Strip the "std" prefix if present.
                let stdlib_parts: Vec<String> = if parts.len() > 0 && parts[0] == "std" {
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
                    if stdlib_path.exists() {
                        return Ok(stdlib_path);
                    }

                    // Also try __init__.spl in stdlib
                    let mut stdlib_init_path = stdlib_candidate.clone();
                    for part in &stdlib_parts {
                        stdlib_init_path = stdlib_init_path.join(part);
                    }
                    stdlib_init_path = stdlib_init_path.join("__init__");
                    stdlib_init_path.set_extension("spl");
                    if stdlib_init_path.exists() {
                        return Ok(stdlib_init_path);
                    }
                }
            } // End of if stdlib_candidate.exists()
        } // End of for stdlib_subpath
        if let Some(parent) = current.parent() {
            current = parent.to_path_buf();
        } else {
            break;
        }
    }

    Err(crate::error::factory::cannot_resolve_module(&parts.join(".")))
}

//! Path resolution helpers for the module loader.
//!
//! Converts `use` statement paths into filesystem `.spl` file paths,
//! handling dotted-directory layouts, stdlib search roots, and type imports.

use std::fs;
use std::path::{Path, PathBuf};

use simple_parser::ast::{ImportTarget, UseStmt};

pub(super) fn prefer_package_init_for_member_import(resolved: PathBuf, use_stmt: &UseStmt) -> PathBuf {
    match &use_stmt.target {
        ImportTarget::Group(_) | ImportTarget::Glob => {
            if resolved.extension().is_some_and(|ext| ext == "spl")
                && resolved.file_name().is_none_or(|name| name != "__init__.spl")
            {
                let package_init = resolved.with_extension("").join("__init__.spl");
                if package_init.exists() && package_init.is_file() {
                    return package_init;
                }
            }
            resolved
        }
        _ => resolved,
    }
}

pub(super) fn dotted_dir_from(current: &Path, segment: &str) -> Option<PathBuf> {
    let parent = current.parent()?;
    let current_name = current.file_name()?.to_str()?;
    let dotted_dir = parent.join(format!("{}.{}", current_name, segment));
    if dotted_dir.is_dir() {
        Some(dotted_dir)
    } else {
        None
    }
}

pub(super) fn domain_to_dir(domain: &str) -> String {
    domain.replace('-', "_")
}

pub(super) fn normalize_type_parts(parts: &[String]) -> Option<Vec<String>> {
    if parts.is_empty() {
        return None;
    }

    if parts.len() >= 2 && parts[0].contains('-') {
        let mut normalized = vec!["type".to_string(), domain_to_dir(&parts[0])];
        normalized.extend(parts[1..].iter().cloned());
        return Some(normalized);
    }

    if parts.len() == 1 {
        return Some(vec!["type".to_string(), "simple_lang".to_string(), parts[0].clone()]);
    }

    None
}

pub(super) fn resolve_parts_from_root(root: &Path, parts: &[String], use_stmt: &UseStmt) -> Option<PathBuf> {
    let mut resolved = root.to_path_buf();
    for part in parts {
        resolved = resolved.join(part);
    }
    resolved.set_extension("spl");
    if resolved.exists() && resolved.is_file() {
        return Some(prefer_package_init_for_member_import(resolved, use_stmt));
    }

    if parts.is_empty() {
        return None;
    }

    let mut dotted_resolved = root.to_path_buf();
    for part in &parts[..parts.len().saturating_sub(1)] {
        let direct = dotted_resolved.join(part);
        if direct.exists() && direct.is_dir() {
            dotted_resolved = direct;
        } else if let Some(dotted_dir) = dotted_dir_from(&dotted_resolved, part) {
            dotted_resolved = dotted_dir;
        } else {
            dotted_resolved = PathBuf::new();
            break;
        }
    }
    if dotted_resolved.as_os_str().is_empty() {
        return None;
    }

    let last = &parts[parts.len() - 1];
    let dotted_file = dotted_resolved.join(format!("{}.spl", last));
    if dotted_file.exists() && dotted_file.is_file() {
        return Some(prefer_package_init_for_member_import(dotted_file, use_stmt));
    }

    let dotted_init = dotted_resolved.join(last).join("__init__.spl");
    if dotted_init.exists() && dotted_init.is_file() {
        return Some(dotted_init);
    }

    if let Some(dotted_dir) = dotted_dir_from(&dotted_resolved, last) {
        let dotted_dir_init = dotted_dir.join("__init__.spl");
        if dotted_dir_init.exists() && dotted_dir_init.is_file() {
            return Some(dotted_dir_init);
        }
        let nested_file = dotted_dir.join(format!("{}.spl", last));
        if nested_file.exists() && nested_file.is_file() {
            return Some(prefer_package_init_for_member_import(nested_file, use_stmt));
        }
    }

    None
}

pub(super) fn resolve_parts_with_search_roots(base: &Path, parts: &[String], use_stmt: &UseStmt) -> Option<PathBuf> {
    if let Some(resolved) = resolve_parts_from_root(base, parts, use_stmt) {
        return Some(resolved);
    }

    let mut init_resolved = base.to_path_buf();
    for part in parts {
        init_resolved = init_resolved.join(part);
    }
    init_resolved = init_resolved.join("__init__");
    init_resolved.set_extension("spl");
    if init_resolved.exists() && init_resolved.is_file() {
        return Some(init_resolved);
    }

    let mut mod_resolved = base.to_path_buf();
    for part in parts {
        mod_resolved = mod_resolved.join(part);
    }
    mod_resolved = mod_resolved.join("mod");
    mod_resolved.set_extension("spl");
    if mod_resolved.exists() && mod_resolved.is_file() {
        return Some(mod_resolved);
    }

    let mut parent_dir = base.to_path_buf();
    for _ in 0..10 {
        if let Some(parent) = parent_dir.parent() {
            parent_dir = parent.to_path_buf();

            let mut parent_resolved = parent_dir.clone();
            for part in parts {
                parent_resolved = parent_resolved.join(part);
            }
            parent_resolved.set_extension("spl");
            if parent_resolved.exists() && parent_resolved.is_file() {
                return Some(prefer_package_init_for_member_import(parent_resolved, use_stmt));
            }

            if let Some(parent_resolved) = resolve_parts_from_root(&parent_dir, parts, use_stmt) {
                return Some(parent_resolved);
            }

            let parent_src = parent_dir.join("src");
            if parent_src.is_dir() {
                if let Some(src_resolved) = resolve_parts_from_root(&parent_src, parts, use_stmt) {
                    return Some(src_resolved);
                }
            }

            let mut parent_init_resolved = parent_dir.clone();
            for part in parts {
                parent_init_resolved = parent_init_resolved.join(part);
            }
            parent_init_resolved = parent_init_resolved.join("__init__");
            parent_init_resolved.set_extension("spl");
            if parent_init_resolved.exists() && parent_init_resolved.is_file() {
                return Some(parent_init_resolved);
            }

            let mut parent_mod_resolved = parent_dir.clone();
            for part in parts {
                parent_mod_resolved = parent_mod_resolved.join(part);
            }
            parent_mod_resolved = parent_mod_resolved.join("mod");
            parent_mod_resolved.set_extension("spl");
            if parent_mod_resolved.exists() && parent_mod_resolved.is_file() {
                return Some(parent_mod_resolved);
            }
        } else {
            break;
        }
    }

    None
}

pub(super) fn requested_import_names(target: &ImportTarget, out: &mut Vec<String>) {
    match target {
        ImportTarget::Glob => {}
        ImportTarget::Single(name) => out.push(name.clone()),
        ImportTarget::Aliased { name, .. } => out.push(name.clone()),
        ImportTarget::Group(targets) => {
            for nested in targets {
                requested_import_names(nested, out);
            }
        }
    }
}

pub(super) fn should_flatten_transitively(target: &ImportTarget) -> bool {
    matches!(target, ImportTarget::Group(_) | ImportTarget::Glob)
}

pub(super) fn file_might_define_requested_symbol(path: &Path, requested_names: &[String]) -> bool {
    if requested_names.is_empty() {
        return true;
    }

    let Ok(source) = fs::read_to_string(path) else {
        return false;
    };

    requested_names.iter().any(|name| {
        let fn_pat = format!("fn {}(", name);
        let extern_pat = format!("extern fn {}(", name);
        let type_pat = format!("type {}", name);
        let class_pat = format!("class {}", name);
        let struct_pat = format!("struct {}", name);
        let enum_pat = format!("enum {}", name);
        let trait_pat = format!("trait {}", name);
        let let_pat = format!("let {}", name);
        let const_pat = format!("const {}", name);
        source.contains(&fn_pat)
            || source.contains(&extern_pat)
            || source.contains(&type_pat)
            || source.contains(&class_pat)
            || source.contains(&struct_pat)
            || source.contains(&enum_pat)
            || source.contains(&trait_pat)
            || source.contains(&let_pat)
            || source.contains(&const_pat)
    })
}

/// Resolve a simple `use` path to a sibling `.spl` file.
/// Also checks stdlib location if sibling resolution fails.
pub(super) fn resolve_use_to_path(use_stmt: &UseStmt, base: &Path) -> Option<PathBuf> {
    let mut parts: Vec<String> = use_stmt
        .path
        .segments
        .iter()
        .filter(|s| s.as_str() != "crate")
        .cloned()
        .collect();

    // For Single/Aliased imports, the target name may be a module file (not a symbol).
    // Append it to the path so we try resolving `std.mcp.main_lazy_json` as
    // `mcp/main_lazy_json.spl` first, matching the interpreter's behavior.
    // If the file doesn't exist, resolve_use_to_path returns None and the
    // interpreter handles the UseStmt directly (treating target as a symbol).
    match &use_stmt.target {
        ImportTarget::Single(name) | ImportTarget::Aliased { name, .. } => {
            parts.push(name.clone());
        }
        ImportTarget::Group(_) | ImportTarget::Glob => {
            // For Group/Glob imports, path segments already contain the full module path
        }
    }

    if let Some(resolved) = resolve_parts_with_search_roots(base, &parts, use_stmt) {
        return Some(resolved);
    }

    if let Some(type_parts) = normalize_type_parts(&parts) {
        if let Some(resolved) = resolve_parts_with_search_roots(base, &type_parts, use_stmt) {
            return Some(resolved);
        }
    }

    // If not found, try stdlib location
    // Walk up the directory tree to find stdlib
    let mut current = base.to_path_buf();
    for _ in 0..10 {
        // Try various stdlib locations (matching interpreter behavior)
        for stdlib_subpath in &[
            "src/lib",
            // Preferred: repo layout uses src/std/*
            "src/std",
            // Legacy layouts kept for compatibility with older checkouts
            "src/std/src",
            "src/lib/std/src",
            "lib/std/src",
            "rust/lib/std/src",
            "simple/std_lib/src",
            "std_lib/src",
        ] {
            let stdlib_candidate = current.join(stdlib_subpath);
            if stdlib_candidate.exists() {
                // Handle "std" prefix stripping for std.* imports
                let stdlib_parts: Vec<String> = if !parts.is_empty() && parts[0] == "std" {
                    parts[1..].to_vec()
                } else if !parts.is_empty() && parts[0] == "std_lib" {
                    // Also handle std_lib.* imports -> strip std_lib prefix
                    parts[1..].to_vec()
                } else {
                    parts.clone()
                };

                if !stdlib_parts.is_empty() {
                    if stdlib_parts.len() == 1 && stdlib_parts[0] == "io" {
                        let compat_init = stdlib_candidate.join("nogc_sync_mut").join("io").join("__init__.spl");
                        if compat_init.exists() && compat_init.is_file() {
                            return Some(compat_init);
                        }
                    }

                    // Try resolving from stdlib
                    let mut stdlib_path = stdlib_candidate.clone();
                    for part in &stdlib_parts {
                        stdlib_path = stdlib_path.join(part);
                    }
                    stdlib_path.set_extension("spl");
                    if stdlib_path.exists() && stdlib_path.is_file() {
                        return Some(prefer_package_init_for_member_import(stdlib_path, use_stmt));
                    }

                    // Also try __init__.spl in stdlib
                    let mut stdlib_init_path = stdlib_candidate.clone();
                    for part in &stdlib_parts {
                        stdlib_init_path = stdlib_init_path.join(part);
                    }
                    stdlib_init_path = stdlib_init_path.join("__init__");
                    stdlib_init_path.set_extension("spl");
                    if stdlib_init_path.exists() && stdlib_init_path.is_file() {
                        return Some(stdlib_init_path);
                    }

                    // Also try mod.spl in stdlib
                    let mut stdlib_mod_path = stdlib_candidate.clone();
                    for part in &stdlib_parts {
                        stdlib_mod_path = stdlib_mod_path.join(part);
                    }
                    stdlib_mod_path = stdlib_mod_path.join("mod");
                    stdlib_mod_path.set_extension("spl");
                    if stdlib_mod_path.exists() && stdlib_mod_path.is_file() {
                        return Some(stdlib_mod_path);
                    }

                    for subdir in &[
                        "nogc_async_mut",
                        "nogc_sync_mut",
                        "nogc_async_immut",
                        "common",
                        "gc_async_mut",
                        "nogc_async_mut_noalloc",
                    ] {
                        let mut sub_init_path = stdlib_candidate.join(subdir);
                        for part in &stdlib_parts {
                            sub_init_path = sub_init_path.join(part);
                        }
                        sub_init_path = sub_init_path.join("__init__");
                        sub_init_path.set_extension("spl");
                        if sub_init_path.exists() && sub_init_path.is_file() {
                            return Some(sub_init_path);
                        }

                        let mut sub_path = stdlib_candidate.join(subdir);
                        for part in &stdlib_parts {
                            sub_path = sub_path.join(part);
                        }
                        sub_path.set_extension("spl");
                        if sub_path.exists() && sub_path.is_file() {
                            return Some(prefer_package_init_for_member_import(sub_path, use_stmt));
                        }
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

    None
}

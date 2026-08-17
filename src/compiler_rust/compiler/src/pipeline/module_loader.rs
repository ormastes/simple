//! Module loading and import resolution utilities.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};

use simple_parser::ast::{
    Argument, Capability, ConstStmt, Effect, Expr, FunctionDef, ImplBlock, ImportTarget, Module, Node, Type, UseStmt,
    Visibility,
};
use simple_parser::error_recovery::{ErrorHint, ErrorHintLevel};
use simple_parser::Parser;

use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::{
    flatten_owner_mangled_name, normalize_path_key, tag_function_module_owner,
    FLATTEN_GLOBAL_OWNER_MARKER_PREFIX, FLATTEN_IMPORT_BINDING_MARKER_PREFIX,
    FLATTEN_MODULE_OWNER_ATTR_PREFIX,
};
use crate::stdlib_variant::stdlib_root_candidates;
use crate::CompileError as _;

fn prefer_package_init_for_member_import(resolved: PathBuf, use_stmt: &UseStmt) -> PathBuf {
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

fn dotted_dir_from(current: &Path, segment: &str) -> Option<PathBuf> {
    let parent = current.parent()?;
    let current_name = current.file_name()?.to_str()?;
    let dotted_dir = parent.join(format!("{}.{}", current_name, segment));
    if dotted_dir.is_dir() {
        Some(dotted_dir)
    } else {
        None
    }
}

fn domain_to_dir(domain: &str) -> String {
    domain.replace('-', "_")
}

fn normalize_type_parts(parts: &[String]) -> Option<Vec<String>> {
    if parts.is_empty() {
        return None;
    }

    if parts.len() >= 2 && parts[0].contains('-') {
        let mut normalized = vec!["src".to_string(), "type".to_string(), domain_to_dir(&parts[0])];
        normalized.extend(parts[1..].iter().cloned());
        return Some(normalized);
    }

    if parts.len() == 1 {
        return Some(vec![
            "src".to_string(),
            "type".to_string(),
            "simple_lang".to_string(),
            parts[0].clone(),
        ]);
    }

    None
}

fn resolve_parts_from_root(root: &Path, parts: &[String], use_stmt: &UseStmt) -> Option<PathBuf> {
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

// Thread-local cache for directory listings to avoid repeated `read_dir` on the
// stdlib-variant candidate roots. `stdlib_root_candidates` yields per-tier variant
// dirs (e.g. `src/lib/variants/x86_64_avx2`) that usually do NOT exist, plus real
// dirs (`src/compiler`, its numbered layers) that are re-scanned once per import.
// Without memoization the pipeline loader re-`read_dir`s each of these on every
// `use` — thousands of `openat(..., O_DIRECTORY)` (many ENOENT) for a single load.
// Negatives are cached too (empty vec), so a missing variant dir is probed once.
thread_local! {
    static PIPELINE_DIR_LISTING_CACHE: RefCell<HashMap<PathBuf, Vec<(String, PathBuf)>>> =
        RefCell::new(HashMap::new());
}

/// Cached directory listing. Each entry is (file_name, full_path). Mirrors
/// `interpreter_module::path_resolution::cached_read_dir`. Returns an empty vec
/// for missing/unreadable dirs (and caches that), matching the previous
/// `fs::read_dir(dir).ok()` behaviour where any error meant "no entries".
fn cached_read_dir(dir: &Path) -> Vec<(String, PathBuf)> {
    if let Some(entries) = PIPELINE_DIR_LISTING_CACHE.with(|cache| cache.borrow().get(dir).cloned()) {
        return entries;
    }

    let mut entries = Vec::new();
    if let Ok(read_dir) = fs::read_dir(dir) {
        for entry in read_dir.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            entries.push((name, entry.path()));
        }
    }

    PIPELINE_DIR_LISTING_CACHE.with(|cache| {
        cache.borrow_mut().insert(dir.to_path_buf(), entries.clone());
    });
    entries
}

/// Clear the pipeline directory-listing cache. Mirrors
/// `path_resolution::clear_path_resolution_cache` so long-lived processes
/// (test runner, MCP/LSP servers) that reset module state also drop any
/// negatively-cached dir listings.
pub fn clear_pipeline_dir_listing_cache() {
    PIPELINE_DIR_LISTING_CACHE.with(|cache| cache.borrow_mut().clear());
}

fn resolve_numbered_parts_from_root(root: &Path, parts: &[String], use_stmt: &UseStmt) -> Option<PathBuf> {
    if parts.is_empty() {
        return None;
    }
    let mut current = root.to_path_buf();
    for (idx, part) in parts.iter().enumerate() {
        let is_last = idx + 1 == parts.len();
        if is_last {
            let mut file = current.join(part);
            file.set_extension("spl");
            if file.is_file() {
                return Some(prefer_package_init_for_member_import(file, use_stmt));
            }
            if let Some(alias) = layered_alias_child_dir(&current, part) {
                let init = alias.join("__init__.spl");
                if init.is_file() {
                    return Some(init);
                }
                let mut nested_file = alias.join(part);
                nested_file.set_extension("spl");
                if nested_file.is_file() {
                    return Some(prefer_package_init_for_member_import(nested_file, use_stmt));
                }
            }
            if let Some(alias_file) = layered_alias_child_file(&current, part) {
                return Some(prefer_package_init_for_member_import(alias_file, use_stmt));
            }
            for (name, path) in cached_read_dir(&current) {
                if !path.is_dir() {
                    continue;
                }
                let Some(dot) = name.find('.') else {
                    continue;
                };
                let prefix = &name[..dot];
                let suffix = &name[dot + 1..];
                if suffix == part
                    && !prefix.is_empty()
                    && prefix.len() <= 3
                    && prefix.chars().all(|c| c.is_ascii_digit())
                {
                    let init = path.join("__init__.spl");
                    if init.is_file() {
                        return Some(init);
                    }
                    let mut nested_file = path.join(part);
                    nested_file.set_extension("spl");
                    if nested_file.is_file() {
                        return Some(prefer_package_init_for_member_import(nested_file, use_stmt));
                    }
                }
            }
            return None;
        }

        let direct = current.join(part);
        if direct.is_dir() {
            current = direct;
            continue;
        }
        if let Some(alias) = layered_alias_child_dir(&current, part) {
            current = alias;
            continue;
        }

        let mut matched = None;
        for (name, path) in cached_read_dir(&current) {
            if !path.is_dir() {
                continue;
            }
            let Some(dot) = name.find('.') else {
                continue;
            };
            let prefix = &name[..dot];
            let suffix = &name[dot + 1..];
            if suffix == part && !prefix.is_empty() && prefix.len() <= 3 && prefix.chars().all(|c| c.is_ascii_digit()) {
                matched = Some(path);
                break;
            }
            let nested = path.join(part);
            if nested.is_dir() {
                matched = Some(nested);
                break;
            }
        }
        current = matched?;
    }
    None
}

fn layered_dir_alias_name(current: &Path) -> Option<String> {
    let name = current.file_name()?.to_str()?;
    if let Some(after_dot) = name.find('.') {
        let prefix = &name[..after_dot];
        let suffix = &name[after_dot + 1..];
        if !prefix.is_empty() && prefix.len() <= 3 && prefix.chars().all(|c| c.is_ascii_digit()) {
            return Some(suffix.to_string());
        }
    }
    Some(name.to_string())
}

fn layered_alias_child_dir(current: &Path, segment: &str) -> Option<PathBuf> {
    let alias_name = layered_dir_alias_name(current)?;
    let nested = current.join(alias_name).join(segment);
    if nested.is_dir() {
        Some(nested)
    } else {
        None
    }
}

fn layered_alias_child_file(current: &Path, segment: &str) -> Option<PathBuf> {
    let alias_name = layered_dir_alias_name(current)?;
    let mut nested = current.join(alias_name).join(segment);
    nested.set_extension("spl");
    if nested.is_file() {
        Some(nested)
    } else {
        None
    }
}

/// `true` when `dir` is the root of the enclosing repository/workspace.
///
/// An ancestor climb must stop here. Everything above belongs to a different
/// project (a sibling checkout, a scratch tree, the user's home directory) and
/// must never contribute modules to this build. A nested git worktree marks its
/// root with a `.git` **file**, not a directory, so `exists()` is the right test
/// — that is what makes `build/worktrees/x` and `.claude/worktrees/y` their own
/// boundaries rather than a name we have to blacklist.
fn is_workspace_boundary(dir: &Path) -> bool {
    dir.join(".git").exists() || dir.join(".jj").is_dir()
}

/// `true` for imports that name the project's own standard library.
///
/// These must resolve from the project's stdlib roots and nowhere else. The
/// importer-relative and ancestor-climbing strategies join the import verbatim
/// onto the importing file's directory and onto every ancestor, so `use std.x`
/// from `test/01_unit/a/b_spec.spl` also tries `test/01_unit/a/std/x.spl`,
/// `test/01_unit/std/x.spl`, `test/std/x.spl`, … Any `std/` folder along that
/// chain silently outranks `src/lib/x.spl`, and editing the real file then has
/// no observable effect at all.
fn is_project_stdlib_import(parts: &[String]) -> bool {
    parts
        .first()
        .map(|p| matches!(p.as_str(), "std" | "std_lib" | "lib"))
        .unwrap_or(false)
}

fn resolve_parts_with_search_roots(base: &Path, parts: &[String], use_stmt: &UseStmt) -> Option<PathBuf> {
    // Stdlib imports never resolve relative to the importing file — see
    // is_project_stdlib_import. The caller falls through to the project-rooted
    // stdlib search.
    if is_project_stdlib_import(parts) {
        return None;
    }
    if let Some(resolved) = resolve_parts_from_root(base, parts, use_stmt) {
        return Some(resolved);
    }
    if let Some(resolved) = resolve_numbered_parts_from_root(base, parts, use_stmt) {
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
            if let Some(parent_resolved) = resolve_numbered_parts_from_root(&parent_dir, parts, use_stmt) {
                return Some(parent_resolved);
            }

            let parent_src = parent_dir.join("src");
            if parent_src.is_dir() {
                if let Some(src_resolved) = resolve_parts_from_root(&parent_src, parts, use_stmt) {
                    return Some(src_resolved);
                }
                if let Some(src_resolved) = resolve_numbered_parts_from_root(&parent_src, parts, use_stmt) {
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

            // Never climb out of the enclosing repository.
            if is_workspace_boundary(&parent_dir) {
                break;
            }
        } else {
            break;
        }
    }

    None
}

fn resolve_from_stdlib_root(root: &Path, parts: &[String], use_stmt: &UseStmt) -> Option<PathBuf> {
    for stdlib_subpath in &[
        "src/lib",
        "src/std",
        "src/std/src",
        "src/lib/std/src",
        "lib/std/src",
        "rust/lib/std/src",
        "simple/std_lib/src",
        "std_lib/src",
    ] {
        let stdlib_candidate = root.join(stdlib_subpath);
        if !stdlib_candidate.exists() {
            continue;
        }

        let stdlib_parts: Vec<String> = if !parts.is_empty() && (parts[0] == "std" || parts[0] == "std_lib") {
            parts[1..].to_vec()
        } else {
            parts.to_vec()
        };

        if stdlib_parts.is_empty() {
            continue;
        }

        for stdlib_root in stdlib_root_candidates(&stdlib_candidate) {
            if stdlib_parts.len() == 1 && stdlib_parts[0] == "io" {
                let compat_init = stdlib_root.join("nogc_sync_mut").join("io").join("__init__.spl");
                if compat_init.exists() && compat_init.is_file() {
                    return Some(compat_init);
                }
            }

            let mut stdlib_path = stdlib_root.clone();
            for part in &stdlib_parts {
                stdlib_path = stdlib_path.join(part);
            }
            stdlib_path.set_extension("spl");
            if stdlib_path.exists() && stdlib_path.is_file() {
                return Some(prefer_package_init_for_member_import(stdlib_path, use_stmt));
            }

            let mut stdlib_init_path = stdlib_root.clone();
            for part in &stdlib_parts {
                stdlib_init_path = stdlib_init_path.join(part);
            }
            stdlib_init_path = stdlib_init_path.join("__init__");
            stdlib_init_path.set_extension("spl");
            if stdlib_init_path.exists() && stdlib_init_path.is_file() {
                return Some(stdlib_init_path);
            }

            let mut stdlib_mod_path = stdlib_root.clone();
            for part in &stdlib_parts {
                stdlib_mod_path = stdlib_mod_path.join(part);
            }
            stdlib_mod_path = stdlib_mod_path.join("mod");
            stdlib_mod_path.set_extension("spl");
            if stdlib_mod_path.exists() && stdlib_mod_path.is_file() {
                return Some(stdlib_mod_path);
            }

            if let Some(numbered) = resolve_numbered_parts_from_root(&stdlib_root, &stdlib_parts, use_stmt) {
                return Some(numbered);
            }

            for subdir in &[
                "nogc_async_mut",
                "nogc_sync_mut",
                "nogc_async_immut",
                "common",
                "gc_async_mut",
                "nogc_async_mut_noalloc",
            ] {
                let mut sub_init_path = stdlib_root.join(subdir);
                for part in &stdlib_parts {
                    sub_init_path = sub_init_path.join(part);
                }
                sub_init_path = sub_init_path.join("__init__");
                sub_init_path.set_extension("spl");
                if sub_init_path.exists() && sub_init_path.is_file() {
                    return Some(sub_init_path);
                }

                let mut sub_path = stdlib_root.join(subdir);
                for part in &stdlib_parts {
                    sub_path = sub_path.join(part);
                }
                sub_path.set_extension("spl");
                if sub_path.exists() && sub_path.is_file() {
                    return Some(prefer_package_init_for_member_import(sub_path, use_stmt));
                }

                if let Some(numbered) =
                    resolve_numbered_parts_from_root(&stdlib_root.join(subdir), &stdlib_parts, use_stmt)
                {
                    return Some(numbered);
                }
            }
        }
    }

    None
}

/// Splices `module`'s items into the caller's flat item list for the
/// `bin/simple run`/`-c` interpreted entry path. This is also the point where
/// each retained free function is tagged with its true owning-module path via a
/// synthetic attribute (name prefix `FLATTEN_MODULE_OWNER_ATTR_PREFIX`) pushed
/// onto `FunctionDef.attributes`. After this splice, the interpreter's single
/// flat registration pass in `evaluate_module_impl` (interpreter_eval.rs) can
/// no longer tell which file a `Node::Function` came from — the root cause of
/// the unqualified same-name/same-arity cross-module overload collision (see
/// doc/08_tracking/bug/interp_cross_module_struct_field_collision_2026-07-04.md).
/// The attribute travels *with* the node value (unlike a span side-table, which
/// collides when two files define a same-named fn at identical line/column), so
/// registration recovers the exact owner per node. See the const's doc comment
/// in `interpreter_state.rs`.
///
/// The `already_tagged` guard keeps the *innermost* owner: a function pulled in
/// through a nested import was already tagged by that deeper flatten pass
/// (nested loads run before this outer strip), so we must not overwrite it.
fn tag_node_function_owners(node: &mut Node, owner: &str) {
    let methods = match node {
        Node::Function(function) => {
            tag_function_module_owner(function, owner);
            return;
        }
        Node::Struct(definition) => &mut definition.methods,
        Node::Class(definition) => &mut definition.methods,
        Node::Enum(definition) => &mut definition.methods,
        Node::Trait(definition) => &mut definition.methods,
        Node::Impl(definition) => &mut definition.methods,
        Node::Mixin(definition) => &mut definition.methods,
        Node::Actor(definition) => &mut definition.methods,
        Node::Extend(definition) => &mut definition.methods,
        Node::ModDecl(module) => {
            if let Some(body) = &mut module.body {
                for item in body {
                    tag_node_function_owners(item, owner);
                }
            }
            return;
        }
        _ => return,
    };
    for method in methods {
        tag_function_module_owner(method, owner);
    }
}

fn import_binding_marker_name(importer: &str, local: &str, source_owner: &str, source_name: &str) -> String {
    format!(
        "{FLATTEN_IMPORT_BINDING_MARKER_PREFIX}{}:{importer}{}:{local}{}:{source_owner}{}:{source_name}",
        importer.len(),
        local.len(),
        source_owner.len(),
        source_name.len()
    )
}

fn append_flattened_import_binding_markers(
    items: &mut Vec<Node>,
    use_stmt: &UseStmt,
    module_path: &Path,
    owner_name: &str,
) {
    let Some(source_path) = resolve_use_to_path(use_stmt, module_path.parent().unwrap_or(Path::new("."))) else {
        return;
    };
    let source_name = normalize_path_key(&source_path).to_string_lossy().into_owned();
    let mut add_marker = |local_name: &str, source_symbol: &str| {
        items.push(Node::Const(ConstStmt {
            span: use_stmt.span,
            name: import_binding_marker_name(owner_name, local_name, &source_name, source_symbol),
            ty: None,
            value: Expr::Nil,
            visibility: Visibility::Private,
        }));
    };
    match &use_stmt.target {
        ImportTarget::Group(targets) => {
            for target in targets {
                match target {
                    ImportTarget::Single(name) => add_marker(name, name),
                    ImportTarget::Aliased { name, alias } => add_marker(alias, name),
                    _ => {}
                }
            }
        }
        ImportTarget::Glob => add_marker("*", "*"),
        ImportTarget::Single(_) | ImportTarget::Aliased { .. } => {}
    }
}

fn strip_flattened_import_nodes(module: Module, module_path: &Path) -> Module {
    let owner_path = normalize_path_key(module_path);
    let owner_name = owner_path.to_string_lossy();
    let owner_marker_name = format!("{FLATTEN_GLOBAL_OWNER_MARKER_PREFIX}{}", owner_path.to_string_lossy());
    let mut items = Vec::new();
    let mut next_global_already_tagged = false;
    for mut item in module.items {
        tag_node_function_owners(&mut item, &owner_name);
        if let Node::Const(marker) = &item {
            if marker.name.starts_with(FLATTEN_GLOBAL_OWNER_MARKER_PREFIX) {
                next_global_already_tagged = true;
                items.push(item);
                continue;
            }
            if marker.name.starts_with(FLATTEN_IMPORT_BINDING_MARKER_PREFIX) {
                items.push(item);
                continue;
            }
        }

        match item {
            Node::UseStmt(use_stmt) => {
                append_flattened_import_binding_markers(&mut items, &use_stmt, module_path, &owner_name);
                next_global_already_tagged = false;
            }
            Node::ExportUseStmt(export_use) => {
                // A re-export facade participates in the flattened interpreter
                // just like an ordinary import.  Keep its global binding chain
                // even though the ExportUseStmt itself is removed below: an
                // importer may resolve a mutable module global through this
                // facade (consumer -> facade -> defining module).
                if !export_use.path.segments.is_empty() {
                    let reexport_as_use = UseStmt {
                        span: export_use.span,
                        path: export_use.path,
                        target: export_use.target,
                        is_type_only: false,
                        is_lazy: false,
                    };
                    append_flattened_import_binding_markers(
                        &mut items,
                        &reexport_as_use,
                        module_path,
                        &owner_name,
                    );
                }
                next_global_already_tagged = false;
            }
            Node::Function(mut function) => {
                if function.name == "main" {
                    // An IMPORTED `main` must never become, or collide with,
                    // the program entry symbol -- which is why this used to
                    // `continue` and drop the node outright. Dropping it also
                    // destroyed the only definition `use m.{main as g}` could
                    // bind to, so the alias resolved to the ENTRY module's
                    // `main` and recursed forever (measured: `fatal runtime
                    // error: stack overflow`). Renaming keeps the original
                    // intent -- it is still not called `main`, so it cannot be
                    // mistaken for the entry point -- while preserving the body
                    // under an owner-unique symbol the alias can resolve to,
                    // the same way the native-project lane has always
                    // disambiguated same-named free functions by owner. See
                    // `doc/08_tracking/bug/flattened_lane_does_not_mangle_duplicate_function_names_2026-08-10.md`.
                    function.name = flatten_owner_mangled_name(&owner_name, "main");
                }
                items.push(Node::Function(function));
                next_global_already_tagged = false;
            }
            declaration @ (Node::Let(_) | Node::Const(_) | Node::Static(_)) => {
                if !next_global_already_tagged {
                    let span = match &declaration {
                        Node::Let(stmt) => stmt.span,
                        Node::Const(stmt) => stmt.span,
                        Node::Static(stmt) => stmt.span,
                        _ => unreachable!(),
                    };
                    items.push(Node::Const(ConstStmt {
                        span,
                        name: owner_marker_name.clone(),
                        ty: None,
                        value: Expr::Nil,
                        visibility: Visibility::Private,
                    }));
                }
                items.push(declaration);
                next_global_already_tagged = false;
            }
            other => {
                if matches!(
                    other,
                    Node::UseStmt(_)
                        | Node::MultiUse(_)
                        | Node::CommonUseStmt(_)
                        | Node::ExportUseStmt(_)
                        | Node::StructuredExportStmt(_)
                        | Node::AutoImportStmt(_)
                ) {
                    next_global_already_tagged = false;
                } else {
                    items.push(other);
                    next_global_already_tagged = false;
                }
            }
        }
    }
    Module {
        name: module.name,
        items,
    }
}

fn requested_import_names(target: &ImportTarget, out: &mut Vec<String>) {
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

fn should_flatten_transitively(target: &ImportTarget) -> bool {
    matches!(target, ImportTarget::Group(_) | ImportTarget::Glob)
}

fn source_snippet_for_span(source: &str, span: simple_parser::token::Span) -> Option<&str> {
    source.get(span.start..span.end)
}

fn should_flatten_nested_import(use_stmt: &UseStmt, source: &str) -> bool {
    if !should_flatten_transitively(&use_stmt.target) {
        return false;
    }

    match &use_stmt.target {
        ImportTarget::Group(_) => true,
        ImportTarget::Glob => {
            source_snippet_for_span(source, use_stmt.span).is_some_and(|snippet| snippet.contains('*'))
        }
        ImportTarget::Single(_) | ImportTarget::Aliased { .. } => false,
    }
}

/// True when a `Single`/`Aliased` import resolves to a standalone module file,
/// either by naming the file or one of its symbols. Package aggregators stay
/// lazy because their requested symbol may belong to a sibling provider.
///
/// `should_flatten_nested_import` only flattens `Group`/`Glob` forms, so a
/// whole-module `use a.b.c` brings the module's *type* into scope (via the
/// exports cache) but never compiles its `impl` method bodies into the codegen
/// unit — imported class methods then fail to link (undefined `Type_dot_m`) and
/// degrade to the interpreter. When the import targets a module file directly,
/// flattening that one file's definitions is the same operation `Group`/`Glob`
/// already perform, just keyed on the resolved path instead of the syntax.
fn single_import_targets_module_file(target: &ImportTarget, resolved: &Path) -> bool {
    matches!(target, ImportTarget::Single(_) | ImportTarget::Aliased { .. })
        && resolved.file_name().is_none_or(|name| name != "__init__.spl")
}

fn file_might_define_requested_symbol(path: &Path, requested_names: &[String]) -> bool {
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
        let val_pat = format!("val {}", name);
        let var_pat = format!("var {}", name);
        let const_pat = format!("const {}", name);
        let export_pat = format!("export {}", name);
        let export_comma_pat = format!(", {}", name);
        source.contains(&fn_pat)
            || source.contains(&extern_pat)
            || source.contains(&type_pat)
            || source.contains(&class_pat)
            || source.contains(&struct_pat)
            || source.contains(&enum_pat)
            || source.contains(&trait_pat)
            || source.contains(&let_pat)
            || source.contains(&val_pat)
            || source.contains(&var_pat)
            || source.contains(&const_pat)
            || source.contains(&export_pat)
            || source.contains(&export_comma_pat)
    })
}

fn load_matching_package_siblings(
    package_init_path: &Path,
    use_stmt: &UseStmt,
    visited: &mut HashSet<PathBuf>,
    importing_capabilities: Option<&[Capability]>,
    target_arch: simple_common::target::TargetArch,
) -> Result<Vec<Node>, CompileError> {
    let Some(package_dir) = package_init_path.parent() else {
        return Ok(Vec::new());
    };

    let mut requested_names = Vec::new();
    requested_import_names(&use_stmt.target, &mut requested_names);

    let mut sibling_files: Vec<PathBuf> = match fs::read_dir(package_dir) {
        Ok(entries) => entries
            .filter_map(|entry| entry.ok().map(|e| e.path()))
            .filter(|path| {
                path.extension().is_some_and(|ext| ext == "spl")
                    && path
                        .file_name()
                        .is_some_and(|name| name != "__init__.spl" && name != "mod_stub.spl")
                    && path.is_file()
                    && file_might_define_requested_symbol(path, &requested_names)
            })
            .collect(),
        Err(_) => return Ok(Vec::new()),
    };

    sibling_files.sort();

    let mut collected = Vec::new();
    for sibling_path in sibling_files {
        let imported =
            load_module_with_imports_internal(&sibling_path, visited, importing_capabilities, true, target_arch)?;
        collected.extend(imported.items);
    }

    Ok(collected)
}

/// Display parser error hints (warnings, etc.) to stderr
fn display_parser_hints(parser: &Parser, source: &str, path: &Path) {
    let hints = parser.error_hints();
    if hints.is_empty() {
        return;
    }

    // Check if non-fatal parser hints should be suppressed. Bootstrap native
    // rebuilds parse hundreds of modules under the interpreter; formatting
    // every warning dominates the run and hides the first real failure.
    let suppress_non_errors =
        std::env::var("SIMPLE_ALLOW_DEPRECATED").is_ok() || std::env::var("SIMPLE_NO_DEPRECATED_WARNINGS").is_ok();

    // Index the source lines ONCE. `source.lines().nth(n)` re-walks the file
    // from byte 0 for every hint, making the printer O(hints x file lines).
    let source_lines: Vec<&str> = source.lines().collect();

    // Display hints to stderr
    for hint in hints {
        if suppress_non_errors && !matches!(hint.level, ErrorHintLevel::Error) {
            continue;
        }

        let level_str = match hint.level {
            ErrorHintLevel::Error => "\x1b[31merror\x1b[0m",     // red
            ErrorHintLevel::Warning => "\x1b[33mwarning\x1b[0m", // yellow
            ErrorHintLevel::Info => "\x1b[36minfo\x1b[0m",       // cyan
            ErrorHintLevel::Hint => "\x1b[32mhint\x1b[0m",       // green
        };

        eprintln!("{}: {}", level_str, hint.message);
        eprintln!("  --> {}:{}:{}", path.display(), hint.span.line, hint.span.column);

        // Show source line with caret
        if let Some(line) = hint.span.line.checked_sub(1).and_then(|i| source_lines.get(i)) {
            eprintln!("   |");
            eprintln!("{:3} | {}", hint.span.line, line);
            eprintln!("   | {}^", " ".repeat(hint.span.column - 1));
        }

        if let Some(ref suggestion) = hint.suggestion {
            eprintln!("\n{}", suggestion);
        }

        if let Some(ref help) = hint.help {
            eprintln!("\n{}", help);
        }

        eprintln!(); // blank line between hints
    }
}

/// Application type for startup optimization (#1979)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum StartupAppType {
    /// Command-line tool (minimal resources)
    #[default]
    Cli,
    /// Terminal UI application (terminal mode, buffers)
    Tui,
    /// Graphical application (window, GPU context)
    Gui,
    /// Background service/daemon (IPC, signal handlers)
    Service,
    /// Interactive REPL (history, line editor)
    Repl,
}

impl StartupAppType {
    /// Parse from string
    #[allow(clippy::should_implement_trait)] // reason: standard trait signature does not match this fallible or extended variant
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "cli" => Some(Self::Cli),
            "tui" => Some(Self::Tui),
            "gui" => Some(Self::Gui),
            "service" => Some(Self::Service),
            "repl" => Some(Self::Repl),
            _ => None,
        }
    }

    /// Convert to u8 for SMF header
    pub fn to_smf_byte(self) -> u8 {
        match self {
            Self::Cli => 0,
            Self::Tui => 1,
            Self::Gui => 2,
            Self::Service => 3,
            Self::Repl => 4,
        }
    }
}

/// Window hints for GUI applications (#1986)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StartupWindowHints {
    pub width: u16,
    pub height: u16,
    pub title: String,
}

impl Default for StartupWindowHints {
    fn default() -> Self {
        Self {
            width: 1280,
            height: 720,
            title: "Simple Application".to_string(),
        }
    }
}

/// Startup configuration extracted from module decorators (#1979, #1986)
#[derive(Debug, Clone, Default)]
pub struct StartupConfig {
    /// Application type from @app_type decorator
    pub app_type: StartupAppType,
    /// Window hints from @window_hints decorator
    pub window_hints: StartupWindowHints,
    /// Whether @app_type was explicitly set
    pub has_app_type: bool,
    /// Whether @window_hints was explicitly set
    pub has_window_hints: bool,
}

/// Extract startup configuration from a module's main function decorators.
///
/// Looks for:
/// - `@app_type("gui")` - application type
/// - `@window_hints(width=1920, height=1080, title="My App")` - window configuration
///
/// Returns None if no main function found.
pub fn extract_startup_config(module: &Module) -> Option<StartupConfig> {
    // Find the main function
    for item in &module.items {
        if let Node::Function(func) = item {
            if func.name == "main" {
                return Some(extract_startup_config_from_decorators(&func.decorators));
            }
        }
    }
    None
}

/// Protect `?` characters inside string literals from being altered by
/// `strip_optionals`.  Replaces them with a sentinel that is restored later.
pub(crate) fn protect_question_marks_in_strings(s: &str) -> String {
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut out = Vec::with_capacity(len + 512);
    let mut i = 0;
    const SENTINEL: &[u8] = b"\x00QMARK\x00";

    while i < len {
        // Line comment — pass through unchanged
        if bytes[i] == b'#' {
            while i < len && bytes[i] != b'\n' {
                out.push(bytes[i]);
                i += 1;
            }
            continue;
        }

        // Triple-quoted string """..."""
        if i + 2 < len && bytes[i] == b'"' && bytes[i + 1] == b'"' && bytes[i + 2] == b'"' {
            out.push(b'"');
            out.push(b'"');
            out.push(b'"');
            i += 3;
            while i < len {
                if i + 2 < len && bytes[i] == b'"' && bytes[i + 1] == b'"' && bytes[i + 2] == b'"' {
                    out.push(b'"');
                    out.push(b'"');
                    out.push(b'"');
                    i += 3;
                    break;
                }
                if bytes[i] == b'\\' && i + 1 < len {
                    out.push(bytes[i]);
                    out.push(bytes[i + 1]);
                    i += 2;
                    continue;
                }
                if bytes[i] == b'?' {
                    out.extend_from_slice(SENTINEL);
                } else {
                    out.push(bytes[i]);
                }
                i += 1;
            }
            continue;
        }

        // Double-quoted string "..."
        if bytes[i] == b'"' {
            out.push(b'"');
            i += 1;
            while i < len && bytes[i] != b'"' {
                if bytes[i] == b'\\' && i + 1 < len {
                    out.push(bytes[i]);
                    out.push(bytes[i + 1]);
                    i += 2;
                    continue;
                }
                if bytes[i] == b'?' {
                    out.extend_from_slice(SENTINEL);
                } else {
                    out.push(bytes[i]);
                }
                i += 1;
            }
            if i < len {
                out.push(b'"');
                i += 1;
            }
            continue;
        }

        out.push(bytes[i]);
        i += 1;
    }

    String::from_utf8(out).unwrap_or_else(|_| s.to_string())
}

/// Bootstrap-only: strip optional type suffix (`?`) and convert `.?` existence
/// checks, while preserving `??` (null coalescing) and `?.` (optional chaining).
fn strip_optionals(mut s: String) -> String {
    // Step 0: Protect `?` inside string literals
    s = protect_question_marks_in_strings(&s);

    // Step 1: Protect `??` and `?.` operators by replacing with placeholders
    s = s.replace("??", "\x00NULLCOAL\x00");
    s = s.replace("?.", "\x00OPTCHAIN\x00");

    // Step 2: Convert `.?` existence checks to `!= nil`
    s = s.replace(".?:", " != nil:");
    s = s.replace(".? ", " != nil ");
    s = s.replace(".?\n", " != nil\n");
    s = s.replace(".?\r\n", " != nil\r\n");
    s = s.replace(".?)", " != nil)");
    s = s.replace(".?,", " != nil,");

    // Step 3: Strip remaining `?` (type suffixes like `Type?`)
    for pat in ["? ", "?\n", "?\r\n", "?\t", "?,", "?)", "?]", "?>", "?:", "?=", "?;"] {
        while s.contains(pat) {
            s = s.replace(pat, &pat[1..]); // drop leading '?'
        }
    }
    // Trailing ? at EOF
    if s.ends_with('?') {
        s.pop();
    }

    // Step 4: Restore `??` and `?.` operators
    s = s.replace("\x00NULLCOAL\x00", "??");
    s = s.replace("\x00OPTCHAIN\x00", "?.");

    // Step 5: Restore `?` inside string literals
    s = s.replace("\x00QMARK\x00", "?");
    s
}

/// Extract startup configuration from a list of decorators.
fn extract_startup_config_from_decorators(decorators: &[simple_parser::ast::Decorator]) -> StartupConfig {
    let mut config = StartupConfig::default();

    for decorator in decorators {
        // Check decorator name - can be Identifier or Call
        let (name, args) = match &decorator.name {
            Expr::Identifier(name) => (name.as_str(), decorator.args.as_ref()),
            Expr::Call { callee, args } => {
                // @app_type("gui") is parsed as Call { callee: Identifier("app_type"), args: [...] }
                if let Expr::Identifier(name) = callee.as_ref() {
                    (name.as_str(), Some(args))
                } else {
                    continue;
                }
            }
            _ => continue,
        };

        match name {
            "app_type" => {
                // @app_type("gui") - first positional argument is the type
                if let Some(args) = args {
                    if let Some(first_arg) = args.first() {
                        if let Some(type_str) = extract_string_from_arg(first_arg) {
                            if let Some(app_type) = StartupAppType::from_str(&type_str) {
                                config.app_type = app_type;
                                config.has_app_type = true;
                            }
                        }
                    }
                }
            }
            "window_hints" => {
                // @window_hints(width=1920, height=1080, title="My App")
                if let Some(args) = args {
                    for arg in args {
                        // Argument is a struct with name: Option<String> and value: Expr
                        if let Some(arg_name) = &arg.name {
                            match arg_name.as_str() {
                                "width" => {
                                    if let Some(w) = extract_integer_from_expr(&arg.value) {
                                        config.window_hints.width = w as u16;
                                        config.has_window_hints = true;
                                    }
                                }
                                "height" => {
                                    if let Some(h) = extract_integer_from_expr(&arg.value) {
                                        config.window_hints.height = h as u16;
                                        config.has_window_hints = true;
                                    }
                                }
                                "title" => {
                                    if let Some(t) = extract_string_from_expr(&arg.value) {
                                        config.window_hints.title = t;
                                        config.has_window_hints = true;
                                    }
                                }
                                _ => {}
                            }
                        }
                        // Ignore positional args for window_hints
                    }
                }
            }
            _ => {}
        }
    }

    config
}

/// Extract string value from an argument
fn extract_string_from_arg(arg: &Argument) -> Option<String> {
    extract_string_from_expr(&arg.value)
}

/// Extract string value from an expression
fn extract_string_from_expr(expr: &Expr) -> Option<String> {
    match expr {
        Expr::String(s) => Some(s.clone()),
        Expr::TypedString(s, _) => Some(s.clone()),
        // Handle FString (interpolated strings) - extract if it's just a literal
        Expr::FString { parts, .. } => {
            if parts.len() == 1 {
                if let simple_parser::ast::FStringPart::Literal(s) = &parts[0] {
                    return Some(s.clone());
                }
            }
            None
        }
        _ => None,
    }
}

/// Extract integer value from an expression
fn extract_integer_from_expr(expr: &Expr) -> Option<i64> {
    match expr {
        Expr::Integer(n) => Some(*n),
        Expr::TypedInteger(n, _) => Some(*n),
        _ => None,
    }
}

/// Extract capabilities from a module's `requires [...]` statement.
/// Returns None if no requires statement found (unrestricted module).
pub fn extract_module_capabilities(module: &Module) -> Option<Vec<Capability>> {
    for item in &module.items {
        if let Node::RequiresCapabilities(stmt) = item {
            return Some(stmt.capabilities.clone());
        }
    }
    None
}

/// Extract function effects from a module.
/// Returns a list of (function_name, effects) pairs.
pub fn extract_function_effects(module: &Module) -> Vec<(String, Vec<Effect>)> {
    let mut results = Vec::new();
    for item in &module.items {
        if let Node::Function(func) = item {
            if !func.effects.is_empty() {
                results.push((func.name.clone(), func.effects.clone()));
            }
        }
    }
    results
}

/// Check if a function's effects are compatible with a module's capabilities.
/// Returns an error message if incompatible, None if compatible.
pub fn check_import_compatibility(
    func_name: &str,
    func_effects: &[Effect],
    importing_capabilities: &[Capability],
) -> Option<String> {
    // If importing module is unrestricted, all imports are allowed
    if importing_capabilities.is_empty() {
        return None;
    }

    for effect in func_effects {
        let required_cap = match effect {
            Effect::Pure => Some(Capability::Pure),
            Effect::Io => Some(Capability::Io),
            Effect::Net => Some(Capability::Net),
            Effect::Fs => Some(Capability::Fs),
            Effect::Unsafe => Some(Capability::Unsafe),
            Effect::Async => None,       // Async is always allowed
            Effect::Verify => None,      // Verification mode marker, no capability
            Effect::Trusted => None,     // Trusted boundary marker, no capability
            Effect::Ghost => None,       // Ghost is compile-time only, no capability
            Effect::AutoLean(_) => None, // AutoLean is compile-time only, no capability
        };

        if let Some(cap) = required_cap {
            if !importing_capabilities.contains(&cap) {
                return Some(format!(
                    "cannot import function '{}' with @{} effect into module with capabilities [{}]",
                    func_name,
                    effect.decorator_name(),
                    importing_capabilities
                        .iter()
                        .map(|c| c.name())
                        .collect::<Vec<_>>()
                        .join(", ")
                ));
            }
        }
    }

    None
}

/// Naive resolver for `use foo` when running single-file programs from the CLI.
///
/// Recursively loads sibling modules and flattens their items into the root module.
pub fn load_module_with_imports(path: &Path, visited: &mut HashSet<PathBuf>) -> Result<Module, CompileError> {
    load_module_with_imports_for_target(path, visited, simple_common::target::TargetArch::host())
}

/// Collect same-named struct/class field-layout variants from a flattened
/// module, keyed by bare type name.
///
/// The run/JIT lane (`run_file_jit`) has no import-collection pass of its
/// own: it lowers the flattened module directly, so the HIR lowerer's global
/// struct registries stay empty and a field read that only exists on a
/// non-registered variant (three `GlyphBitmap` classes; only spl_fonts' has
/// `gbm_*` fields) fails closed with "Cannot infer field type" and de-JITs
/// the whole module (~100-1000x slowdown). The lowerer's duplicate-variant
/// consensus fallback fixes exactly this — but only when this map is
/// populated. Only names with two or more DISTINCT layouts are kept, matching
/// native_project's `record_struct_fields` semantics (identical re-imports of
/// the same layout are not collisions).
pub fn collect_duplicate_struct_defs(
    module: &Module,
) -> HashMap<String, Vec<Vec<(String, Type)>>> {
    let mut by_name: HashMap<String, Vec<Vec<(String, Type)>>> = HashMap::new();
    for item in &module.items {
        let (name, fields) = match item {
            Node::Struct(s) if !s.fields.is_empty() => (
                &s.name,
                s.fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect::<Vec<_>>(),
            ),
            Node::Class(c) if !c.fields.is_empty() => (
                &c.name,
                c.fields.iter().map(|f| (f.name.clone(), f.ty.clone())).collect::<Vec<_>>(),
            ),
            _ => continue,
        };
        let variants = by_name.entry(name.clone()).or_default();
        if !variants.iter().any(|candidate| candidate == &fields) {
            variants.push(fields);
        }
    }
    by_name.into_iter().filter(|(_, v)| v.len() > 1).collect()
}


pub fn load_module_with_imports_for_target(
    path: &Path,
    visited: &mut HashSet<PathBuf>,
    target_arch: simple_common::target::TargetArch,
) -> Result<Module, CompileError> {
    let mut module = load_module_with_imports_internal(path, visited, None, true, target_arch)?;
    append_root_import_binding_markers(&mut module, path);
    warn_duplicate_private_signatures(&module);
    warn_method_arity_collisions(&module);
    warn_cross_impl_method_collisions(&module);
    Ok(module)
}

/// Emit import-binding markers for the ROOT module's own `use` statements.
///
/// `strip_flattened_import_nodes` emits markers only while flattening
/// *imported* modules; the entry module's `use state.{values}` never got one,
/// so entry-frame envs carried imported globals with NO owner binding. A
/// lambda (or any frame) writing such an alias then had no owner to sync to
/// and the write silently missed the defining module's global store — the
/// stage-4 stale-global class. Root-defined functions register under the
/// `"<entry>"` owner sentinel (see interpreter_eval), so the markers use that
/// importer key.
fn append_root_import_binding_markers(module: &mut Module, path: &Path) {
    let mut markers = Vec::new();
    for item in &module.items {
        match item {
            Node::UseStmt(use_stmt) => {
                append_flattened_import_binding_markers(&mut markers, use_stmt, path, "<entry>");
            }
            Node::MultiUse(multi_use) => {
                for (module_path, target) in &multi_use.imports {
                    let temp_use = UseStmt {
                        span: multi_use.span,
                        path: module_path.clone(),
                        target: target.clone(),
                        is_type_only: multi_use.is_type_only,
                        is_lazy: false,
                    };
                    append_flattened_import_binding_markers(&mut markers, &temp_use, path, "<entry>");
                }
            }
            _ => {}
        }
    }
    module.items.splice(0..0, markers);
}

/// Diagnostic: warn when two or more co-compiled top-level functions share a
/// registry key but have differing signatures.
///
/// Once import flattening merges two same-named definitions, a call may silently
/// dispatch to the wrong one — nil / garbage in the interpreter, NULL-deref SIGSEGV
/// under Cranelift (the `aes_gcm`/`hkdf` `_append_bytes` case).
///
/// **Resolution policy, measured 2026-08-01 — the previous description here was
/// wrong on both halves.** This comment used to read "Functions resolve by bare name
/// (interpreter `HashMap<String, FunctionDef>`; codegen `func_ids`, last-write-wins)".
/// Neither clause survives a two-module experiment (`a.spl` and `b.spl` each defining
/// `fn who() -> text`, plus a third file importing both):
///
/// - ~~The **interpreter does not resolve by bare name alone.** A call made from
///   *inside* a defining module is resolved against that module's owner tag (see
///   `FLATTEN_MODULE_OWNER_ATTR_PREFIX` and `FUNCTION_MODULE_OWNER`), so `a.call_a()`
///   keeps reaching `a.who` and `b.call_b()` keeps reaching `b.who`, in either import
///   order. It is only the bare-name *fallback* — a call from a third module that
///   defines neither — that collapses.~~
///
///   **RETRACTED 2026-08-17 — this bullet is FALSE, and it is the dangerous kind of
///   false: it tells a maintainer that in-module calls are already safe.** Re-run of
///   the very experiment it describes (`a.spl`/`b.spl` each defining `fn who() -> text`,
///   a third file importing both, `bin/simple run`): `call_a()` AND `call_b()` both
///   printed `from_A`. Swapping the two `use` lines made both print `from_B`. The
///   interpreter is first-import-wins for the in-module call too, exactly like the
///   third-module fallback — the owner tag does not rescue it.
///
///   Three further measurements pin the mechanism:
///   * It is **not** specific to the `_` private-helper convention — a public `who()`
///     collides identically (the bullet above used a public name and still got it wrong).
///   * It is **not** limited to identical signatures. With A's `shared_arity()` taking
///     no parameters and B's taking one, B's own wrapper calls `shared_arity(7)` and
///     reaches A's zero-parameter body: the argument is silently DISCARDED and **no
///     arity error fires**.
///   * The owner-tag tie-break in `select_overload` (`interpreter_call/mod.rs:177`) is
///     **never reached**. Under `SIMPLE_DEBUG_OVERLOAD_SELECT=1` the probe printed no
///     `[module-tie]` line at all, so `FUNCTION_OVERLOADS[name]` holds fewer than two
///     candidates by dispatch time — only one definition survives into the registry and
///     there is nothing for the tie-break to choose between. Note this diagnostic
///     (`warn_duplicate_private_signatures`) still sees BOTH definitions in
///     `module.items` and warns about them, so the loss happens between this pass and
///     interpreter registration. Fixing `select_overload` alone cannot help; the
///     registry must keep both definitions (owner-scoped keys or mangling).
///
///   Regression fixtures + specs, all currently RED by design:
///   `test/01_unit/compiler/pipeline/cross_module_symbol_collision_spec.spl`,
///   `test/01_unit/compiler/pipeline/cross_module_collision_detection_spec.spl`,
///   `test/01_unit/compiler/pipeline/fixtures/probe_xmod_collision.spl`.
/// - **Codegen is first-import-wins, not last-write-wins.** Flip the two `use` lines
///   and the surviving definition flips with them, under both the Cranelift JIT and
///   `compile --native` (the two native artifacts differ byte-wise, so the winner is
///   baked in at compile time).
/// - For the third-module caller, **every** engine — interpreter fallback, JIT and
///   native alike — is first-import-wins. That is the shape a spec has: it imports
///   its subject and something else, and defines neither.
///
/// Do not restate a registry policy here from reading one engine. Four divergent
/// policies exist in this tree; the only reliable method is the two-module
/// experiment above, run per engine, with the import order swapped.
///
/// **Scope widened 2026-08-01.** This check used to skip every name that did not
/// start with `_`, and every qualified (`Type.method`) name, on the assumption that
/// only the private per-file helper convention could collide and that "methods are
/// qualified and cannot collide on a bare name". Both halves of that assumption are
/// wrong in the same way:
///
/// - Public free functions live in the *same* flat last-write-wins table as private
///   ones. Nothing about a leading `_` changes how the registry is keyed.
/// - A qualified `Type.method` key is only unique per *type*, not per *module*. Two
///   modules that both define `impl Type` with the same method name produce the same
///   key and clobber each other exactly like the free-function case (the sibling
///   check `find_method_arity_collisions` only sees collisions *within one* impl
///   block, so the cross-module case had no detector at all).
/// - Two same-name overloads in one file (e.g. `expect(value: bool)` alongside
///   `expect(value)`) are the same hazard and are now reported too.
///
/// The consequence of the old narrow scope was that "no collision warning was
/// printed" was routinely read as "nothing collided", when in fact the entire
/// public and method half of the family was unwarned. See
/// `doc/08_tracking/bug/diag_stage_facet_cross_module_collision_under_test_2026-07-06.md`
/// ("Why 'no collision warning was printed' proves nothing").
///
/// **Scope widened again 2026-08-01 (same-signature arm).** The check used to bail
/// out whenever all the colliding definitions had *identical* signatures, under the
/// comment "all identical → harmless under last-write-wins". That reasoning is
/// inverted. Identical signatures are the *most* dangerous case, not the harmless
/// one: one definition silently wins and the others are discarded, and because the
/// signatures agree there is no type error, no arity error and no ambiguity fallback
/// to surface it. The call site is indistinguishable from a correct one. That made
/// the single collision shape undetectable by any other means the single shape that
/// was never reported.
///
/// The concrete damage is a vacuity class, not just a wrong answer: a spec that
/// correctly imports its subject, and whose local copy has already been removed, can
/// still be served by an unrelated module's same-named function and stay green
/// through a sabotage of the file it imports. See
/// `doc/08_tracking/bug/vacuous_spec_census_2026-07-30.md`
/// ("A FOURTH vacuity shape: name-collision hijack").
///
/// The same-signature arm is **warn-only and default-off**, behind
/// `SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1`, because that family is much larger than
/// the differing-signature family and would otherwise bury the original warning.
///
/// Non-breaking diagnostic only. The real fix is to key the registry on
/// (module path, name) rather than on the name alone; until then the workaround is
/// to rename one of the colliding definitions. See bug
/// `compiler_cross_module_private_symbol_collision_2026-06-16`.
/// Render a function signature for collision comparison. `Debug` output is stable
/// within a build; the common `Type` Debug forms are simplified for readability.
fn render_signature(f: &FunctionDef) -> String {
    let render = |t: &Type| -> String {
        format!("{t:?}")
            .replace("Array { element: ", "[")
            .replace(", size: None }", "]")
            .replace("Simple(\"", "")
            .replace("\")", "")
    };
    let params: Vec<String> = f
        .params
        .iter()
        .map(|p| p.ty.as_ref().map(&render).unwrap_or_else(|| "?".to_string()))
        .collect();
    let ret = f.return_type.as_ref().map(&render).unwrap_or_else(|| "()".to_string());
    format!("({})->{ret}", params.join(","))
}

/// Best-effort source-module attribution for a function in the *flattened* module.
///
/// `strip_flattened_import_nodes` stamps every retained imported free function with
/// a synthetic `FLATTEN_MODULE_OWNER_ATTR_PREFIX` attribute carrying its true owning
/// file (see the doc comment on that function). Functions belonging to the entry file
/// itself never pass through that splice and so carry no tag.
fn function_owner_module(f: &FunctionDef) -> &str {
    f.attributes
        .iter()
        .find_map(|a| a.name.strip_prefix(FLATTEN_MODULE_OWNER_ATTR_PREFIX))
        .unwrap_or("<entry file>")
}

/// Env gate for the same-signature half of the collision diagnostic.
///
/// Default OFF. The same-signature family is far larger than the differing-signature
/// family (every module pair that re-declares an identically-typed helper trips it),
/// so turning it on unconditionally would bury the existing warning under noise on a
/// full test/bootstrap run. Opt in with `SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1`.
fn same_signature_diag_enabled() -> bool {
    use std::sync::OnceLock;
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("SIMPLE_DIAG_SAME_SIGNATURE_COLLISION")
            .map(|v| v != "0" && !v.is_empty())
            .unwrap_or(false)
    })
}

fn warn_duplicate_private_signatures(module: &Module) {
    use std::collections::HashMap;
    use std::sync::{Mutex, OnceLock};

    let mut by_name: HashMap<&str, Vec<(String, &str)>> = HashMap::new();
    // Classes live in the same flat by-name registry as functions (see
    // `classes.insert(c.name.clone(), ...)` in interpreter/node_exec.rs), so two
    // co-loaded modules that each define a same-named class cross-dispatch method
    // bodies onto instances of the wrong class. The symptom does NOT look like a
    // collision — it reads as "method not found" or "no field named X" on a class
    // that plainly has the member. See
    // doc/08_tracking/bug/interp_class_name_collision_breaks_test_db_persistence_2026-08-10.md
    let mut classes_by_name: HashMap<&str, Vec<&str>> = HashMap::new();
    for item in &module.items {
        match item {
            Node::Function(f) => {
                // Every top-level function participates in the flat registry: private
                // helpers, public free functions, and qualified `Type.method` entries
                // alike. Do NOT reintroduce a `starts_with('_')` / `contains('.')` skip
                // here — that is precisely the blind spot documented above.
                by_name
                    .entry(f.name.as_str())
                    .or_default()
                    .push((render_signature(f), function_owner_module(f)));
            }
            Node::Class(c) => {
                // ClassDef itself carries no owner tag; its methods do (the flatten
                // pass stamps every method via `tag_node_function_owners`), so the
                // first method's owner attributes the class. A method-less class
                // falls back to "<entry file>".
                let owner = c
                    .methods
                    .first()
                    .map(function_owner_module)
                    .unwrap_or("<entry file>");
                classes_by_name.entry(c.name.as_str()).or_default().push(owner);
            }
            _ => {}
        }
    }

    // Warn once per (name, signature-set) per process so a full test/bootstrap run
    // that re-loads the same stdlib does not repeat the same warning thousands of times.
    static WARNED: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();
    let warned = WARNED.get_or_init(|| Mutex::new(HashSet::new()));

    let mut names: Vec<&str> = by_name.keys().copied().collect();
    names.sort();
    for name in names {
        let entries = &by_name[name];
        if entries.len() < 2 {
            continue;
        }
        let sigs: Vec<&String> = entries.iter().map(|(sig, _)| sig).collect();
        let mut distinct: Vec<&String> = sigs.clone();
        distinct.sort();
        distinct.dedup();
        let kind = if name.contains('.') {
            "method"
        } else if name.starts_with('_') {
            "private helper"
        } else {
            "public function"
        };
        if distinct.len() < 2 {
            // ------------------------------------------------------------------
            // SAME-SIGNATURE COLLISION.
            //
            // This arm used to be `continue` with the comment "all identical →
            // harmless under last-write-wins". That is exactly backwards, and it
            // made the *only* collision shape that no other tool can detect the
            // *one* shape that was never reported.
            //
            // Two co-compiled definitions with identical signatures are not
            // harmless: one of them silently wins and the other is discarded.
            // Because the signatures agree, no type error, no arity error and no
            // ambiguity fallback ever fires — the call simply runs a different
            // module's body than the one the caller imported. That is a silent
            // wrong answer, and it is undetectable from the call site.
            //
            // It is also the mechanism behind a whole vacuity class: a spec can
            // correctly import its subject, be green, and still be testing some
            // other module's same-named function. See
            // doc/08_tracking/bug/vacuous_spec_census_2026-07-30.md
            // ("A FOURTH vacuity shape: name-collision hijack").
            //
            // Warn-only and default-off (see `same_signature_diag_enabled`); this
            // is deliberately NOT promoted to an error here.
            // ------------------------------------------------------------------
            if !same_signature_diag_enabled() {
                continue;
            }
            let mut owners: Vec<&str> = entries.iter().map(|(_, owner)| *owner).collect();
            owners.sort();
            owners.dedup();
            if owners.len() < 2 {
                // Same file declaring the same signature twice is a plain local
                // redefinition, not a cross-module hijack. Left to the existing
                // same-file overload checks so this diagnostic stays about the
                // cross-module case it was added for.
                continue;
            }
            let key = format!("samesig|{name}|{}|{}", distinct[0], owners.join("|"));
            if let Ok(mut set) = warned.lock() {
                if !set.insert(key) {
                    continue;
                }
            }
            eprintln!(
                "warning: {} `{}` has {} co-compiled definitions across {} modules with the \
                 SAME signature ({}) — one silently wins and the rest are discarded. Because the \
                 signatures agree, no type/arity error and no ambiguity fallback can fire, so a \
                 call resolves to a different module's body than the one it imported: a silent \
                 wrong answer, and the shape that makes an importing spec vacuous. Defined in: \
                 {}. Rename one of the definitions to a unique name. \
                 [compiler_cross_module_private_symbol_collision]",
                kind,
                name,
                entries.len(),
                owners.len(),
                distinct[0],
                owners.join(", "),
            );
            continue;
        }
        let key = format!(
            "{name}|{}",
            distinct.iter().map(|s| s.as_str()).collect::<Vec<_>>().join("|")
        );
        if let Ok(mut set) = warned.lock() {
            if !set.insert(key) {
                continue;
            }
        }
        eprintln!(
            "warning: {} `{}` has {} co-compiled definitions with {} differing \
             signatures ({}); JIT call sites resolve by exact arg-type match (mangled `$dupN` \
             variants), falling back to the last definition when types are ambiguous — a \
             fallback hit may still dispatch to the wrong one. Rename the conflicting helper(s) \
             to a unique name. [compiler_cross_module_private_symbol_collision]",
            kind,
            name,
            sigs.len(),
            distinct.len(),
            distinct.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(" vs "),
        );
    }

    // Class-name collisions. Unlike functions there is no signature to compare —
    // the interpreter's class registry is keyed on the bare name alone, so ANY
    // cross-module duplicate mis-dispatches. Always-on (not behind the same-sig
    // env gate): the census of the whole repo is large, but co-loading into ONE
    // flattened module is exactly the live, wrong-answer case. Warn once per
    // (name, owner-set) per process. Same-file redefinition is left to local
    // redefinition checks.
    let mut class_names: Vec<&str> = classes_by_name.keys().copied().collect();
    class_names.sort();
    for name in class_names {
        let entries = &classes_by_name[name];
        if entries.len() < 2 {
            continue;
        }
        let mut owners: Vec<&str> = entries.clone();
        owners.sort();
        owners.dedup();
        if owners.len() < 2 {
            continue;
        }
        let key = format!("class|{name}|{}", owners.join("|"));
        if let Ok(mut set) = warned.lock() {
            if !set.insert(key) {
                continue;
            }
        }
        eprintln!(
            "warning: class `{}` has {} co-compiled definitions across {} modules; the \
             interpreter resolves class members by NAME across modules, so method bodies \
             from one definition execute against instances of the other — the failure reads \
             as `method not found` or `no field named ...` on a class that has the member. \
             Defined in: {}. Rename one of the classes to a unique name. \
             [compiler_cross_module_private_symbol_collision]",
            name,
            entries.len(),
            owners.len(),
            owners.join(", "),
        );
    }
}

/// Diagnostic: warn when a single `impl` block defines two or more methods that
/// share a bare name but differ in parameter count (arity).
///
/// `warn_duplicate_private_signatures` above used to check only bare top-level
/// free functions, on the documented assumption that "methods are qualified
/// (`Type.method`) and cannot collide". That assumption is false: a real
/// defect (`BeDomNode` with two `static fn element` definitions differing only
/// in arity) showed that same-name methods *within one impl block* collide
/// exactly like the free-function case once dispatch resolves by name — JIT
/// codegen field reads on instances built through the "wrong" arity came back
/// silently empty, while the interpreter was correct. The bug wore four masks
/// (blank pixels, wrong font, unpopulated computed style, unparsed HTML
/// attribute) before the actual cause — two `element` overloads differing
/// only in arity — was found. A 15-line repro reproduces it; renaming one
/// overload fixes it.
///
/// This is a structural AST check over `ImplBlock.methods` (already parsed,
/// impl-block-scoped), not a text/indentation heuristic — it cannot confuse an
/// impl-block-level method with an `extern fn` declared locally inside a
/// method body, because such nested declarations live in the method's `body`
/// statements, never in `ImplBlock.methods`.
///
/// Non-breaking diagnostic only. The fix is to rename one of the colliding
/// overloads to a unique name.
fn warn_method_arity_collisions(module: &Module) {
    for finding in find_method_arity_collisions(module) {
        eprintln!("{}", finding.render());
    }
}

/// Diagnostic: warn when the same `Type.method` key is defined by two or more
/// *different* co-compiled `impl` blocks with differing signatures.
///
/// `find_method_arity_collisions` only looks *inside one* impl block, so the
/// cross-module case — two modules that each write `impl Foo` with a method of the
/// same name — had no detector at all. That key is unique per *type*, not per
/// *module*, so those two definitions land on the same registry slot and clobber
/// each other exactly like the free-function case. This was the method half of the
/// blind spot documented in
/// `doc/08_tracking/bug/diag_stage_facet_cross_module_collision_under_test_2026-07-06.md`.
///
/// Same-arity-but-different-types overloads are included here (the arity check
/// cannot see them). Non-breaking diagnostic only.
fn warn_cross_impl_method_collisions(module: &Module) {
    use std::collections::HashMap;
    use std::sync::{Mutex, OnceLock};

    // (class, method) -> distinct signatures, and how many impl blocks contributed.
    let mut by_key: HashMap<String, Vec<String>> = HashMap::new();
    let mut blocks_for_key: HashMap<String, usize> = HashMap::new();
    for item in &module.items {
        if let Node::Impl(impl_block) = item {
            let class_name = render_target_type(&impl_block.target_type);
            let mut seen_here: HashSet<String> = HashSet::new();
            for method in &impl_block.methods {
                let key = format!("{class_name}.{}", method.name);
                by_key.entry(key.clone()).or_default().push(render_signature(method));
                if seen_here.insert(key.clone()) {
                    *blocks_for_key.entry(key).or_default() += 1;
                }
            }
        }
    }

    static WARNED: OnceLock<Mutex<HashSet<String>>> = OnceLock::new();
    let warned = WARNED.get_or_init(|| Mutex::new(HashSet::new()));

    let mut keys: Vec<&String> = by_key.keys().collect();
    keys.sort();
    for key in keys {
        // Only the cross-impl-block case; same-block overloads are the arity
        // check's territory and would double-report here.
        if blocks_for_key.get(key).copied().unwrap_or(0) < 2 {
            continue;
        }
        let mut distinct: Vec<&String> = by_key[key].iter().collect();
        distinct.sort();
        distinct.dedup();
        if distinct.len() < 2 {
            continue; // identical redefinitions → harmless under last-write-wins
        }
        let sigs = distinct.iter().map(|s| s.as_str()).collect::<Vec<_>>().join(" vs ");
        let dedup_key = format!("{key}|{sigs}");
        if let Ok(mut set) = warned.lock() {
            if !set.insert(dedup_key) {
                continue;
            }
        }
        eprintln!(
            "warning: method `{key}` is defined by {} separate co-compiled impl blocks with \
             {} differing signatures ({sigs}); a `Type.method` key is unique per type, not per \
             module, so these share one last-write-wins registry slot and a call may silently \
             dispatch to the wrong body. Rename the conflicting definition(s) or give the types \
             distinct names. [compiler_cross_module_method_collision]",
            blocks_for_key[key],
            distinct.len(),
        );
    }
}

/// One `impl` block method-name whose definitions disagree on arity.
#[derive(Debug, Clone, PartialEq, Eq)]
struct MethodArityCollision {
    class_name: String,
    method_name: String,
    /// Distinct parameter counts seen for this name, ascending.
    arities: Vec<usize>,
}

impl MethodArityCollision {
    fn render(&self) -> String {
        let arities_text = self
            .arities
            .iter()
            .map(|a| a.to_string())
            .collect::<Vec<_>>()
            .join(" vs ");
        format!(
            "warning: class `{}` defines method `{}` {} times in the same impl block with \
             differing arities ({arities_text} parameters); methods resolve by bare name within \
             an impl block, so JIT dispatch may silently resolve a call to the wrong overload — \
             field reads on instances built through the wrong arity can come back empty/corrupt \
             with no error. Rename the conflicting overload(s) to a unique name. \
             [compiler_impl_block_method_arity_collision]",
            self.class_name,
            self.method_name,
            self.arities.len(),
        )
    }
}

fn render_target_type(ty: &Type) -> String {
    match ty {
        Type::Simple(name) => name.clone(),
        Type::Generic { name, .. } => name.clone(),
        other => format!("{other:?}"),
    }
}

/// Scan every `impl` block in `module` for same-name methods that differ in arity.
/// Pure/testable core of `warn_method_arity_collisions` — see that function's doc
/// comment for the motivating defect and the rationale for checking
/// `ImplBlock.methods` structurally rather than via text scanning.
fn find_method_arity_collisions(module: &Module) -> Vec<MethodArityCollision> {
    let mut findings = Vec::new();
    for item in &module.items {
        if let Node::Impl(impl_block) = item {
            findings.extend(find_method_arity_collisions_in_impl(impl_block));
        }
    }
    findings
}

fn find_method_arity_collisions_in_impl(impl_block: &ImplBlock) -> Vec<MethodArityCollision> {
    use std::collections::HashMap;

    let class_name = render_target_type(&impl_block.target_type);

    // name -> distinct arities seen, in first-seen order.
    let mut arities_by_name: HashMap<&str, Vec<usize>> = HashMap::new();
    for method in &impl_block.methods {
        let arity = method.params.len();
        let seen = arities_by_name.entry(method.name.as_str()).or_default();
        if !seen.contains(&arity) {
            seen.push(arity);
        }
    }

    let mut names: Vec<&str> = arities_by_name.keys().copied().collect();
    names.sort();

    let mut findings = Vec::new();
    for name in names {
        let arities = &arities_by_name[name];
        if arities.len() < 2 {
            continue; // only one arity present -> not the collision this check targets
        }
        let mut sorted_arities = arities.clone();
        sorted_arities.sort_unstable();
        findings.push(MethodArityCollision {
            class_name: class_name.clone(),
            method_name: name.to_string(),
            arities: sorted_arities,
        });
    }
    findings
}

/// Load module with imports and validate imported function effects against capabilities.
///
/// If `importing_capabilities` is Some, validates that imported functions have effects
/// compatible with the importing module's capabilities.
pub fn load_module_with_imports_validated(
    path: &Path,
    visited: &mut HashSet<PathBuf>,
    importing_capabilities: Option<&[Capability]>,
) -> Result<Module, CompileError> {
    load_module_with_imports_internal(
        path,
        visited,
        importing_capabilities,
        true,
        simple_common::target::TargetArch::host(),
    )
}

/// Collect resolved imported module file paths in dependency-first order.
///
/// This is used by SMF execution paths that must preload imported modules before
/// loading the entry artifact. The returned paths exclude the entry file itself.
pub fn collect_imported_module_paths(path: &Path) -> Result<Vec<PathBuf>, CompileError> {
    let mut visited = HashSet::new();
    let mut collected = Vec::new();
    collect_imported_module_paths_internal(path, &mut visited, &mut collected)?;
    Ok(collected)
}

pub fn collect_direct_imported_module_paths(path: &Path) -> Result<Vec<PathBuf>, CompileError> {
    let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    let mut source = fs::read_to_string(&path).map_err(|e| CompileError::Io(format!("Cannot read {:?}: {e}", path)))?;
    if source.contains('\r') {
        source = source.replace('\r', "");
    }

    source =
        crate::pipeline::cfg_strip::strip_inactive_cfg_arch_globals(&source, simple_common::target::TargetArch::host());
    let mut parser = simple_parser::Parser::new(&source);
    let mut module = parser
        .parse()
        .map_err(|e| CompileError::Parse(format!("in {:?}: {e}", path)))?;
    crate::pipeline::cfg_strip::strip_inactive_cfg_arch_fns_for_host(&mut module);
    display_parser_hints(&parser, &source, &path);

    let base_dir = path.parent().unwrap_or(Path::new("."));
    let mut collected = Vec::new();

    for item in module.items {
        match item {
            Node::UseStmt(use_stmt) => {
                collect_use_stmt_direct_paths(&use_stmt, base_dir, &mut collected)?;
            }
            Node::ExportUseStmt(export_use) => {
                if export_use.path.segments.is_empty() {
                    continue;
                }
                let temp_use = UseStmt {
                    span: export_use.span,
                    path: export_use.path,
                    target: export_use.target,
                    is_type_only: false,
                    is_lazy: false,
                };
                collect_use_stmt_direct_paths(&temp_use, base_dir, &mut collected)?;
            }
            _ => {}
        }
    }

    Ok(collected)
}

fn collect_imported_module_paths_internal(
    path: &Path,
    visited: &mut HashSet<PathBuf>,
    collected: &mut Vec<PathBuf>,
) -> Result<(), CompileError> {
    let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    if !visited.insert(path.clone()) {
        return Ok(());
    }

    let mut source = fs::read_to_string(&path).map_err(|e| CompileError::Io(format!("Cannot read {:?}: {e}", path)))?;
    if source.contains('\r') {
        source = source.replace('\r', "");
    }

    source =
        crate::pipeline::cfg_strip::strip_inactive_cfg_arch_globals(&source, simple_common::target::TargetArch::host());
    let mut parser = simple_parser::Parser::new(&source);
    let mut module = parser
        .parse()
        .map_err(|e| CompileError::Parse(format!("in {:?}: {e}", path)))?;
    crate::pipeline::cfg_strip::strip_inactive_cfg_arch_fns_for_host(&mut module);
    display_parser_hints(&parser, &source, &path);

    let base_dir = path.parent().unwrap_or(Path::new("."));

    for item in module.items {
        match item {
            Node::UseStmt(use_stmt) => {
                collect_use_stmt_paths(&use_stmt, base_dir, visited, collected)?;
            }
            Node::ExportUseStmt(export_use) => {
                if export_use.path.segments.is_empty() {
                    continue;
                }
                let temp_use = UseStmt {
                    span: export_use.span,
                    path: export_use.path,
                    target: export_use.target,
                    is_type_only: false,
                    is_lazy: false,
                };
                collect_use_stmt_paths(&temp_use, base_dir, visited, collected)?;
            }
            _ => {}
        }
    }

    Ok(())
}

fn collect_use_stmt_paths(
    use_stmt: &UseStmt,
    base_dir: &Path,
    visited: &mut HashSet<PathBuf>,
    collected: &mut Vec<PathBuf>,
) -> Result<(), CompileError> {
    let Some(resolved) = resolve_use_to_path(use_stmt, base_dir) else {
        return Ok(());
    };

    let mut preload_path = resolved.clone();
    if let Some(package_module) = sibling_package_module_path(&resolved) {
        preload_path = package_module;
    }

    collect_imported_module_paths_internal(&preload_path, visited, collected)?;
    if !collected.contains(&preload_path) {
        collected.push(preload_path.clone());
    }

    if resolved.file_name().is_some_and(|name| name == "__init__.spl") {
        for sibling in collect_matching_package_sibling_paths(&resolved, use_stmt)? {
            collect_imported_module_paths_internal(&sibling, visited, collected)?;
            if !collected.contains(&sibling) {
                collected.push(sibling);
            }
        }
    }

    Ok(())
}

fn collect_use_stmt_direct_paths(
    use_stmt: &UseStmt,
    base_dir: &Path,
    collected: &mut Vec<PathBuf>,
) -> Result<(), CompileError> {
    let Some(resolved) = resolve_use_to_path(use_stmt, base_dir) else {
        return Ok(());
    };

    let mut preload_path = resolved.clone();
    if let Some(package_module) = sibling_package_module_path(&resolved) {
        preload_path = package_module;
    }

    if !collected.contains(&preload_path) {
        collected.push(preload_path);
    }

    if resolved.file_name().is_some_and(|name| name == "__init__.spl") {
        for sibling in collect_matching_package_sibling_paths(&resolved, use_stmt)? {
            if !collected.contains(&sibling) {
                collected.push(sibling);
            }
        }
    }

    Ok(())
}

fn sibling_package_module_path(resolved: &Path) -> Option<PathBuf> {
    if resolved.file_name().is_none_or(|name| name != "__init__.spl") {
        return None;
    }
    let package_dir = resolved.parent()?;
    let package_name = package_dir.file_name()?.to_str()?;
    let candidate = package_dir.with_file_name(format!("{package_name}.spl"));
    if candidate.exists() && candidate.is_file() {
        Some(candidate)
    } else {
        None
    }
}

fn collect_matching_package_sibling_paths(
    package_init_path: &Path,
    use_stmt: &UseStmt,
) -> Result<Vec<PathBuf>, CompileError> {
    let Some(package_dir) = package_init_path.parent() else {
        return Ok(Vec::new());
    };

    let mut requested_names = Vec::new();
    requested_import_names(&use_stmt.target, &mut requested_names);

    let mut sibling_files: Vec<PathBuf> = match fs::read_dir(package_dir) {
        Ok(entries) => entries
            .filter_map(|entry| entry.ok().map(|e| e.path()))
            .filter(|path| {
                path.extension().is_some_and(|ext| ext == "spl")
                    && path
                        .file_name()
                        .is_some_and(|name| name != "__init__.spl" && name != "mod_stub.spl")
                    && path.is_file()
                    && file_might_define_requested_symbol(path, &requested_names)
            })
            .collect(),
        Err(e) => {
            return Err(CompileError::Io(format!(
                "Cannot read package directory {:?}: {}",
                package_dir, e
            )))
        }
    };

    sibling_files.sort();
    Ok(sibling_files)
}

fn load_module_with_imports_internal(
    path: &Path,
    visited: &mut HashSet<PathBuf>,
    importing_capabilities: Option<&[Capability]>,
    flatten_imports: bool,
    target_arch: simple_common::target::TargetArch,
) -> Result<Module, CompileError> {
    let path = path.canonicalize().unwrap_or_else(|_| path.to_path_buf());
    if flatten_imports && !visited.insert(path.clone()) {
        return Ok(Module {
            name: None,
            items: Vec::new(),
        });
    }

    let mut source = fs::read_to_string(&path).map_err(|e| CompileError::Io(format!("Cannot read {:?}: {e}", path)))?;
    // Normalize CRLF → LF so indentation-sensitive parsing works on all platforms
    if source.contains('\r') {
        source = source.replace('\r', "");
    }

    // Bootstrap leniency: older sources use optional `text?` types which the
    // current parser treats as a bare identifier. During early bootstrap we
    // normalize them to `text` so type checking succeeds. Guarded by env to
    // avoid affecting normal builds.
    //
    // FALLBACK-ONLY (2026-07-30): the normalization is TEXTUAL — its
    // `strip_optionals` step deletes `?` before whitespace/delimiters, which
    // also deleted every try-operator from VALID modern sources
    // (`val h = f(x)?` matches the `"?\n"` pattern), silently turning `?`
    // into a no-op whenever SIMPLE_BOOTSTRAP=1 was set. That env var is
    // routinely set just to suppress the seed banner, so the corruption was
    // widespread and engine-independent (the JIT then did arithmetic on the
    // un-unwrapped enum pointer; the interpreter mis-typed it). Parse the
    // pristine source FIRST and only fall back to the legacy normalization
    // when the pristine parse fails — a source that parses cleanly is never
    // rewritten.
    source = crate::pipeline::cfg_strip::strip_inactive_cfg_arch_globals(&source, target_arch);
    if std::env::var("SIMPLE_BOOTSTRAP").as_deref() == Ok("1") {
        // Probe-parse the pristine source (throwaway parser); only a source
        // the current parser genuinely cannot handle gets the legacy
        // rewrite. The extra parse only happens in bootstrap mode.
        if simple_parser::Parser::new(&source).parse().is_err() {
            let mut lenient = source.replace("text?", "text");
            lenient = strip_optionals(lenient);
            source = lenient;
        }
    }
    let mut parser = simple_parser::Parser::new(&source);
    let mut module = parser
        .parse()
        .map_err(|e| CompileError::Parse(format!("in {:?}: {e}", path)))?;
    crate::pipeline::cfg_strip::strip_inactive_cfg_arch_fns(&mut module, target_arch);

    // Display error hints (warnings, etc.) from parser
    display_parser_hints(&parser, &source, &path);

    // Auto-import std.shell.* for .shs files
    if path.extension().and_then(|e| e.to_str()) == Some("shs") {
        use simple_parser::ast::{UseStmt, ModulePath, ImportTarget};
        use simple_parser::token::Span;
        let shell_import = Node::UseStmt(UseStmt {
            span: Span::new(0, 0, 0, 0),
            path: ModulePath::new(vec!["std".to_string(), "shell".to_string()]),
            target: ImportTarget::Glob,
            is_type_only: false,
            is_lazy: false,
        });
        module.items.insert(0, shell_import);
    }

    // Extract this module's capabilities for passing to child imports
    let this_caps = extract_module_capabilities(&module);
    let effective_caps = importing_capabilities.or(this_caps.as_deref()).unwrap_or(&[]);

    let mut items = Vec::new();
    for item in module.items {
        if let Node::UseStmt(use_stmt) = &item {
            if let Some(resolved) = resolve_use_to_path(use_stmt, path.parent().unwrap_or(Path::new("."))) {
                if flatten_imports {
                    let flatten_this_import = should_flatten_nested_import(use_stmt, &source)
                        || single_import_targets_module_file(&use_stmt.target, &resolved);
                    let mut imported = load_module_with_imports_internal(
                        &resolved,
                        visited,
                        Some(effective_caps),
                        flatten_this_import,
                        target_arch,
                    )?;
                    if flatten_this_import && resolved.file_name().is_some_and(|name| name == "__init__.spl") {
                        imported.items.extend(load_matching_package_siblings(
                            &resolved,
                            use_stmt,
                            visited,
                            Some(effective_caps),
                            target_arch,
                        )?);
                    }

                    // Validate imported functions against our capabilities
                    if !effective_caps.is_empty() {
                        let func_effects = extract_function_effects(&imported);
                        for (func_name, effects) in func_effects {
                            if let Some(err) = check_import_compatibility(&func_name, &effects, effective_caps) {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::UNSUPPORTED_FEATURE)
                                    .with_help(format!(
                                        "Function `{}` uses effects not allowed by module capabilities",
                                        func_name
                                    ));
                                return Err(CompileError::semantic_with_context(err, ctx));
                            }
                        }
                    }

                    // Add imported items for flattened access (functions/classes in global scope)
                    if flatten_this_import {
                        items.extend(strip_flattened_import_nodes(imported, &resolved).items);
                    }
                }
                // ALSO keep the UseStmt so evaluate_module can create the module binding
                // The module exports cache prevents redundant re-parsing
                items.push(item);
                continue;
            }
        } else if let Node::ExportUseStmt(export_use) = &item {
            // Handle export use statements (e.g., `export describe, context from dsl`)
            // Skip bare exports (empty path) - they only mark local symbols for export
            if export_use.path.segments.is_empty() {
                items.push(item);
                continue;
            }
            let temp_use = UseStmt {
                span: export_use.span,
                path: export_use.path.clone(),
                target: export_use.target.clone(),
                is_type_only: false,
                is_lazy: false,
            };
            if let Some(resolved) = resolve_use_to_path(&temp_use, path.parent().unwrap_or(Path::new("."))) {
                if flatten_imports {
                    let flatten_this_import = should_flatten_nested_import(&temp_use, &source);
                    let mut imported = load_module_with_imports_internal(
                        &resolved,
                        visited,
                        Some(effective_caps),
                        flatten_this_import,
                        target_arch,
                    )?;
                    if flatten_this_import && resolved.file_name().is_some_and(|name| name == "__init__.spl") {
                        imported.items.extend(load_matching_package_siblings(
                            &resolved,
                            &temp_use,
                            visited,
                            Some(effective_caps),
                            target_arch,
                        )?);
                    }

                    if !effective_caps.is_empty() {
                        let func_effects = extract_function_effects(&imported);
                        for (func_name, effects) in func_effects {
                            if let Some(err) = check_import_compatibility(&func_name, &effects, effective_caps) {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::UNSUPPORTED_FEATURE)
                                    .with_help(format!(
                                        "Function `{}` uses effects not allowed by module capabilities",
                                        func_name
                                    ));
                                return Err(CompileError::semantic_with_context(err, ctx));
                            }
                        }
                    }

                    if flatten_this_import {
                        items.extend(strip_flattened_import_nodes(imported, &resolved).items);
                    }
                }
                items.push(item);
                continue;
            }
        } else if let Node::CommonUseStmt(common_use) = &item {
            // Handle common use statements
            let temp_use = UseStmt {
                span: common_use.span,
                path: common_use.path.clone(),
                target: common_use.target.clone(),
                is_type_only: false,
                is_lazy: false,
            };
            if let Some(resolved) = resolve_use_to_path(&temp_use, path.parent().unwrap_or(Path::new("."))) {
                if flatten_imports {
                    let flatten_this_import = should_flatten_nested_import(&temp_use, &source);
                    let mut imported = load_module_with_imports_internal(
                        &resolved,
                        visited,
                        Some(effective_caps),
                        flatten_this_import,
                        target_arch,
                    )?;
                    if flatten_this_import && resolved.file_name().is_some_and(|name| name == "__init__.spl") {
                        imported.items.extend(load_matching_package_siblings(
                            &resolved,
                            &temp_use,
                            visited,
                            Some(effective_caps),
                            target_arch,
                        )?);
                    }

                    if !effective_caps.is_empty() {
                        let func_effects = extract_function_effects(&imported);
                        for (func_name, effects) in func_effects {
                            if let Some(err) = check_import_compatibility(&func_name, &effects, effective_caps) {
                                let ctx = ErrorContext::new()
                                    .with_code(codes::UNSUPPORTED_FEATURE)
                                    .with_help(format!(
                                        "Function `{}` uses effects not allowed by module capabilities",
                                        func_name
                                    ));
                                return Err(CompileError::semantic_with_context(err, ctx));
                            }
                        }
                    }

                    if flatten_this_import {
                        items.extend(strip_flattened_import_nodes(imported, &resolved).items);
                    }
                }
                items.push(item);
                continue;
            }
        } else if let Node::MultiUse(multi_use) = &item {
            // Handle comma-separated imports: use a.B, c.D
            for (module_path, target) in &multi_use.imports {
                // Create a temporary UseStmt to reuse the resolution logic
                let temp_use = UseStmt {
                    span: multi_use.span,
                    path: module_path.clone(),
                    target: target.clone(),
                    is_type_only: multi_use.is_type_only,
                    is_lazy: false,
                };
                if let Some(resolved) = resolve_use_to_path(&temp_use, path.parent().unwrap_or(Path::new("."))) {
                    if flatten_imports {
                        let flatten_this_import = should_flatten_nested_import(&temp_use, &source);
                        let mut imported = load_module_with_imports_internal(
                            &resolved,
                            visited,
                            Some(effective_caps),
                            flatten_this_import,
                            target_arch,
                        )?;
                        if flatten_this_import && resolved.file_name().is_some_and(|name| name == "__init__.spl") {
                            imported.items.extend(load_matching_package_siblings(
                                &resolved,
                                &temp_use,
                                visited,
                                Some(effective_caps),
                                target_arch,
                            )?);
                        }

                        // Validate imported functions against our capabilities
                        if !effective_caps.is_empty() {
                            let func_effects = extract_function_effects(&imported);
                            for (func_name, effects) in func_effects {
                                if let Some(err) = check_import_compatibility(&func_name, &effects, effective_caps) {
                                    let ctx =
                                        ErrorContext::new()
                                            .with_code(codes::UNSUPPORTED_FEATURE)
                                            .with_help(format!(
                                                "Function `{}` uses effects not allowed by module capabilities",
                                                func_name
                                            ));
                                    return Err(CompileError::semantic_with_context(err, ctx));
                                }
                            }
                        }

                        // Add imported items for flattened access
                        if flatten_this_import {
                            items.extend(strip_flattened_import_nodes(imported, &resolved).items);
                        }
                    }
                }
            }
            // Keep the MultiUse so evaluate_module can create the module binding
            items.push(item);
            continue;
        }
        items.push(item);
    }

    Ok(Module {
        name: module.name,
        items,
    })
}

/// Resolve a simple `use` path to a sibling `.spl` file.
/// Also checks stdlib location if sibling resolution fails.
fn resolve_use_to_path(use_stmt: &UseStmt, base: &Path) -> Option<PathBuf> {
    let mut parts: Vec<String> = use_stmt
        .path
        .segments
        .iter()
        .filter(|s| s.as_str() != "crate" && s.as_str() != "self" && s.as_str() != ".")
        .cloned()
        .collect();

    // Reject deprecated `std.ffi` — must use `std.sffi` instead
    if parts.len() >= 2 && parts[0] == "std" && parts[1] == "ffi" {
        eprintln!("\x1b[31merror\x1b[0m: `use std.ffi` is deprecated — use `use std.sffi` instead");
        eprintln!(
            "  hint: rename `std.ffi.{}` → `std.sffi.{}`",
            parts[2..].join("."),
            parts[2..].join(".")
        );
        if std::env::var("SIMPLE_STRICT_SFFI").is_ok() {
            std::process::exit(1);
        }
        parts[1] = "sffi".to_string();
    }

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

    let resolve_parts = |parts: &[String]| {
        if let Some(resolved) = resolve_parts_with_search_roots(base, parts, use_stmt) {
            return Some(resolved);
        }

        if let Some(type_parts) = normalize_type_parts(parts) {
            if let Some(resolved) = resolve_parts_with_search_roots(base, &type_parts, use_stmt) {
                return Some(resolved);
            }
        }

        let mut current = base.to_path_buf();
        for _ in 0..10 {
            if let Some(resolved) = resolve_from_stdlib_root(&current, parts, use_stmt) {
                return Some(resolved);
            }
            // Never climb out of the enclosing repository.
            if is_workspace_boundary(&current) {
                break;
            }
            let Some(parent) = current.parent() else {
                break;
            };
            current = parent.to_path_buf();
        }

        let manifest_root = Path::new(env!("CARGO_MANIFEST_DIR"));
        let repo_root = manifest_root.join("..").join("..").join("..");
        for fallback_root in [
            repo_root,
            manifest_root.join("..").join(".."),
            manifest_root.join(".."),
            manifest_root.to_path_buf(),
            std::env::current_dir().unwrap_or_else(|_| PathBuf::from(".")),
        ] {
            if let Some(resolved) = resolve_from_stdlib_root(&fallback_root, parts, use_stmt) {
                return Some(resolved);
            }
        }

        None
    };

    if let Some(resolved) = resolve_parts(&parts) {
        return Some(resolved);
    }

    if matches!(use_stmt.target, ImportTarget::Single(_) | ImportTarget::Aliased { .. }) {
        parts.pop();
        return resolve_parts(&parts);
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_simd::{host_cpu_config, reset_host_cpu_config_cache_for_tests, HostCpuConfig, SimdTier};
    use simple_parser::ast::{ExportUseStmt, ImportTarget, ModulePath, UseStmt};
    use simple_parser::token::Span;
    use std::collections::HashSet;
    use std::path::Path;
    use std::sync::{Mutex, OnceLock};

    #[test]
    fn flattened_export_use_emits_global_binding_markers_for_reexport_facades() {
        let temp = tempfile::tempdir().unwrap();
        let facade_path = temp.path().join("facade.spl");
        let leaf_path = temp.path().join("leaf.spl");
        fs::write(&leaf_path, "var value: i32 = 0\n").unwrap();

        let span = Span::new(0, 0, 0, 0);
        let module = Module {
            name: None,
            items: vec![
                Node::ExportUseStmt(ExportUseStmt {
                    span,
                    path: ModulePath::new(vec!["leaf".to_string()]),
                    target: ImportTarget::Group(vec![
                        ImportTarget::Single("value".to_string()),
                        ImportTarget::Aliased {
                            name: "other_value".to_string(),
                            alias: "aliased_value".to_string(),
                        },
                    ]),
                }),
                Node::ExportUseStmt(ExportUseStmt {
                    span,
                    path: ModulePath::new(vec!["leaf".to_string()]),
                    target: ImportTarget::Glob,
                }),
                Node::ExportUseStmt(ExportUseStmt {
                    span,
                    path: ModulePath::new(vec![]),
                    target: ImportTarget::Single("bare_value".to_string()),
                }),
            ],
        };

        let flattened = strip_flattened_import_nodes(module, &facade_path);
        let importer = normalize_path_key(&facade_path).to_string_lossy().into_owned();
        let source = normalize_path_key(&leaf_path).to_string_lossy().into_owned();
        let marker_names: Vec<String> = flattened
            .items
            .iter()
            .filter_map(|item| match item {
                Node::Const(marker) if marker.name.starts_with(FLATTEN_IMPORT_BINDING_MARKER_PREFIX) => {
                    Some(marker.name.clone())
                }
                _ => None,
            })
            .collect();

        assert!(marker_names.contains(&import_binding_marker_name(&importer, "value", &source, "value")));
        assert!(marker_names.contains(&import_binding_marker_name(
            &importer,
            "aliased_value",
            &source,
            "other_value"
        )));
        assert!(marker_names.contains(&import_binding_marker_name(&importer, "*", &source, "*")));
        assert!(!marker_names.iter().any(|marker| marker.contains("bare_value")));
        assert!(!flattened
            .items
            .iter()
            .any(|item| matches!(item, Node::ExportUseStmt(_))));
    }

    fn simd_tier_env_lock() -> &'static Mutex<()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
    }

    fn with_simd_envs<T>(simd_tier: Option<&str>, cpu_config_path: Option<&Path>, f: impl FnOnce() -> T) -> T {
        let _guard = simd_tier_env_lock().lock().unwrap();
        let previous_simd_tier = std::env::var("SIMPLE_SIMD_TIER").ok();
        let previous_cpu_config_path = std::env::var("SIMPLE_CPU_CONFIG_PATH").ok();

        match simd_tier {
            Some(value) => std::env::set_var("SIMPLE_SIMD_TIER", value),
            None => std::env::remove_var("SIMPLE_SIMD_TIER"),
        }

        match cpu_config_path {
            Some(path) => std::env::set_var("SIMPLE_CPU_CONFIG_PATH", path),
            None => std::env::remove_var("SIMPLE_CPU_CONFIG_PATH"),
        }

        reset_host_cpu_config_cache_for_tests();
        let result = f();
        reset_host_cpu_config_cache_for_tests();

        match previous_simd_tier.as_deref() {
            Some(value) => std::env::set_var("SIMPLE_SIMD_TIER", value),
            None => std::env::remove_var("SIMPLE_SIMD_TIER"),
        }

        match previous_cpu_config_path.as_deref() {
            Some(value) => std::env::set_var("SIMPLE_CPU_CONFIG_PATH", value),
            None => std::env::remove_var("SIMPLE_CPU_CONFIG_PATH"),
        }

        reset_host_cpu_config_cache_for_tests();
        result
    }

    fn render_string_list(values: &[String]) -> String {
        format!(
            "[{}]",
            values
                .iter()
                .map(|value| format!("\"{value}\""))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    fn render_tier_list(values: &[SimdTier]) -> String {
        format!(
            "[{}]",
            values
                .iter()
                .map(|value| format!("\"{}\"", value.as_str()))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    fn instruction_sets_for_tier(tier: SimdTier) -> &'static [&'static str] {
        match tier {
            SimdTier::Scalar => &[],
            SimdTier::X86_64Sse2 => &["sse2"],
            SimdTier::X86_64Avx2 => &["sse2", "avx2"],
            SimdTier::X86_64Avx512 => &["sse2", "avx2", "avx512f"],
            SimdTier::Aarch64Neon => &["neon"],
            SimdTier::Aarch64Sve => &["neon", "sve"],
            SimdTier::Aarch64Sve2 => &["neon", "sve", "sve2"],
            SimdTier::Riscv64Rvv => &["rvv"],
            SimdTier::Wasm128 => &["wasm128"],
        }
    }

    fn config_document(base: &HostCpuConfig, enabled_tier: SimdTier) -> String {
        let enabled_instruction_sets = instruction_sets_for_tier(enabled_tier)
            .iter()
            .filter(|instruction_set| {
                base.simple_support
                    .instruction_sets
                    .iter()
                    .any(|supported| supported == **instruction_set)
            })
            .map(|instruction_set| (*instruction_set).to_string())
            .collect::<Vec<_>>();

        format!(
            concat!(
                "version: 1\n",
                "target_triple: \"{}\"\n",
                "generated_by: \"test\"\n",
                "support:\n",
                "    simd_tier: \"{}\"\n",
                "    instruction_sets: {}\n",
                "simple_support:\n",
                "    simd_tier_fallbacks: {}\n",
                "    instruction_sets: {}\n",
                "enabled:\n",
                "    simd_tier: \"{}\"\n",
                "    instruction_sets: {}\n"
            ),
            base.target_triple,
            base.support.simd_tier.as_str(),
            render_string_list(&base.support.instruction_sets),
            render_tier_list(&base.simple_support.simd_tier_fallbacks),
            render_string_list(&base.simple_support.instruction_sets),
            enabled_tier.as_str(),
            render_string_list(&enabled_instruction_sets),
        )
    }

    #[test]
    fn test_startup_app_type_parsing() {
        assert_eq!(StartupAppType::from_str("cli"), Some(StartupAppType::Cli));
        assert_eq!(StartupAppType::from_str("tui"), Some(StartupAppType::Tui));
        assert_eq!(StartupAppType::from_str("gui"), Some(StartupAppType::Gui));
        assert_eq!(StartupAppType::from_str("service"), Some(StartupAppType::Service));
        assert_eq!(StartupAppType::from_str("repl"), Some(StartupAppType::Repl));
        assert_eq!(StartupAppType::from_str("GUI"), Some(StartupAppType::Gui)); // Case insensitive
        assert_eq!(StartupAppType::from_str("invalid"), None);
    }

    #[test]
    fn test_startup_app_type_to_smf_byte() {
        assert_eq!(StartupAppType::Cli.to_smf_byte(), 0);
        assert_eq!(StartupAppType::Tui.to_smf_byte(), 1);
        assert_eq!(StartupAppType::Gui.to_smf_byte(), 2);
        assert_eq!(StartupAppType::Service.to_smf_byte(), 3);
        assert_eq!(StartupAppType::Repl.to_smf_byte(), 4);
    }

    #[test]
    fn test_startup_window_hints_default() {
        let hints = StartupWindowHints::default();
        assert_eq!(hints.width, 1280);
        assert_eq!(hints.height, 720);
        assert_eq!(hints.title, "Simple Application");
    }

    #[test]
    fn test_startup_config_default() {
        let config = StartupConfig::default();
        assert_eq!(config.app_type, StartupAppType::Cli);
        assert!(!config.has_app_type);
        assert!(!config.has_window_hints);
    }

    fn use_stmt(path: &[&str], target: ImportTarget) -> UseStmt {
        UseStmt {
            span: Span::new(0, 0, 0, 0),
            path: ModulePath::new(path.iter().map(|s| s.to_string()).collect()),
            target,
            is_type_only: false,
            is_lazy: false,
        }
    }

    #[test]
    fn resolves_std_io_to_package_init_from_src_lib() {
        let resolved = resolve_use_to_path(
            &use_stmt(
                &["std", "io"],
                ImportTarget::Group(vec![ImportTarget::Single("env_get".to_string())]),
            ),
            Path::new("src/lib/nogc_sync_mut/test_runner"),
        )
        .unwrap();

        assert!(resolved.ends_with("src/lib/nogc_sync_mut/io/__init__.spl"));
    }

    #[test]
    fn resolve_use_to_path_uses_configured_variant_stdlib_root_without_override() {
        let temp = tempfile::tempdir().unwrap();
        let project_root = temp.path();
        let base_dir = project_root.join("src/app");
        let scalar_config = project_root.join("scalar_cpu_config.sdn");
        let variant_config = project_root.join("variant_cpu_config.sdn");
        let base = with_simd_envs(None, Some(&scalar_config), || host_cpu_config().unwrap());
        let Some(variant_tier) = base
            .simple_support
            .simd_tier_fallbacks
            .iter()
            .copied()
            .find(|tier| !tier.is_scalar())
        else {
            return;
        };
        let variant_name = variant_tier.as_str();
        fs::create_dir_all(&base_dir).unwrap();
        fs::create_dir_all(project_root.join("src/lib/std/src/io")).unwrap();
        fs::create_dir_all(project_root.join(format!("src/lib/std/variants/{variant_name}/src/io"))).unwrap();
        fs::write(project_root.join("src/lib/std/src/io/__init__.spl"), "export scalar\n").unwrap();
        fs::write(
            project_root.join(format!("src/lib/std/variants/{variant_name}/src/io/__init__.spl")),
            "export sse2\n",
        )
        .unwrap();
        fs::write(&scalar_config, config_document(&base, SimdTier::Scalar)).unwrap();
        fs::write(&variant_config, config_document(&base, variant_tier)).unwrap();

        let use_stmt = use_stmt(
            &["std", "io"],
            ImportTarget::Group(vec![ImportTarget::Single("env_get".to_string())]),
        );

        let scalar = with_simd_envs(None, Some(&scalar_config), || {
            resolve_use_to_path(&use_stmt, &base_dir).unwrap()
        });
        let variant = with_simd_envs(None, Some(&variant_config), || {
            resolve_use_to_path(&use_stmt, &base_dir).unwrap()
        });

        assert_eq!(scalar, project_root.join("src/lib/std/src/io/__init__.spl"));
        assert_eq!(
            variant,
            project_root.join(format!("src/lib/std/variants/{variant_name}/src/io/__init__.spl"))
        );
    }

    #[test]
    fn flattens_std_io_group_imports_into_module_items() {
        let temp = tempfile::tempdir().unwrap();
        let entry = temp.path().join("main.spl");
        fs::write(
            &entry,
            "use std.io.{env_get}\nfn main() -> int:\n    env_get(\"HOME\").len()\n",
        )
        .unwrap();

        let loaded = load_module_with_imports(&entry, &mut HashSet::new()).unwrap();
        let has_env_get = loaded
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(func) if func.name == "env_get"));

        assert!(has_env_get);
    }

    #[test]
    fn resolves_dotted_backend_imports_from_source_tree() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        let app_ui = src.join("app").join("ui");
        let app_ui_web = src.join("app").join("ui.web");
        fs::create_dir_all(&app_ui).unwrap();
        fs::create_dir_all(&app_ui_web).unwrap();

        let entry = src.join("main.spl");
        fs::write(
            &entry,
            "use app.ui.web.server.{run_web}\nfn main() -> int:\n    run_web()\n",
        )
        .unwrap();
        fs::write(app_ui.join("__init__.spl"), "mod ui\n").unwrap();
        fs::write(app_ui_web.join("server.spl"), "fn run_web() -> int:\n    0\n").unwrap();

        let loaded = load_module_with_imports(&entry, &mut HashSet::new()).unwrap();
        let has_run_web = loaded
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(func) if func.name == "run_web"));

        assert!(has_run_web);
    }

    #[test]
    fn flat_ast_bridge_parser_group_import_keeps_parser_body() {
        let entry = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("..")
            .join("..")
            .join("src")
            .join("compiler")
            .join("10.frontend")
            .join("_FlatAstBridge")
            .join("module_assembly.spl")
            .canonicalize()
            .unwrap();
        let parser_use = use_stmt(
            &["compiler", "core", "parser"],
            ImportTarget::Group(vec![ImportTarget::Single("parser_init_with_path".to_string())]),
        );
        let resolved = resolve_use_to_path(&parser_use, entry.parent().unwrap()).unwrap();

        assert!(resolved.ends_with("src/compiler/10.frontend/core/parser.spl"));

        let loaded = load_module_with_imports(&entry, &mut HashSet::new()).unwrap();
        let has_parser_init = loaded
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(func) if func.name == "parser_init_with_path"));

        assert!(has_parser_init);
    }

    #[test]
    fn compiler_blocks_nested_layer_import_resolves_to_blocks_child_dir() {
        let registry = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("..")
            .join("..")
            .join("src")
            .join("compiler")
            .join("15.blocks")
            .join("blocks")
            .join("registry.spl")
            .canonicalize()
            .unwrap();
        let use_stmt = use_stmt(
            &["compiler", "blocks", "builtin_blocks_math"],
            ImportTarget::Group(vec![ImportTarget::Single("MathBlockDef".to_string())]),
        );
        let resolved = resolve_use_to_path(&use_stmt, registry.parent().unwrap()).unwrap();

        assert!(
            resolved.ends_with("compiler/blocks/blocks/builtin_blocks_math.spl")
                || resolved.ends_with("compiler/15.blocks/blocks/builtin_blocks_math.spl"),
            "resolved to {}",
            resolved.display()
        );
    }

    #[test]
    fn resolves_dotted_backend_imports_from_examples_tree_via_src_root() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        let examples = temp.path().join("examples").join("ui");
        let app_ui = src.join("app").join("ui");
        let app_ui_web = src.join("app").join("ui.web");
        fs::create_dir_all(&examples).unwrap();
        fs::create_dir_all(&app_ui).unwrap();
        fs::create_dir_all(&app_ui_web).unwrap();

        let entry = examples.join("hello_web.spl");
        fs::write(
            &entry,
            "use app.ui.web.server.{run_web}\nfn main() -> int:\n    run_web()\n",
        )
        .unwrap();
        fs::write(app_ui.join("__init__.spl"), "mod ui\n").unwrap();
        fs::write(app_ui_web.join("server.spl"), "fn run_web() -> int:\n    0\n").unwrap();

        let loaded = load_module_with_imports(&entry, &mut HashSet::new()).unwrap();
        let has_run_web = loaded
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(func) if func.name == "run_web"));

        assert!(has_run_web);
    }

    #[test]
    fn resolves_numbered_stdlib_imports_from_examples_tree() {
        let temp = tempfile::tempdir().unwrap();
        let examples = temp.path().join("examples").join("ide");
        let backend = temp.path().join("src").join("lib").join("editor").join("70.backend");
        fs::create_dir_all(&examples).unwrap();
        fs::create_dir_all(&backend).unwrap();

        let entry = examples.join("main.spl");
        fs::write(
            &entry,
            "use std.editor.backend.helper.*\nfn main() -> text:\n    probe_text()\n",
        )
        .unwrap();
        fs::write(backend.join("helper.spl"), "fn probe_text() -> text:\n    \"ok\"\n").unwrap();

        let loaded = load_module_with_imports(&entry, &mut HashSet::new()).unwrap();
        let has_probe_text = loaded
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(func) if func.name == "probe_text"));

        assert!(has_probe_text);
    }

    #[test]
    fn resolves_bare_type_imports_from_project_type_root() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        let nested = src.join("app");
        let type_dir = temp.path().join("src").join("type").join("simple_lang");
        fs::create_dir_all(&nested).unwrap();
        fs::create_dir_all(&type_dir).unwrap();
        fs::write(type_dir.join("I64.spl"), "type I64 = i64\nexport I64\n").unwrap();

        let resolved = resolve_use_to_path(&use_stmt(&["I64"], ImportTarget::Glob), &nested).unwrap();

        assert_eq!(resolved, type_dir.join("I64.spl"));
    }

    #[test]
    fn resolves_owned_domain_type_imports_from_project_type_root() {
        let temp = tempfile::tempdir().unwrap();
        let src = temp.path().join("src");
        let nested = src.join("app");
        let type_dir = temp.path().join("src").join("type").join("simple_lang");
        fs::create_dir_all(&nested).unwrap();
        fs::create_dir_all(&type_dir).unwrap();
        fs::write(type_dir.join("I64.spl"), "type I64 = i64\nexport I64\n").unwrap();

        let resolved = resolve_use_to_path(&use_stmt(&["simple-lang", "I64"], ImportTarget::Glob), &nested).unwrap();

        assert_eq!(resolved, type_dir.join("I64.spl"));
    }

    #[test]
    fn nested_whole_module_imports_are_not_flattened_into_group_imports() {
        let temp = tempfile::tempdir().unwrap();
        let entry = temp.path().join("main.spl");
        let wrapper = temp.path().join("wrapper.spl");
        let helper = temp.path().join("helper.spl");

        fs::write(
            &entry,
            "use wrapper.{run}\nfn main() -> int:\n    print(\"ok\")\n    0\n",
        )
        .unwrap();
        fs::write(&wrapper, "use helper\n\nfn run() -> int:\n    0\n").unwrap();
        fs::write(&helper, "fn helper_fn() -> int:\n    1\n").unwrap();

        let loaded = load_module_with_imports(&entry, &mut HashSet::new()).unwrap();
        let has_run = loaded
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(func) if func.name == "run"));
        let has_helper = loaded
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(func) if func.name == "helper_fn"));

        assert!(has_run);
        assert!(!has_helper);
    }

    #[test]
    fn nested_group_imports_flatten_transitively() {
        let temp = tempfile::tempdir().unwrap();
        let entry = temp.path().join("main.spl");
        let wrapper = temp.path().join("wrapper.spl");
        let helper = temp.path().join("helper.spl");

        fs::write(&entry, "use wrapper.{run}\nfn main() -> int:\n    run()\n").unwrap();
        fs::write(
            &wrapper,
            "use helper.{helper_fn}\n\nfn run() -> int:\n    helper_fn()\n",
        )
        .unwrap();
        fs::write(&helper, "fn helper_fn() -> int:\n    1\n").unwrap();

        let loaded = load_module_with_imports(&entry, &mut HashSet::new()).unwrap();
        let has_run = loaded
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(func) if func.name == "run"));
        let has_helper = loaded
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(func) if func.name == "helper_fn"));

        assert!(has_run);
        assert!(has_helper);
    }

    #[test]
    fn nested_direct_symbol_imports_flatten_transitively() {
        let temp = tempfile::tempdir().unwrap();
        let entry = temp.path().join("main.spl");
        let wrapper = temp.path().join("wrapper.spl");
        let pipeline = temp.path().join("pipeline.spl");

        fs::write(&entry, "use wrapper.{run}\nfn main() -> int:\n    run()\n").unwrap();
        fs::write(
            &wrapper,
            "use pipeline.compile_default\nfn run() -> int:\n    compile_default()\n",
        )
        .unwrap();
        fs::write(&pipeline, "fn compile_default() -> int:\n    73\n").unwrap();

        let loaded = load_module_with_imports(&entry, &mut HashSet::new()).unwrap();

        assert!(loaded
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(func) if func.name == "compile_default")));
    }

    #[test]
    fn symbol_heuristic_matches_val_var_and_exported_names() {
        let temp = tempfile::tempdir().unwrap();
        let val_file = temp.path().join("val_target.spl");
        let var_file = temp.path().join("var_target.spl");
        let export_file = temp.path().join("export_target.spl");

        fs::write(&val_file, "val TARGET_DEVICE: i32 = 1\n").unwrap();
        fs::write(&var_file, "var g_state: i32 = 0\n").unwrap();
        fs::write(
            &export_file,
            "fn helper():\n    pass\n\nexport helper, TARGET_DEVICE, TARGET_HOST_FILE\n",
        )
        .unwrap();

        assert!(file_might_define_requested_symbol(
            &val_file,
            &["TARGET_DEVICE".to_string()]
        ));
        assert!(file_might_define_requested_symbol(&var_file, &["g_state".to_string()]));
        assert!(file_might_define_requested_symbol(
            &export_file,
            &["TARGET_DEVICE".to_string(), "TARGET_HOST_FILE".to_string()]
        ));
    }

    #[test]
    fn web_wm_example_flattens_nested_web_helpers() {
        let entry = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("..")
            .join("..")
            .join("examples")
            .join("06_io")
            .join("ui")
            .join("web_wm.spl");

        let loaded = load_module_with_imports(&entry, &mut HashSet::new()).unwrap();
        let has_run_web_wm = loaded
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(func) if func.name == "run_web_wm"));
        let has_parse_ui_to_tree = loaded
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(func) if func.name == "parse_ui_to_tree"));
        let has_generate_wm_html_page = loaded
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(func) if func.name == "generate_wm_html_page"));
        let has_handle_ws_wm_upgrade = loaded
            .items
            .iter()
            .any(|item| matches!(item, Node::Function(func) if func.name == "handle_ws_wm_upgrade"));

        assert!(has_run_web_wm);
        assert!(has_parse_ui_to_tree);
        assert!(has_generate_wm_html_page);
        assert!(has_handle_ws_wm_upgrade);
    }

    #[test]
    fn test_extract_startup_config_with_app_type() {
        let source = r#"
@app_type("gui")
fn main():
    pass
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");
        let config = extract_startup_config(&module);

        assert!(config.is_some());
        let config = config.unwrap();
        assert_eq!(config.app_type, StartupAppType::Gui);
        assert!(config.has_app_type);
    }

    #[test]
    fn test_extract_startup_config_with_window_hints() {
        let source = r#"
@window_hints(width=1920, height=1080, title="Test App")
fn main():
    pass
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");
        let config = extract_startup_config(&module);

        assert!(config.is_some());
        let config = config.unwrap();
        assert_eq!(config.window_hints.width, 1920);
        assert_eq!(config.window_hints.height, 1080);
        assert_eq!(config.window_hints.title, "Test App");
        assert!(config.has_window_hints);
    }

    #[test]
    fn test_extract_startup_config_combined() {
        let source = r#"
@app_type("gui")
@window_hints(width=800, height=600, title="My Game")
fn main():
    pass
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");
        let config = extract_startup_config(&module);

        assert!(config.is_some());
        let config = config.unwrap();
        assert_eq!(config.app_type, StartupAppType::Gui);
        assert!(config.has_app_type);
        assert_eq!(config.window_hints.width, 800);
        assert_eq!(config.window_hints.height, 600);
        assert_eq!(config.window_hints.title, "My Game");
        assert!(config.has_window_hints);
    }

    #[test]
    fn test_extract_startup_config_no_main() {
        let source = r#"
fn other():
    pass
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");
        let config = extract_startup_config(&module);

        assert!(config.is_none());
    }

    #[test]
    fn test_extract_startup_config_main_no_decorators() {
        let source = r#"
fn main():
    pass
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");
        let config = extract_startup_config(&module);

        assert!(config.is_some());
        let config = config.unwrap();
        assert_eq!(config.app_type, StartupAppType::Cli); // Default
        assert!(!config.has_app_type);
        assert!(!config.has_window_hints);
    }

    #[test]
    fn test_extract_startup_config_partial_window_hints() {
        let source = r#"
@window_hints(width=1600)
fn main():
    pass
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");
        let config = extract_startup_config(&module);

        assert!(config.is_some());
        let config = config.unwrap();
        assert_eq!(config.window_hints.width, 1600);
        assert_eq!(config.window_hints.height, 720); // Default
        assert_eq!(config.window_hints.title, "Simple Application"); // Default
        assert!(config.has_window_hints);
    }

    #[test]
    fn test_strip_optionals_preserves_question_mark_in_strings() {
        let input = r#"val c = "env_seed[0] ? env_seed : \"seed\""
fn foo(x: Int?) -> text?:
    pass
"#;
        let result = strip_optionals(input.to_string());
        assert!(
            result.contains("env_seed[0] ? env_seed"),
            "? inside string was stripped: {}",
            result
        );
        assert!(!result.contains("Int?"), "Int? in code was NOT stripped: {}", result);
        assert!(
            !result.contains("text?"),
            "text? should have been stripped by caller, but strip_optionals does not strip text?"
        );
    }

    #[test]
    fn test_strip_optionals_c_wrapper_string() {
        let input = r#"    val c_src = "perror(env_seed && env_seed[0] ? env_seed : \"simple bootstrap seed\");\n"
"#;
        let result = strip_optionals(input.to_string());
        assert!(
            result.contains("env_seed[0] ? env_seed"),
            "C ternary ? was stripped! Result: {}",
            result
        );
    }

    #[test]
    fn test_protect_question_marks_in_strings() {
        let input = r#""hello ? world""#;
        let result = protect_question_marks_in_strings(input);
        assert!(!result.contains('?'), "? should be replaced with sentinel");
        assert!(result.contains("QMARK"), "sentinel should be present");
    }

    // --- warn_method_arity_collisions / find_method_arity_collisions ---
    //
    // Non-vacuity proof for the `compiler_impl_block_method_arity_collision`
    // detector: fires on the BeDomNode-shaped repro (two `static fn element`
    // overloads differing only in arity, matching the real defect in
    // `src/lib/gc_async_mut/gpu/browser_engine/dom.spl`), and stays silent on
    // two negative controls that a naive text scanner would misfire on.

    #[test]
    fn method_arity_collision_fires_on_bedomnode_shaped_repro() {
        let source = r#"
class BeDomNode:
    node_id: i64
    tag_name: text

impl BeDomNode:
    static fn element(tag_name: text) -> BeDomNode:
        return BeDomNode(node_id: 0, tag_name: tag_name)

    static fn element(node_id: i64, tag_name: text) -> BeDomNode:
        return BeDomNode(node_id: node_id, tag_name: tag_name)
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");

        let findings = find_method_arity_collisions(&module);
        assert_eq!(findings.len(), 1, "expected exactly one collision, got {:?}", findings);
        let finding = &findings[0];
        assert_eq!(finding.class_name, "BeDomNode");
        assert_eq!(finding.method_name, "element");
        assert_eq!(finding.arities, vec![1, 2]);

        let rendered = finding.render();
        assert!(rendered.contains("BeDomNode"));
        assert!(rendered.contains("element"));
        assert!(rendered.contains('1'));
        assert!(rendered.contains('2'));
        assert!(rendered.contains("JIT dispatch"));
        assert!(rendered.contains("[compiler_impl_block_method_arity_collision]"));
    }

    #[test]
    fn method_arity_collision_silent_when_methods_differ_only_in_type_not_arity() {
        // Same name, same arity (1 param each) but different param types.
        // Not the arity-collision hazard this check targets: must stay silent
        // so the detector isn't a blanket "duplicate method name" scanner.
        let source = r#"
class Wrapper:
    value: i64

impl Wrapper:
    static fn make(value: i64) -> Wrapper:
        return Wrapper(value: value)

    static fn make(value: text) -> Wrapper:
        return Wrapper(value: 0)
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");

        let findings = find_method_arity_collisions(&module);
        assert!(
            findings.is_empty(),
            "same-arity, different-type overloads must not fire the arity-collision check: {:?}",
            findings
        );
    }

    #[test]
    fn method_arity_collision_silent_for_nested_extern_fn_inside_method_body() {
        // A local `extern fn` declared inside a method body must NOT be
        // confused with an impl-block-level method of the same name at a
        // different arity — this is exactly the false-positive class a
        // text/indentation scanner produced. Structurally, nested
        // declarations live in the method's `body`, never in
        // `ImplBlock.methods`, so this must stay silent.
        let source = r#"
class Wrapper:
    value: i64

impl Wrapper:
    static fn make(value: i64) -> Wrapper:
        extern fn make(a: i64, b: i64, c: i64) -> i64
        return Wrapper(value: value)
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");

        let findings = find_method_arity_collisions(&module);
        assert!(
            findings.is_empty(),
            "nested extern fn inside a method body must not be treated as an impl-block method: {:?}",
            findings
        );
    }

    #[test]
    fn method_arity_collision_silent_for_comment_mentioning_a_different_arity() {
        // A comment whose TEXT happens to describe a same-named method at a
        // different arity (exactly the shape of the real explanatory comment
        // above `element_with_id` in dom.spl, e.g. "two `static fn element`
        // co-compiled definitions") must not be mistaken for a second
        // definition. This is a structural AST check over `ImplBlock.methods`
        // — comments never become AST nodes — but this test pins that
        // guarantee explicitly so a future regression (e.g. a parser change
        // that leaks doc-comment text into the item list) is caught here.
        let source = r#"
class Wrapper:
    value: i64

impl Wrapper:
    static fn make(value: i64) -> Wrapper:
        """Construct a Wrapper."""
        Wrapper(value: value)

    # Named distinctly from `make(value)` above rather than overloaded on
    # arity: two `static fn make` co-compiled definitions with differing
    # signatures (e.g. static fn make(a: i64, b: i64, c: i64)) would corrupt
    # struct-field reads under JIT.
    static fn make_pair(value: i64, other: i64) -> Wrapper:
        Wrapper(value: value + other)
"#;
        let mut parser = simple_parser::Parser::new(source);
        let module = parser.parse().expect("parse ok");

        let findings = find_method_arity_collisions(&module);
        assert!(
            findings.is_empty(),
            "a comment describing a differently-named/differently-arity method must not fire: {:?}",
            findings
        );
    }

    /// Not a correctness test — a repo-wide census of real
    /// `compiler_impl_block_method_arity_collision` sites under `src/`.
    /// `#[ignore]`d so normal `cargo test` runs don't pay the walk cost; run
    /// explicitly with `cargo test -p simple-compiler --lib
    /// pipeline::module_loader::tests::scan_repo_for_method_arity_collisions
    /// -- --ignored --nocapture`.
    #[test]
    #[ignore]
    fn scan_repo_for_method_arity_collisions() {
        // CARGO_MANIFEST_DIR is <repo>/src/compiler_rust/compiler; two levels
        // up lands on <repo>/src.
        let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
        let src_root = manifest_dir
            .join("../..")
            .canonicalize()
            .expect("resolve repo src/ root from CARGO_MANIFEST_DIR");
        assert!(
            src_root.ends_with("src"),
            "expected repo src/ root, got {}",
            src_root.display()
        );

        let mut spl_files = Vec::new();
        collect_spl_files(&src_root, &mut spl_files);

        // Dedupe by canonicalized real path: symlinked mirrors of the same
        // tree (e.g. src/std -> src/lib) must not count the same source file
        // twice.
        let mut seen_real_paths = std::collections::HashSet::new();
        spl_files.retain(|p| match p.canonicalize() {
            Ok(real) => seen_real_paths.insert(real),
            Err(_) => true, // keep unreadable paths so read_to_string reports the failure below
        });
        spl_files.sort();

        let mut parse_failures = 0usize;
        let mut total_findings = 0usize;
        let mut sites: Vec<String> = Vec::new();
        for file in &spl_files {
            let Ok(source) = fs::read_to_string(file) else {
                parse_failures += 1;
                continue;
            };
            let mut parser = simple_parser::Parser::new(&source);
            let module = match parser.parse() {
                Ok(m) => m,
                Err(_) => {
                    parse_failures += 1;
                    continue;
                }
            };
            for finding in find_method_arity_collisions(&module) {
                total_findings += 1;
                sites.push(format!(
                    "{}: class `{}` method `{}` arities {:?}",
                    file.display(),
                    finding.class_name,
                    finding.method_name,
                    finding.arities
                ));
            }
        }

        eprintln!(
            "scan_repo_for_method_arity_collisions: {} .spl files scanned, {} failed to parse, \
             {} arity-collision site(s) found",
            spl_files.len(),
            parse_failures,
            total_findings
        );
        for site in &sites {
            eprintln!("  {site}");
        }
    }

    fn collect_spl_files(dir: &Path, out: &mut Vec<PathBuf>) {
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                collect_spl_files(&path, out);
            } else if path.extension().and_then(|e| e.to_str()) == Some("spl") {
                out.push(path);
            }
        }
    }
}

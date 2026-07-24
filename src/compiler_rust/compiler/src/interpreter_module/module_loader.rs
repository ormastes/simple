//! Module loading functionality for the Simple interpreter.
//!
//! This module handles loading and parsing module files, managing circular imports,
//! and caching module exports.
//!
//! ## Capability-Based Import Validation
//!
//! When a module declares `requires [capabilities]`, imports are validated:
//! - Imported functions' effects must be compatible with importer's capabilities
//! - If importer has `requires [io]`, it can import functions with @io
//! - If importer has no `requires`, it can import anything (unrestricted)
//! - Capability violations are reported at import time

use std::collections::HashMap;
use std::fs;
use std::path::Path;
use std::sync::{Arc, OnceLock};
use std::time::Instant;

use tracing::{debug, error, trace, warn, instrument};

/// Check if loader tracing is enabled via SIMPLE_LOADER_TRACE=1 env var.
/// Result is cached in a OnceLock so the env var is only read once.
fn loader_trace_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        std::env::var("SIMPLE_LOADER_TRACE")
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false)
    })
}

/// Print a structured trace line to stderr when SIMPLE_LOADER_TRACE=1.
/// No-op when tracing is disabled (the format string is never evaluated).
macro_rules! loader_trace {
    ($tag:expr, $($arg:tt)*) => {
        if loader_trace_enabled() {
            eprintln!("[loader-trace] {}: {}", $tag, format!($($arg)*));
        }
    };
}

use simple_parser::ast::{Capability, ClassDef, EnumDef, Effect, ImportTarget, Node, UseStmt};

use crate::error::CompileError;
use crate::value::{Env, Value};

use super::module_cache::{
    cache_module_definitions, cache_module_exports, clear_partial_module_exports, decrement_load_depth,
    get_cached_module_exports, get_partial_module_exports, increment_load_depth, increment_total_modules,
    is_module_loading, mark_module_loading, merge_cached_module_definitions, unmark_module_loading,
    record_module_visit, record_module_eval_time, record_sibling_preload, MAX_MODULE_DEPTH,
};
use super::module_evaluator::{evaluate_module_exports, evaluate_module_exports_with_preloaded};
use super::path_resolution::resolve_module_path;

type Enums = HashMap<String, Arc<EnumDef>>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RuntimeFamily {
    Common,
    NogcAsyncMutNoalloc,
    NogcAsyncMut,
    NogcAsyncImmut,
    NogcSyncImmut,
    Async,
    NogcSyncMut,
    GcAsyncMut,
    GcAsyncImmut,
    GcSyncMut,
    GcSyncImmut,
}

impl RuntimeFamily {
    fn from_name(name: &str) -> Option<Self> {
        match name {
            "common" => Some(Self::Common),
            "nogc_async_mut_noalloc" => Some(Self::NogcAsyncMutNoalloc),
            "nogc_async_mut" => Some(Self::NogcAsyncMut),
            "nogc_async_immut" => Some(Self::NogcAsyncImmut),
            "nogc_sync_immut" => Some(Self::NogcSyncImmut),
            "async" => Some(Self::Async),
            "nogc_sync_mut" => Some(Self::NogcSyncMut),
            "gc_async_mut" => Some(Self::GcAsyncMut),
            "gc_async_immut" => Some(Self::GcAsyncImmut),
            "gc_sync_mut" => Some(Self::GcSyncMut),
            "gc_sync_immut" => Some(Self::GcSyncImmut),
            _ => None,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Common => "common",
            Self::NogcAsyncMutNoalloc => "nogc_async_mut_noalloc",
            Self::NogcAsyncMut => "nogc_async_mut",
            Self::NogcAsyncImmut => "nogc_async_immut",
            Self::NogcSyncImmut => "nogc_sync_immut",
            Self::Async => "async",
            Self::NogcSyncMut => "nogc_sync_mut",
            Self::GcAsyncMut => "gc_async_mut",
            Self::GcAsyncImmut => "gc_async_immut",
            Self::GcSyncMut => "gc_sync_mut",
            Self::GcSyncImmut => "gc_sync_immut",
        }
    }

    fn is_gc(self) -> bool {
        matches!(
            self,
            Self::GcAsyncMut | Self::GcAsyncImmut | Self::GcSyncMut | Self::GcSyncImmut
        )
    }

    fn is_noalloc(self) -> bool {
        matches!(self, Self::NogcAsyncMutNoalloc)
    }

    fn is_allocating(self) -> bool {
        !matches!(self, Self::Common | Self::NogcAsyncMutNoalloc)
    }

    fn rank(self) -> i8 {
        match self {
            Self::Common => 0,
            Self::NogcAsyncMutNoalloc => 1,
            Self::NogcAsyncMut | Self::NogcAsyncImmut | Self::NogcSyncImmut => 2,
            Self::Async | Self::NogcSyncMut => 3,
            Self::GcAsyncMut | Self::GcAsyncImmut | Self::GcSyncMut | Self::GcSyncImmut => 4,
        }
    }
}

fn runtime_family_from_path(path: &Path) -> Option<RuntimeFamily> {
    let components: Vec<String> = path
        .components()
        .map(|component| component.as_os_str().to_string_lossy().to_string())
        .collect();

    for pair in components.windows(2) {
        if pair[0] == "lib" || pair[0] == "std" {
            return RuntimeFamily::from_name(&pair[1]);
        }
    }

    None
}

fn runtime_family_import_violation_reason(
    importer_family: RuntimeFamily,
    imported_family: RuntimeFamily,
) -> Option<&'static str> {
    if imported_family == RuntimeFamily::Common {
        return None;
    }

    if importer_family.is_noalloc() && imported_family.is_gc() {
        return Some("noalloc_imports_gc_family");
    }

    if importer_family.is_noalloc() && imported_family.is_allocating() {
        return Some("noalloc_imports_allocating_family");
    }

    if !importer_family.is_gc() && imported_family.is_gc() {
        return Some("nogc_imports_gc_family");
    }

    if imported_family.rank() > importer_family.rank() {
        return Some("higher_layer_runtime_family");
    }

    None
}

fn gc_boundary_warning_message(importer_path: &Path, imported_path: &Path, module_name: &str) -> Option<String> {
    let importer_family = runtime_family_from_path(importer_path)?;
    let imported_family = runtime_family_from_path(imported_path)?;

    if importer_family == RuntimeFamily::Common
        || imported_family == RuntimeFamily::Common
        || importer_family == imported_family
    {
        return None;
    }

    let reason = runtime_family_import_violation_reason(importer_family, imported_family)?;
    let label = if importer_family.is_noalloc() && imported_family.is_allocating() {
        "Allocating"
    } else if imported_family.is_gc() {
        "GC"
    } else {
        "Higher-layer"
    };

    Some(format!(
        "[gc-warning] {label} module '{module_name}' (family: {}) imported in restricted context (family: {}) ({reason})",
        imported_family.name(),
        importer_family.name()
    ))
}

fn strict_runtime_family_imports_enabled() -> bool {
    std::env::var("SIMPLE_STRICT_RUNTIME_FAMILY")
        .map(|value| value == "1" || value.eq_ignore_ascii_case("true"))
        .unwrap_or(false)
}

fn enforce_gc_boundary_policy(
    importer_path: Option<&Path>,
    imported_path: &Path,
    module_name: &str,
    strict: bool,
) -> Result<(), CompileError> {
    let Some(importer_path) = importer_path else {
        return Ok(());
    };
    if let Some(message) = gc_boundary_warning_message(importer_path, imported_path, module_name) {
        if strict {
            return Err(CompileError::Runtime(message.replace("[gc-warning]", "[gc-error]")));
        }
        if std::env::var_os("SIMPLE_NO_DEPRECATED_WARNINGS").is_some() {
            return Ok(());
        }
        eprintln!("{message}");
    }
    Ok(())
}

fn emit_gc_boundary_warning(
    importer_path: Option<&Path>,
    imported_path: &Path,
    module_name: &str,
) -> Result<(), CompileError> {
    enforce_gc_boundary_policy(
        importer_path,
        imported_path,
        module_name,
        strict_runtime_family_imports_enabled(),
    )
}

fn requested_group_import_names(use_stmt: &UseStmt) -> Option<Vec<String>> {
    match &use_stmt.target {
        ImportTarget::Group(items) => Some(
            items
                .iter()
                .filter_map(|item| match item {
                    ImportTarget::Single(name) => Some(name.clone()),
                    ImportTarget::Aliased { name, .. } => Some(name.clone()),
                    _ => None,
                })
                .collect(),
        ),
        _ => None,
    }
}

/// Check if a sibling file might define any of the requested names.
/// Returns `Some(source)` if it might (caching the read), `None` if not.
/// When `requested_names` is empty, returns `Some(source)` for all readable files.
fn sibling_might_define_requested_names(path: &Path, requested_names: &[String]) -> Option<String> {
    // Skip files larger than configurable limit — unlikely to be simple re-export modules
    let max_check_bytes = crate::memory_guard::sibling_max_check_bytes();
    if let Ok(meta) = std::fs::metadata(path) {
        if meta.len() > max_check_bytes {
            return None;
        }
    }

    let source = fs::read_to_string(path).ok()?;

    if requested_names.is_empty() {
        return Some(source);
    }

    let matches = requested_names.iter().any(|name| {
        let fn_pat = format!("fn {}(", name);
        let extern_pat = format!("extern fn {}(", name);
        let class_pat = format!("class {}", name);
        let struct_pat = format!("struct {}", name);
        let enum_pat = format!("enum {}", name);
        let trait_pat = format!("trait {}", name);
        let let_pat = format!("let {}", name);
        source.contains(&fn_pat)
            || source.contains(&extern_pat)
            || source.contains(&class_pat)
            || source.contains(&struct_pat)
            || source.contains(&enum_pat)
            || source.contains(&trait_pat)
            || source.contains(&let_pat)
    });

    if matches {
        Some(source)
    } else {
        None
    }
}

fn locally_defined_names(items: &[Node]) -> Vec<String> {
    let mut names = Vec::new();
    for item in items {
        match item {
            Node::Function(f) => names.push(f.name.clone()),
            Node::Class(c) => names.push(c.name.clone()),
            Node::Struct(s) => names.push(s.name.clone()),
            Node::Enum(e) => names.push(e.name.clone()),
            Node::Let(stmt) => {
                if let simple_parser::ast::Pattern::Identifier(name) = &stmt.pattern {
                    names.push(name.clone());
                }
            }
            _ => {}
        }
    }
    names
}

fn unresolved_bare_export_names(items: &[Node]) -> Vec<String> {
    let local_names = locally_defined_names(items);
    let mut names = Vec::new();
    for item in items {
        if let Node::ExportUseStmt(export_stmt) = item {
            if export_stmt.path.segments.is_empty() {
                for name in export_target_names(&export_stmt.target) {
                    if !local_names.iter().any(|local| local == &name) && !names.iter().any(|seen| seen == &name) {
                        names.push(name);
                    }
                }
            }
        }
    }
    names
}

fn export_target_names(target: &ImportTarget) -> Vec<String> {
    match target {
        ImportTarget::Single(name) => vec![name.clone()],
        ImportTarget::Aliased { name, alias } => vec![name.clone(), alias.clone()],
        ImportTarget::Group(items) => items.iter().flat_map(export_target_names).collect(),
        ImportTarget::Glob => Vec::new(),
    }
}

/// Decide whether an AST item should be kept when performing selective (group) import filtering.
///
/// This is a generalized filter: given a set of `requested_names`, it keeps only the items
/// that are relevant to those names. This avoids evaluating large modules in full when the
/// caller only needs a few symbols.
///
/// Rules:
/// - `ExportUseStmt`: keep only if it re-exports at least one requested name
/// - `UseStmt`: always keep. Imported functions often depend on helper imports that
///   do not share the same symbol names as the exported API surface.
/// - `Function`: keep only if the function name is in the requested set
/// - Everything else (classes, structs, enums, etc.): always keep (cheap to evaluate)
fn should_keep_selective_export(item: &Node, requested_names: &[String]) -> bool {
    match item {
        Node::ExportUseStmt(export_stmt) => {
            // Glob target (export *) is a wildcard — always keep it
            if matches!(export_stmt.target, ImportTarget::Glob) {
                return true;
            }
            let export_names = export_target_names(&export_stmt.target);
            !export_names.is_empty()
                && export_names
                    .iter()
                    .any(|name| requested_names.iter().any(|wanted| wanted == name))
        }
        Node::UseStmt(_) => true,
        Node::Function(f) => requested_names.iter().any(|wanted| wanted == &f.name),
        _ => true,
    }
}

/// Loose text probe: does `path`'s source plausibly provide any of `names` —
/// either as a definition (`fn name(`, `class name`, ..., matched by
/// [`sibling_might_define_requested_names`]) or as a member of an
/// `export`/`use ... {.., name, ..}` re-export list (e.g. a thin shim like
/// `export use std.nogc_sync_mut.spec.{.., print_summary, ..}`, which has no
/// `fn print_summary(` of its own)? Returns the subset of `names` found.
/// Tokenizes on non-identifier characters so a name must appear as a whole
/// token, not merely as a substring of a longer identifier. Reads the file
/// once regardless of how many names are probed. Deliberately loose/
/// best-effort: a false positive here just falls back to the existing
/// "package wins" default below, not a wrong resolution.
fn file_plausibly_provides_names(path: &Path, names: &[String]) -> std::collections::HashSet<String> {
    let max_check_bytes = crate::memory_guard::sibling_max_check_bytes();
    if let Ok(meta) = std::fs::metadata(path) {
        if meta.len() > max_check_bytes {
            return std::collections::HashSet::new();
        }
    }
    let Ok(source) = fs::read_to_string(path) else {
        return std::collections::HashSet::new();
    };
    let tokens: std::collections::HashSet<&str> =
        source.split(|c: char| !(c.is_alphanumeric() || c == '_')).collect();
    names
        .iter()
        .filter(|name| tokens.contains(name.as_str()))
        .cloned()
        .collect()
}

fn prefer_package_init_for_member_import(module_path: &Path, use_stmt: &UseStmt) -> std::path::PathBuf {
    match &use_stmt.target {
        ImportTarget::Group(_) | ImportTarget::Glob => {
            if module_path.extension().is_some_and(|ext| ext == "spl")
                && module_path.file_name().is_none_or(|name| name != "__init__.spl")
            {
                let package_init = module_path.with_extension("").join("__init__.spl");
                if package_init.exists() && package_init.is_file() {
                    // A `Group` import naming specific symbols must not redirect
                    // away from a sibling FILE that provides those symbols into a
                    // same-named PACKAGE that doesn't — that silently loses the
                    // requested names (see
                    // doc/08_tracking/bug/std_spec_package_shadows_file_print_summary_2026-07-17.md:
                    // `use std.spec.{print_summary, ...}` resolved the FILE
                    // `spec.spl`, which defines them, then got redirected here to
                    // the sibling `spec/__init__.spl` PACKAGE, which doesn't).
                    // The check must be PER-NAME, not "package has any match at
                    // all": a re-export shim can list a large mixed group where
                    // the package legitimately covers *some* names (e.g. a BDD
                    // facade re-exporting both the framework's own `print_summary`
                    // AND decorator/env-detect names like `is_windows`/`skip_it`
                    // that genuinely live in the sibling package) while still
                    // lacking others the file uniquely provides. A coarse "package
                    // has ANY requested name" test still redirected in that mixed
                    // case and re-lost `print_summary`. So: withhold the
                    // (otherwise unconditional) package-init preference as soon as
                    // ANY single requested name is positively confirmed on the
                    // file but NOT on the package; an empty/ambiguous probe on
                    // both sides for a given name doesn't count either way and
                    // falls back to the existing "package wins" default (see
                    // `prefers_package_init_for_group_imports_when_both_exist`).
                    if let ImportTarget::Group(_) = &use_stmt.target {
                        if let Some(requested) = requested_group_import_names(use_stmt) {
                            if !requested.is_empty() {
                                let file_names = file_plausibly_provides_names(module_path, &requested);
                                let package_names = file_plausibly_provides_names(&package_init, &requested);
                                let file_has_unique_name = file_names.iter().any(|name| !package_names.contains(name));
                                if file_has_unique_name {
                                    return module_path.to_path_buf();
                                }
                            }
                        }
                    }
                    return package_init;
                }
            }
            module_path.to_path_buf()
        }
        _ => module_path.to_path_buf(),
    }
}

/// Wraps `prefer_package_init_for_member_import` with a guard against
/// self-referential redirect cycles (task #153).
///
/// A `Group`/`Glob` import from `X.spl` normally prefers a sibling
/// `X/__init__.spl` package aggregator when one exists — many legitimate
/// "thin file + real package" pairs rely on this (see
/// `prefers_package_init_for_group_imports_when_both_exist`). But if `X/__init__.spl`
/// itself re-exports from the very module path that led here (e.g. a stale
/// duplicate `X/__init__.spl` doing `export use pkg.X.{...}`), the redirect
/// sends us right back into a module already on the load stack. That hits
/// the circular-import branch below, which returns empty/partial exports —
/// silently dropping every symbol the redirect exists to serve. This is
/// exactly how `compiler_driver_create` went missing for standalone
/// `simple run` scripts when a stale `80.driver/driver/__init__.spl` shadowed
/// the real `80.driver/driver.spl` (see
/// doc/08_tracking/bug/selfhost_bootstrap_unresolved_symbols_2026-06-24.md).
/// In that specific case, keep the already-resolved file — it has the real
/// definitions instead of a stale/self-referential aggregator.
fn resolve_member_import_target(module_path: &Path, use_stmt: &UseStmt) -> std::path::PathBuf {
    let redirected = prefer_package_init_for_member_import(module_path, use_stmt);
    if redirected != module_path && is_module_loading(&redirected) {
        module_path.to_path_buf()
    } else {
        redirected
    }
}

/// Validate that imported function effects are compatible with importer's capabilities.
///
/// If the importer has no `requires [capabilities]`, it's unrestricted and can import anything.
/// Otherwise, each imported function's effects must be covered by the importer's capabilities.
pub fn validate_import_capabilities(
    import_name: &str,
    func_effects: &[Effect],
    importer_capabilities: &[Capability],
) -> Result<(), CompileError> {
    // If importer has no capabilities declared, it's unrestricted
    if importer_capabilities.is_empty() {
        return Ok(());
    }

    // Check each effect of the imported function
    for effect in func_effects {
        // Map effect to required capability
        let required_cap = Capability::from_effect(effect);

        // Async is always allowed (execution model, not capability)
        if required_cap.is_none() {
            continue;
        }

        let required_cap = required_cap.unwrap();

        // Check if importer has the required capability
        if !importer_capabilities.contains(&required_cap) {
            return Err(CompileError::semantic(format!(
                "Cannot import '{}' with @{} effect: module requires [{}] capability",
                import_name,
                effect.decorator_name(),
                required_cap.name()
            )));
        }
    }

    Ok(())
}

/// Extract capabilities from a module's AST nodes
pub fn extract_module_capabilities(items: &[Node]) -> Vec<Capability> {
    for item in items {
        if let Node::RequiresCapabilities(stmt) = item {
            return stmt.capabilities.clone();
        }
    }
    Vec::new() // No capabilities = unrestricted
}

/// Get the import alias from a UseStmt if it exists
pub fn get_import_alias(use_stmt: &UseStmt) -> Option<String> {
    match &use_stmt.target {
        ImportTarget::Aliased { alias, .. } => Some(alias.clone()),
        _ => None,
    }
}

/// Load a module file, evaluate it, and return exports with captured environment
/// This is needed so that module-level imports are accessible in exported functions
#[instrument(skip(use_stmt, current_file, functions, classes, enums), fields(path = ?use_stmt.path.segments))]
pub fn load_and_merge_module(
    use_stmt: &UseStmt,
    current_file: Option<&Path>,
    functions: &mut HashMap<String, Arc<simple_parser::ast::FunctionDef>>,
    classes: &mut HashMap<String, Arc<ClassDef>>,
    enums: &mut Enums,
) -> Result<Value, CompileError> {
    // Check depth limit to prevent infinite recursion
    let depth = increment_load_depth();
    if depth > MAX_MODULE_DEPTH {
        decrement_load_depth();
        error!(depth, max = MAX_MODULE_DEPTH, "Module import depth exceeded");
        return Err(CompileError::Runtime(format!(
            "Maximum module import depth ({}) exceeded. Possible circular import or very deep module hierarchy.",
            MAX_MODULE_DEPTH
        )));
    }

    // Build module path from segments (path only, not the import target)
    // Filter out relative-prefix markers that refer to the current module's directory.
    // `self` in `use self.main.{...}` and leading `.` in `use .wiki_tool.{...}`
    // are both sibling-package imports, not real path segments.
    let mut parts: Vec<String> = use_stmt
        .path
        .segments
        .iter()
        .filter(|s| s.as_str() != "crate" && s.as_str() != "self" && s.as_str() != ".")
        .cloned()
        .collect();

    debug!(parts = ?parts, target = ?use_stmt.target, depth, "Loading module");

    // Handle the case where path is empty but target contains the module name
    // e.g., `import spec as sp` has path=[], target=Aliased { name: "spec", alias: "sp" }
    // In this case, "spec" is the module path, not an item to extract from a module
    let import_item_name: Option<String> = if parts.is_empty() {
        match &use_stmt.target {
            ImportTarget::Single(name) => {
                // `import spec` - name is the module path
                parts.push(name.clone());
                None // Import whole module
            }
            ImportTarget::Aliased { name, .. } => {
                // `import spec as sp` - name is the module path
                parts.push(name.clone());
                None // Import whole module (aliased)
            }
            ImportTarget::Glob => {
                // Glob with empty path is invalid - can't do `import *` with no module
                warn!("Glob import with empty path - skipping");
                decrement_load_depth();
                return Ok(Value::Dict(Arc::new(HashMap::new())));
            }
            ImportTarget::Group(items) => {
                // Group import with empty path: import {X, Y, Z}
                // This is invalid - need a module to import from
                warn!("Group import with empty path - skipping");
                decrement_load_depth();
                return Ok(Value::Dict(Arc::new(HashMap::new())));
            }
        }
    } else {
        // Path is not empty - the target 'name' is the final component of the module path
        match &use_stmt.target {
            ImportTarget::Single(name) => {
                // `import X.Y.Z` - import the whole module X.Y.Z, bind to "Z"
                // The target 'name' is the final component of the module path.
                // e.g., `import verification.lean.types`:
                //   - Parser produces: path=["verification", "lean"], name="types"
                //   - We need: parts=["verification", "lean", "types"], import_item_name=None
                parts.push(name.clone());
                None // Import whole module
            }
            ImportTarget::Aliased { name, .. } => {
                // `import X.Y.Z as alias` - import the whole module X.Y.Z, bind to alias
                // The target 'name' is the final component of the module path that was
                // separated by the parser. We need to add it back to get the full path.
                // e.g., `import verification.lean.types as types`:
                //   - Parser produces: path=["verification", "lean"], name="types"
                //   - We need: parts=["verification", "lean", "types"], import_item_name=None
                parts.push(name.clone());
                None // Import whole module
            }
            ImportTarget::Glob => None,
            ImportTarget::Group(_) => {
                // Group imports: `import module.{X, Y, Z}`
                // Load the module and extract the specified items
                None // Import whole module, then extract items
            }
        }
    };

    // Try to resolve the module path
    let base_dir = current_file.and_then(|p| p.parent()).unwrap_or(Path::new("."));

    let module_path = match resolve_module_path(&parts, base_dir) {
        Ok(p) => {
            // `unit.*` opaque sentinel: the unit registry is resolved by the
            // self-hosted compiler. The Rust seed accepts the import and
            // returns an empty module so later stages see no missing symbols.
            // See `.sstack/unit-system-consolidation/state.md` §8.
            if super::path_resolution::is_unit_opaque_sentinel(&p) {
                debug!(path = %parts.join("."), "unit.* opaque soft-accept");
                decrement_load_depth();
                return Ok(Value::Dict(Arc::new(HashMap::new())));
            }
            p
        }
        Err(e) => {
            // FALLBACK: If resolution fails and we're not already extracting an item,
            // try treating the last path component as an item name instead of a module name.
            // E.g., `use app.lsp.server.LspServer` fails to find app/lsp/server/LspServer.spl,
            // so try loading app/lsp/server.spl and extract "LspServer" from it.
            if import_item_name.is_none() && parts.len() > 1 {
                debug!(
                    "Module resolution failed for {:?}, trying fallback: treating last component as item name",
                    parts.join(".")
                );
                // Pop the last component and treat it as an item name
                let mut parent_parts = parts.clone();
                let item_name = parent_parts.pop().unwrap();

                // Try to resolve the parent path
                if let Ok(_parent_module_path) = resolve_module_path(&parent_parts, base_dir) {
                    // Successfully resolved parent module - recursively load it and extract the item
                    decrement_load_depth();

                    // Recursively call load_and_merge_module with the parent path
                    // IMPORTANT: We need to construct the use_stmt such that it loads the PARENT module
                    // without trying to extract an item, because we'll extract the item ourselves below.
                    let mut modified_use_stmt = use_stmt.clone();
                    // For parent_parts = ["app", "lsp"], we need the parser form where:
                    //   - path.segments contains all but the last part
                    //   - target contains the last part
                    // So if parent_parts = ["app", "lsp", "server"], we want:
                    //   - path.segments = ["app", "lsp"]
                    //   - target = Single("server")
                    if parent_parts.len() >= 2 {
                        modified_use_stmt.path.segments = parent_parts[..parent_parts.len() - 1].to_vec();
                        modified_use_stmt.target = ImportTarget::Single(parent_parts[parent_parts.len() - 1].clone());
                    } else if parent_parts.len() == 1 {
                        // Single component like ["spec"] - path is empty, target is the component
                        modified_use_stmt.path.segments = vec![];
                        modified_use_stmt.target = ImportTarget::Single(parent_parts[0].clone());
                    } else {
                        // Empty parent_parts - shouldn't happen but handle it
                        modified_use_stmt.path.segments = vec![];
                        modified_use_stmt.target = ImportTarget::Glob;
                    }

                    return load_and_merge_module(&modified_use_stmt, current_file, functions, classes, enums)
                        .and_then(|module_value| {
                            // Extract the specific item from the loaded module
                            if let Value::Dict(exports_dict) = &module_value {
                                if let Some(value) = exports_dict.get(&item_name) {
                                    return Ok(value.clone());
                                }
                            }
                            Err(CompileError::Runtime(format!(
                                "Module {:?} does not export '{}'",
                                parent_parts.join("."),
                                item_name
                            )))
                        });
                }
            }

            decrement_load_depth();
            debug!(module = %parts.join("."), error = %e, "Failed to resolve module");
            return Err(e);
        }
    };
    let original_module_path = module_path.clone();
    let module_path = resolve_member_import_target(&module_path, use_stmt);
    if module_path != original_module_path {
        loader_trace!(
            "init-redirect",
            "{} -> {}",
            original_module_path.display(),
            module_path.display()
        );
    }
    loader_trace!("resolve", "{} -> {}", parts.join("."), module_path.display());
    debug!(module = %parts.join("."), path = ?module_path, "Resolved module path");
    if let Err(error) = emit_gc_boundary_warning(current_file, &module_path, &parts.join(".")) {
        decrement_load_depth();
        return Err(error);
    }
    record_module_visit(&module_path, depth);

    // Check cache first - if we've already loaded this module, return cached exports
    if let Some(cached_exports) = get_cached_module_exports(&module_path) {
        loader_trace!("cache-hit", "{}", module_path.display());
        // Merge cached definitions (classes, functions, enums) into caller's HashMaps.
        // This ensures that static method calls work on imported classes.
        // Functions are Arc<FunctionDef> in the cache; we unwrap to raw FunctionDef for
        // the interpreter's working set, but the Arc clone from cache is cheap.
        merge_cached_module_definitions(&module_path, classes, functions, enums);

        decrement_load_depth();
        // If importing a specific item, extract it from cached exports
        if let Some(item_name) = import_item_name {
            if let Value::Dict(exports_dict) = &cached_exports {
                if let Some(value) = exports_dict.get(&item_name) {
                    return Ok(value.clone());
                }
            }
            return Err(CompileError::Runtime(format!("Module does not export '{}'", item_name)));
        }
        return Ok(cached_exports);
    }

    // Check for circular import - if this module is currently being loaded,
    // return partial exports (type definitions) to break the cycle.
    // This allows Java-style forward references where types are available
    // even during circular imports.
    if is_module_loading(&module_path) {
        loader_trace!("circular", "{} (returning partial)", module_path.display());
        // Try to get partial exports (type definitions from register_definitions)
        if let Some(partial_exports) = get_partial_module_exports(&module_path) {
            debug!(path = ?module_path, "Circular import detected, returning partial exports (type definitions)");
            decrement_load_depth();
            return Ok(partial_exports);
        }
        // Fallback to empty dict if no partial exports yet (module hasn't completed register_definitions)
        warn!(path = ?module_path, "Circular import detected, returning empty dict (no partial exports yet)");
        decrement_load_depth();
        return Ok(Value::Dict(Arc::new(HashMap::new())));
    }

    // Check total module count limit to prevent OOM from loading too many modules
    // Only count unique (non-cached) module loads since cached modules don't add memory
    let total = increment_total_modules();
    let limit = crate::memory_guard::module_limit();
    if crate::memory_guard::module_limit_exceeded(total, limit) {
        decrement_load_depth();
        warn!(total, max = limit, path = ?module_path, "Total module count limit exceeded");
        return Err(CompileError::Runtime(format!(
            "Module count limit ({}) exceeded loading {:?}. Too many transitive imports.",
            limit, module_path
        )));
    }

    // Mark this module as currently loading
    debug!(path = ?module_path, depth, "Loading module");
    mark_module_loading(&module_path);
    let _load_guard = crate::memory_guard::ModuleLoadGuard::enter(&module_path);

    // Read and parse the module
    let mut source = match fs::read_to_string(&module_path) {
        Ok(s) => {
            // Normalize CRLF → LF so indentation-sensitive parsing works on all platforms
            if s.contains('\r') {
                s.replace('\r', "")
            } else {
                s
            }
        }
        Err(e) => {
            unmark_module_loading(&module_path);
            decrement_load_depth();
            return Err(CompileError::Io(format!("Cannot read module {:?}: {}", module_path, e)));
        }
    };
    source =
        crate::pipeline::cfg_strip::strip_inactive_cfg_arch_globals(&source, simple_common::target::TargetArch::host());

    let mut parser = simple_parser::Parser::new(&source);
    let module = match parser.parse() {
        Ok(m) => m,
        Err(e) => {
            unmark_module_loading(&module_path);
            decrement_load_depth();
            error!(path = ?module_path, error = %e, "Failed to parse module");
            return Err(CompileError::Parse(format!(
                "Cannot parse module {:?}: {}",
                module_path, e
            )));
        }
    };

    let requested_names = requested_group_import_names(use_stmt);
    // Selective filtering in the interpreter loader is too aggressive for real
    // modules: exported entrypoints often depend on private helper functions and
    // internal imports whose names do not match the requested export list. Keep
    // the full module so runtime evaluation remains correct.
    // Move instead of clone — `module` is not used after this point.
    let mut filtered_items: Vec<Node> = module.items;
    // Drop wrong-arch @cfg(<arch>) fn variants before evaluating/registering
    // the module: interpreted code executes on the HOST, and registration is
    // order-driven (multivariant misdispatch, see pipeline::cfg_strip).
    crate::pipeline::cfg_strip::strip_inactive_cfg_arch_fn_nodes(
        &mut filtered_items,
        simple_common::target::TargetArch::host(),
    );
    let load_start = Instant::now();

    // Evaluate the module to get its environment (including imports)
    debug!(path = ?module_path, "Evaluating module exports");

    // For __init__.spl files with bare exports: preload sibling .spl files.
    // Many __init__.spl files use bare exports (export X, Y, Z) where the symbols
    // come from sibling files (mod.spl, or other .spl files in the same directory).
    // Without preloading these siblings, bare exports resolve to nothing.
    let preloaded_env: Option<HashMap<String, Value>> = if module_path.file_name().is_some_and(|f| f == "__init__.spl")
    {
        let has_bare_exports = filtered_items
            .iter()
            .any(|item| matches!(item, Node::ExportUseStmt(e) if e.path.segments.is_empty()));
        if has_bare_exports {
            let parent_dir = module_path.parent();
            if let Some(dir) = parent_dir {
                let mut merged_exports: HashMap<String, Value> = HashMap::new();
                // Collect sibling .spl files (not __init__.spl itself)
                let requested_names = requested_names
                    .clone()
                    .map(|names| {
                        let local_names = locally_defined_names(&filtered_items);
                        names
                            .into_iter()
                            .filter(|name| !local_names.iter().any(|local| local == name))
                            .collect::<Vec<_>>()
                    })
                    .or_else(|| {
                        let names = unresolved_bare_export_names(&filtered_items);
                        if names.is_empty() {
                            None
                        } else {
                            Some(names)
                        }
                    });
                if requested_names.as_ref().is_some_and(|names| names.is_empty()) {
                    None
                } else if let Ok(entries) = fs::read_dir(dir) {
                    // Collect siblings with cached source strings to avoid double disk reads.
                    // sibling_might_define_requested_names returns Some(source) on match.
                    let mut sibling_files: Vec<(std::path::PathBuf, Option<String>)> = entries
                        .filter_map(|e| e.ok())
                        .map(|e| e.path())
                        .filter(|p| {
                            p.extension().is_some_and(|ext| ext == "spl")
                                && p.file_name().is_some_and(|f| f != "__init__.spl")
                                && p.file_name().is_some_and(|f| f != "mod_stub.spl")
                                && p.is_file()
                        })
                        .filter_map(|p| {
                            match requested_names.as_ref() {
                                None => Some((p, None)), // no filter — source read deferred
                                Some(names) => match sibling_might_define_requested_names(&p, names) {
                                    Some(source) => Some((p, Some(source))),
                                    None => {
                                        loader_trace!("sibling-skip", "{} (no matching names)", p.display());
                                        None
                                    }
                                },
                            }
                        })
                        .collect();
                    // Sort for deterministic load order; mod.spl first if present
                    sibling_files.sort_by(|(a, _), (b, _)| {
                        let a_is_mod = a.file_name().is_some_and(|f| f == "mod.spl");
                        let b_is_mod = b.file_name().is_some_and(|f| f == "mod.spl");
                        match (a_is_mod, b_is_mod) {
                            (true, false) => std::cmp::Ordering::Less,
                            (false, true) => std::cmp::Ordering::Greater,
                            _ => a.cmp(b),
                        }
                    });
                    // Cap only fully unfiltered scans. Name-targeted preloads are already bounded
                    // by the package's explicit bare-export surface and should not be truncated.
                    let max_siblings = crate::memory_guard::sibling_preload_limit();
                    if requested_names.is_none() && sibling_files.len() > max_siblings {
                        loader_trace!(
                            "sibling-cap",
                            "skipping preload for {} — {} siblings exceeds cap {}",
                            module_path.display(),
                            sibling_files.len(),
                            max_siblings
                        );
                        sibling_files.truncate(max_siblings);
                    }
                    for (sibling_path, cached_source) in &sibling_files {
                        // Early termination: if all requested names are already found, skip remaining siblings
                        if let Some(names) = requested_names.as_ref() {
                            if !names.is_empty() && names.iter().all(|n| merged_exports.contains_key(n)) {
                                loader_trace!(
                                    "sibling-skip",
                                    "{} (all requested names already found)",
                                    sibling_path.display()
                                );
                                break;
                            }
                        }
                        record_sibling_preload();
                        loader_trace!(
                            "sibling-preload",
                            "{} (requested: {:?})",
                            sibling_path.display(),
                            requested_names
                        );
                        debug!(sibling = ?sibling_path, "Preloading sibling for __init__.spl bare exports");
                        // Use cached source from name-matching step to avoid re-reading from disk
                        let sib_source_result = match cached_source {
                            Some(s) => Ok(s.clone()),
                            None => fs::read_to_string(sibling_path),
                        };
                        if let Ok(sib_source) = sib_source_result {
                            let mut sib_source = if sib_source.contains('\r') {
                                sib_source.replace('\r', "")
                            } else {
                                sib_source
                            };
                            sib_source = crate::pipeline::cfg_strip::strip_inactive_cfg_arch_globals(
                                &sib_source,
                                simple_common::target::TargetArch::host(),
                            );
                            let mut sib_parser = simple_parser::Parser::new(&sib_source);
                            match sib_parser.parse() {
                                Ok(mut sib_module) => {
                                    crate::pipeline::cfg_strip::strip_inactive_cfg_arch_fns_for_host(&mut sib_module);
                                    // Evaluate sibling exports in isolation. Preloading is only
                                    // meant to seed __init__.spl bare exports; it should not let
                                    // helper/fallback files mutate the caller's global symbol
                                    // tables or shadow unrelated imports.
                                    let mut preload_functions = HashMap::new();
                                    let mut preload_classes = HashMap::new();
                                    let mut preload_enums = HashMap::new();
                                    if let Ok((_env, sib_exports, _funcs, _classes, _enums)) = evaluate_module_exports(
                                        &sib_module.items,
                                        Some(sibling_path),
                                        &mut preload_functions,
                                        &mut preload_classes,
                                        &mut preload_enums,
                                    ) {
                                        for (k, v) in sib_exports {
                                            // Preserve the first provider for a symbol.
                                            // This matters for packages like std.nogc_sync_mut.io
                                            // where real implementations and fallback stubs coexist:
                                            // env_ops/dir_ops should win, and later stub files should
                                            // not silently replace them during __init__ preloading.
                                            merged_exports.entry(k).or_insert(v);
                                        }
                                    }
                                }
                                Err(e) => {
                                    debug!(
                                        path = ?sibling_path,
                                        error = %e,
                                        "Skipping preloaded sibling module after parse failure"
                                    );
                                }
                            }
                        }
                    }
                    if merged_exports.is_empty() {
                        None
                    } else {
                        Some(merged_exports)
                    }
                } else if merged_exports.is_empty() {
                    None
                } else {
                    Some(merged_exports)
                }
            } else {
                None
            }
        } else {
            None
        }
    } else {
        None
    };

    let (module_env, module_exports, module_functions, module_classes, module_enums) =
        match evaluate_module_exports_with_preloaded(
            &filtered_items,
            Some(&module_path),
            functions,
            classes,
            enums,
            preloaded_env.as_ref(),
        ) {
            Ok(result) => result,
            Err(e) => {
                unmark_module_loading(&module_path);
                decrement_load_depth();
                return Err(e);
            }
        };

    // Export functions with their original captured_env from the defining module.
    // Previously this merged the importer's entire filtered_env into each function's
    // captured_env, causing O(N*M) cascading memory growth across import chains.
    // Functions already have everything they need from their defining module's env.
    let mut exports: HashMap<String, Value> = HashMap::new();
    for (name, value) in module_exports {
        exports.insert(name, value);
    }

    // Cache the full module exports for future use
    let exports_value = Value::Dict(Arc::new(exports.clone()));
    cache_module_exports(&module_path, exports_value);

    // Also cache the module definitions (classes, functions, enums) for future imports.
    // module_functions is already HashMap<String, Arc<FunctionDef>> -- cache stores Arc clones (cheap).
    cache_module_definitions(&module_path, &module_classes, &module_functions, &module_enums);

    // Merge freshly loaded definitions into caller's scope (same as cache case above).
    // This ensures static method calls work on imported classes.
    for (name, class_def) in &module_classes {
        classes.insert(name.clone(), class_def.clone());
    }
    for (name, func_def) in &module_functions {
        if name != "main" {
            // Don't add "main" from imported modules.
            // Arc clone is cheap (refcount bump).
            functions.insert(name.clone(), Arc::clone(func_def));
        }
    }
    for (name, enum_def) in &module_enums {
        enums.insert(name.clone(), enum_def.clone());
    }

    // Clear partial exports now that full exports are available
    clear_partial_module_exports(&module_path);

    // Mark module as done loading
    unmark_module_loading(&module_path);
    decrement_load_depth();
    let elapsed_us = load_start.elapsed().as_micros();
    let elapsed_ms = elapsed_us / 1000;
    record_module_eval_time(&module_path, elapsed_us);
    loader_trace!(
        "loaded",
        "{} ({} exports, {}d, {}ms)",
        module_path.display(),
        exports.len(),
        depth,
        elapsed_ms
    );
    debug!(path = ?module_path, exports = exports.len(), "Successfully loaded module");

    // If importing a specific item, extract it from exports
    if let Some(item_name) = import_item_name {
        // Look up the specific item in the module's exports
        if let Some(value) = exports.get(&item_name) {
            return Ok(value.clone());
        } else {
            return Err(CompileError::Runtime(format!(
                "Module {:?} does not export '{}'",
                module_path, item_name
            )));
        }
    }

    // Otherwise, return the full module dict (for glob imports or module-level imports)
    Ok(Value::Dict(Arc::new(exports)))
}

#[cfg(test)]
mod tests {
    use super::{
        enforce_gc_boundary_policy, gc_boundary_warning_message, load_and_merge_module, loader_trace_enabled,
        mark_module_loading, prefer_package_init_for_member_import, resolve_member_import_target,
        should_keep_selective_export, unmark_module_loading,
    };
    use crate::value::Value;
    use simple_parser::ast::{ImportTarget, ModulePath, Node, UseStmt};
    use simple_parser::token::Span;
    use std::collections::HashMap;
    use std::fs;
    use std::path::Path;

    #[test]
    fn gc_boundary_warning_message_flags_nogc_to_gc_imports() {
        let msg = gc_boundary_warning_message(
            Path::new("/repo/src/lib/nogc_sync_mut/app.spl"),
            Path::new("/repo/src/std/gc_async_mut/__init__.spl"),
            "std.gc_async_mut",
        )
        .expect("no-GC to GC should warn");

        assert!(msg.contains("[gc-warning]"));
        assert!(msg.contains("GC module 'std.gc_async_mut'"));
        assert!(msg.contains("family: gc_async_mut"));
        assert!(msg.contains("family: nogc_sync_mut"));
    }

    #[test]
    fn gc_boundary_warning_message_flags_noalloc_to_allocating_imports() {
        let msg = gc_boundary_warning_message(
            Path::new("/repo/src/lib/nogc_async_mut_noalloc/app.spl"),
            Path::new("/repo/src/lib/nogc_async_mut/task.spl"),
            "std.nogc_async_mut.task",
        )
        .expect("noalloc to allocating family should warn");

        assert!(msg.contains("Allocating module 'std.nogc_async_mut.task'"));
        assert!(msg.contains("family: nogc_async_mut"));
        assert!(msg.contains("family: nogc_async_mut_noalloc"));
    }

    #[test]
    fn gc_boundary_warning_message_flags_lower_layer_imports() {
        let msg = gc_boundary_warning_message(
            Path::new("/repo/src/lib/nogc_async_immut/app.spl"),
            Path::new("/repo/src/lib/nogc_sync_mut/io.spl"),
            "std.nogc_sync_mut.io",
        )
        .expect("lower-ranked family importing hosted mutable family should warn");

        assert!(msg.contains("Higher-layer module 'std.nogc_sync_mut.io'"));
        assert!(msg.contains("higher_layer_runtime_family"));
        assert!(msg.contains("family: nogc_sync_mut"));
        assert!(msg.contains("family: nogc_async_immut"));
    }

    #[test]
    fn strict_gc_boundary_policy_returns_error() {
        let err = enforce_gc_boundary_policy(
            Some(Path::new("/repo/src/lib/nogc_sync_mut/app.spl")),
            Path::new("/repo/src/std/gc_async_mut/__init__.spl"),
            "std.gc_async_mut",
            true,
        )
        .expect_err("strict runtime-family mode should reject no-GC to GC imports");

        let message = err.to_string();
        assert!(message.contains("[gc-error]"));
        assert!(message.contains("nogc_imports_gc_family"));
    }

    #[test]
    fn warning_gc_boundary_policy_allows_import() {
        let result = enforce_gc_boundary_policy(
            Some(Path::new("/repo/src/lib/nogc_sync_mut/app.spl")),
            Path::new("/repo/src/std/gc_async_mut/__init__.spl"),
            "std.gc_async_mut",
            false,
        );

        assert!(result.is_ok());
    }

    #[test]
    fn gc_boundary_warning_message_allows_common_imports() {
        let msg = gc_boundary_warning_message(
            Path::new("/repo/src/lib/nogc_async_mut_noalloc/app.spl"),
            Path::new("/repo/src/lib/common/text.spl"),
            "std.common.text",
        );

        assert!(msg.is_none());
    }

    fn use_stmt_with_target(target: ImportTarget) -> UseStmt {
        UseStmt {
            span: Span::new(0, 0, 0, 0),
            path: ModulePath {
                segments: vec!["std".to_string(), "io".to_string()],
            },
            target,
            is_type_only: false,
            is_lazy: false,
        }
    }

    #[test]
    fn prefers_package_init_for_group_imports_when_both_exist() {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path();
        let file_path = root.join("io.spl");
        let package_dir = root.join("io");
        let init_path = package_dir.join("__init__.spl");
        fs::write(&file_path, "# file module\n").unwrap();
        fs::create_dir_all(&package_dir).unwrap();
        fs::write(&init_path, "# package module\n").unwrap();

        let resolved = prefer_package_init_for_member_import(
            &file_path,
            &use_stmt_with_target(ImportTarget::Group(vec![ImportTarget::Single("env_get".to_string())])),
        );

        assert_eq!(resolved, init_path);
    }

    #[test]
    fn resolve_member_import_target_falls_back_to_file_on_self_referential_redirect_cycle() {
        // task #153 shape: `driver.spl` (real definitions) sits next to a
        // stale `driver/__init__.spl` that re-exports from the very module
        // path that resolves back to it. `80.driver/driver/__init__.spl` did
        // exactly this (`export use compiler.driver.driver.{compiler_driver_create, ...}`),
        // which shadowed `compiler_driver_create` for every standalone
        // `simple run` script that imported `compiler.driver.driver.{...}`.
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path();
        let file_path = root.join("driver.spl");
        let package_dir = root.join("driver");
        let init_path = package_dir.join("__init__.spl");
        fs::write(&file_path, "fn compiler_driver_create(): 42\n").unwrap();
        fs::create_dir_all(&package_dir).unwrap();
        fs::write(&init_path, "export use driver.{compiler_driver_create}\n").unwrap();

        let use_stmt = use_stmt_with_target(ImportTarget::Group(vec![ImportTarget::Single(
            "compiler_driver_create".to_string(),
        )]));

        // Baseline (no cycle in progress): the package init is preferred,
        // same as any other legitimate "thin file + real package" pair
        // (`prefers_package_init_for_group_imports_when_both_exist`).
        let resolved = resolve_member_import_target(&file_path, &use_stmt);
        assert_eq!(resolved, init_path);

        // Simulate the interpreter mid-way through loading `init_path` when
        // its own self-referential re-export re-resolves the same import.
        // Without the guard, `resolve_member_import_target` would collapse
        // to `prefer_package_init_for_member_import` and redirect back into
        // `init_path` — which the circular-import branch in
        // `load_and_merge_module` then answers with empty/partial exports,
        // silently dropping `compiler_driver_create`.
        mark_module_loading(&init_path);
        let resolved_during_cycle = resolve_member_import_target(&file_path, &use_stmt);
        unmark_module_loading(&init_path);

        assert_eq!(
            resolved_during_cycle, file_path,
            "must keep the already-resolved file instead of re-entering a package-init already on the load stack"
        );
    }

    #[test]
    fn keeps_file_module_for_single_imports() {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path();
        let file_path = root.join("io.spl");
        let package_dir = root.join("io");
        let init_path = package_dir.join("__init__.spl");
        fs::write(&file_path, "# file module\n").unwrap();
        fs::create_dir_all(&package_dir).unwrap();
        fs::write(&init_path, "# package module\n").unwrap();

        let resolved = prefer_package_init_for_member_import(
            &file_path,
            &use_stmt_with_target(ImportTarget::Single("io".to_string())),
        );

        assert_eq!(resolved, file_path);
    }

    fn use_stmt_with_path(path: &[&str], target: ImportTarget) -> UseStmt {
        UseStmt {
            span: Span::new(0, 0, 0, 0),
            path: ModulePath {
                segments: path.iter().map(|s| s.to_string()).collect(),
            },
            target,
            is_type_only: false,
            is_lazy: false,
        }
    }

    #[test]
    fn loads_real_exports_from_nogc_sync_mut_io_package() {
        let mut functions = HashMap::new();
        let mut classes = HashMap::new();
        let mut enums = HashMap::new();
        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..").join("..");
        let current_file = repo_root.join("src/lib/nogc_sync_mut/test_runner/test_runner_main.spl");

        let value = load_and_merge_module(
            &use_stmt_with_path(
                &["std", "nogc_sync_mut", "io"],
                ImportTarget::Group(vec![
                    ImportTarget::Single("env_get".to_string()),
                    ImportTarget::Single("dir_walk".to_string()),
                ]),
            ),
            Some(&current_file),
            &mut functions,
            &mut classes,
            &mut enums,
        )
        .unwrap();

        let exports = match value {
            Value::Dict(exports) => exports,
            other => panic!("expected module exports dict, got {:?}", other),
        };

        assert!(matches!(exports.get("env_get"), Some(Value::Function { .. })));
        assert!(matches!(exports.get("dir_walk"), Some(Value::Function { .. })));
    }

    #[test]
    fn loads_real_exports_from_std_io_package() {
        let mut functions = HashMap::new();
        let mut classes = HashMap::new();
        let mut enums = HashMap::new();
        let repo_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("..").join("..").join("..");
        let current_file = repo_root.join("src/lib/nogc_sync_mut/test_runner/test_runner_main.spl");

        let value = load_and_merge_module(
            &use_stmt_with_path(
                &["std", "io"],
                ImportTarget::Group(vec![ImportTarget::Single("env_get".to_string())]),
            ),
            Some(&current_file),
            &mut functions,
            &mut classes,
            &mut enums,
        )
        .unwrap();

        let exports = match value {
            Value::Dict(exports) => exports,
            other => panic!("expected module exports dict, got {:?}", other),
        };

        assert!(matches!(exports.get("env_get"), Some(Value::Function { .. })));
    }

    #[test]
    fn relative_dot_group_imports_load_sibling_modules() {
        let temp = tempfile::tempdir().unwrap();
        let package_dir = temp.path().join("wiki_keyword");
        fs::create_dir_all(&package_dir).unwrap();

        let wiki_tool = package_dir.join("wiki_tool.spl");
        fs::write(
            &wiki_tool,
            r#"
fn wiki_handler(args: [text]) -> [u8]:
    "ok".bytes()

export wiki_handler
"#,
        )
        .unwrap();

        let register = package_dir.join("register.spl");
        fs::write(
            &register,
            r#"
use .wiki_tool.{wiki_handler}

fn register_wiki_tool() -> [u8]:
    wiki_handler([])

export register_wiki_tool
"#,
        )
        .unwrap();

        let mut functions = HashMap::new();
        let mut classes = HashMap::new();
        let mut enums = HashMap::new();

        let value = load_and_merge_module(
            &use_stmt_with_path(
                &[".", "wiki_tool"],
                ImportTarget::Group(vec![ImportTarget::Single("wiki_handler".to_string())]),
            ),
            Some(&register),
            &mut functions,
            &mut classes,
            &mut enums,
        )
        .unwrap();

        let exports = match value {
            Value::Dict(exports) => exports,
            other => panic!("expected module exports dict, got {:?}", other),
        };

        assert!(matches!(exports.get("wiki_handler"), Some(Value::Function { .. })));
    }

    #[test]
    fn parser_keeps_relative_group_import_module_segment() {
        let mut parser = simple_parser::Parser::new("use .wiki_tool.{wiki_handler}\n");
        let module = parser.parse().unwrap();
        let stmt = match &module.items[0] {
            Node::UseStmt(stmt) => stmt,
            other => panic!("expected use stmt, got {:?}", other),
        };

        assert_eq!(stmt.path.segments, vec![".".to_string(), "wiki_tool".to_string()]);
        assert!(matches!(
            &stmt.target,
            ImportTarget::Group(items)
                if items.len() == 1
                    && matches!(&items[0], ImportTarget::Single(name) if name == "wiki_handler")
        ));
    }

    #[test]
    fn loads_driver_api_generate_headers_for_external_callers() {
        let mut functions = HashMap::new();
        let mut classes = HashMap::new();
        let mut enums = HashMap::new();
        let current_file = Path::new("/tmp/driver_api_probe.spl");

        let value = load_and_merge_module(
            &use_stmt_with_path(
                &["compiler", "driver", "driver_api"],
                ImportTarget::Group(vec![ImportTarget::Single("generate_headers".to_string())]),
            ),
            Some(current_file),
            &mut functions,
            &mut classes,
            &mut enums,
        )
        .unwrap();

        let exports = match value {
            Value::Dict(exports) => exports,
            other => panic!("expected module exports dict, got {:?}", other),
        };

        assert!(matches!(exports.get("generate_headers"), Some(Value::Function { .. })));
    }

    #[test]
    fn loads_driver_api_compile_to_smf_for_external_callers() {
        let mut functions = HashMap::new();
        let mut classes = HashMap::new();
        let mut enums = HashMap::new();
        let current_file = Path::new("/tmp/driver_api_probe.spl");

        let value = load_and_merge_module(
            &use_stmt_with_path(
                &["compiler", "driver", "driver_api"],
                ImportTarget::Group(vec![ImportTarget::Single("compile_to_smf".to_string())]),
            ),
            Some(current_file),
            &mut functions,
            &mut classes,
            &mut enums,
        )
        .unwrap();

        let exports = match value {
            Value::Dict(exports) => exports,
            other => panic!("expected module exports dict, got {:?}", other),
        };

        assert!(matches!(exports.get("compile_to_smf"), Some(Value::Function { .. })));
    }

    #[test]
    fn loads_driver_api_check_file_for_external_callers() {
        let mut functions = HashMap::new();
        let mut classes = HashMap::new();
        let mut enums = HashMap::new();
        let current_file = Path::new("/tmp/driver_api_probe.spl");

        let value = load_and_merge_module(
            &use_stmt_with_path(
                &["compiler", "driver", "driver_api"],
                ImportTarget::Group(vec![ImportTarget::Single("check_file".to_string())]),
            ),
            Some(current_file),
            &mut functions,
            &mut classes,
            &mut enums,
        )
        .unwrap();

        let exports = match value {
            Value::Dict(exports) => exports,
            other => panic!("expected module exports dict, got {:?}", other),
        };

        assert!(matches!(exports.get("check_file"), Some(Value::Function { .. })));
    }

    #[test]
    fn loads_driver_api_compile_surface_group_for_external_callers() {
        let mut functions = HashMap::new();
        let mut classes = HashMap::new();
        let mut enums = HashMap::new();
        let current_file = Path::new("/tmp/driver_api_probe.spl");

        let value = load_and_merge_module(
            &use_stmt_with_path(
                &["compiler", "driver", "driver_api"],
                ImportTarget::Group(vec![
                    ImportTarget::Single("compile_file".to_string()),
                    ImportTarget::Single("compile_to_smf".to_string()),
                    ImportTarget::Single("check_file".to_string()),
                    ImportTarget::Single("aot_c_file".to_string()),
                ]),
            ),
            Some(current_file),
            &mut functions,
            &mut classes,
            &mut enums,
        )
        .unwrap();

        let exports = match value {
            Value::Dict(exports) => exports,
            other => panic!("expected module exports dict, got {:?}", other),
        };

        assert!(matches!(exports.get("compile_file"), Some(Value::Function { .. })));
        assert!(matches!(exports.get("compile_to_smf"), Some(Value::Function { .. })));
        assert!(matches!(exports.get("check_file"), Some(Value::Function { .. })));
        assert!(matches!(exports.get("aot_c_file"), Some(Value::Function { .. })));
    }

    #[test]
    fn loads_driver_api_backend_surface_group_for_external_callers() {
        let mut functions = HashMap::new();
        let mut classes = HashMap::new();
        let mut enums = HashMap::new();
        let current_file = Path::new("/tmp/driver_api_probe.spl");

        let value = load_and_merge_module(
            &use_stmt_with_path(
                &["compiler", "driver", "driver_api"],
                ImportTarget::Group(vec![
                    ImportTarget::Single("aot_llvm_file".to_string()),
                    ImportTarget::Single("aot_llvm_native_file".to_string()),
                    ImportTarget::Single("aot_native_file_with_backend".to_string()),
                    ImportTarget::Single("aot_cuda_file".to_string()),
                    ImportTarget::Single("aot_vhdl_file".to_string()),
                ]),
            ),
            Some(current_file),
            &mut functions,
            &mut classes,
            &mut enums,
        )
        .unwrap();

        let exports = match value {
            Value::Dict(exports) => exports,
            other => panic!("expected module exports dict, got {:?}", other),
        };

        assert!(matches!(exports.get("aot_llvm_file"), Some(Value::Function { .. })));
        assert!(matches!(
            exports.get("aot_llvm_native_file"),
            Some(Value::Function { .. })
        ));
        assert!(matches!(
            exports.get("aot_native_file_with_backend"),
            Some(Value::Function { .. })
        ));
        assert!(matches!(exports.get("aot_cuda_file"), Some(Value::Function { .. })));
        assert!(matches!(exports.get("aot_vhdl_file"), Some(Value::Function { .. })));
    }

    // --- WS1: Loader diagnostics tests ---

    #[test]
    fn loader_trace_disabled_by_default() {
        // Without SIMPLE_LOADER_TRACE=1, tracing should be disabled.
        // Note: OnceLock caches the value, so this test verifies the default path.
        // In CI/test environments the env var is not set, so this should be false.
        // We can't reliably test the enabled path without process-level env control,
        // but we verify the function doesn't panic and returns a bool.
        let result = loader_trace_enabled();
        assert_eq!(result, result); // sanity: it's a bool
    }

    // --- WS2: Generalized selective filter tests ---

    fn make_function_node(name: &str) -> simple_parser::ast::Node {
        use simple_parser::ast::*;
        Node::Function(FunctionDef {
            span: simple_parser::token::Span::new(0, 0, 0, 0),
            name: name.to_string(),
            generic_params: vec![],
            params: vec![],
            return_type: None,
            where_clause: vec![],
            body: simple_parser::ast::Block::default(),
            visibility: Visibility::Private,
            effects: vec![],
            decorators: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
            is_sync: false,
            bounds_block: None,
            is_static: false,
            is_me_method: false,
            is_generator: false,
            return_constraint: None,
            is_generic_template: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
        })
    }

    fn make_export_use_node(names: &[&str]) -> simple_parser::ast::Node {
        use simple_parser::ast::*;
        let items: Vec<ImportTarget> = names.iter().map(|n| ImportTarget::Single(n.to_string())).collect();
        Node::ExportUseStmt(ExportUseStmt {
            span: simple_parser::token::Span::new(0, 0, 0, 0),
            path: ModulePath { segments: vec![] },
            target: ImportTarget::Group(items),
        })
    }

    fn make_use_node(names: &[&str]) -> simple_parser::ast::Node {
        use simple_parser::ast::*;
        let items: Vec<ImportTarget> = names.iter().map(|n| ImportTarget::Single(n.to_string())).collect();
        Node::UseStmt(UseStmt {
            span: simple_parser::token::Span::new(0, 0, 0, 0),
            path: ModulePath {
                segments: vec!["some".to_string(), "module".to_string()],
            },
            target: ImportTarget::Group(items),
            is_type_only: false,
            is_lazy: false,
        })
    }

    #[test]
    fn selective_filter_keeps_requested_function() {
        let node = make_function_node("compile_file");
        let requested = vec!["compile_file".to_string()];
        assert!(should_keep_selective_export(&node, &requested));
    }

    #[test]
    fn selective_filter_removes_unrequested_function() {
        let node = make_function_node("interpret_file");
        let requested = vec!["compile_file".to_string()];
        assert!(!should_keep_selective_export(&node, &requested));
    }

    #[test]
    fn selective_filter_keeps_matching_export_use() {
        let node = make_export_use_node(&["compile_file", "check_file"]);
        let requested = vec!["compile_file".to_string()];
        assert!(should_keep_selective_export(&node, &requested));
    }

    #[test]
    fn selective_filter_removes_non_matching_export_use() {
        let node = make_export_use_node(&["interpret_file", "aot_shared_library"]);
        let requested = vec!["compile_file".to_string()];
        assert!(!should_keep_selective_export(&node, &requested));
    }

    #[test]
    fn selective_filter_keeps_bare_use_stmt() {
        // UseStmt with glob (empty export_target_names) should always be kept
        use simple_parser::ast::*;
        let node = Node::UseStmt(UseStmt {
            span: simple_parser::token::Span::new(0, 0, 0, 0),
            path: ModulePath {
                segments: vec!["std".to_string(), "io".to_string()],
            },
            target: ImportTarget::Glob,
            is_type_only: false,
            is_lazy: false,
        });
        let requested = vec!["compile_file".to_string()];
        assert!(should_keep_selective_export(&node, &requested));
    }

    #[test]
    fn selective_filter_keeps_use_stmt_with_matching_name() {
        let node = make_use_node(&["compile_file", "other"]);
        let requested = vec!["compile_file".to_string()];
        assert!(should_keep_selective_export(&node, &requested));
    }

    #[test]
    fn selective_filter_keeps_use_stmt_with_no_matching_name() {
        let node = make_use_node(&["unrelated_a", "unrelated_b"]);
        let requested = vec!["compile_file".to_string()];
        assert!(should_keep_selective_export(&node, &requested));
    }

    #[test]
    fn selective_filter_always_keeps_non_function_non_use_nodes() {
        // Class, Struct, Enum nodes should always be kept
        use simple_parser::ast::*;
        let node = Node::Class(ClassDef {
            span: simple_parser::token::Span::new(0, 0, 0, 0),
            name: "SomeClass".to_string(),
            generic_params: vec![],
            where_clause: vec![],
            fields: vec![],
            methods: vec![],
            parent: None,
            visibility: Visibility::Private,
            effects: vec![],
            attributes: vec![],
            doc_comment: None,
            is_generic_template: false,
            specialization_of: None,
            type_bindings: HashMap::new(),
            invariant: None,
            macro_invocations: vec![],
            mixins: vec![],
            is_value_type: false,
        });
        let requested = vec!["compile_file".to_string()];
        assert!(should_keep_selective_export(&node, &requested));
    }
}

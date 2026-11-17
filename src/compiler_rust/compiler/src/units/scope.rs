//! Library unit suffix scoping — mirrors the pure-Simple rule in
//! `src/compiler/10.frontend/core/unit_scope.spl`.
//!
//! A suffix backed by a library unit module (`src/unit/<org>[.com]/<family>/<sfx>.spl`)
//! is usable only after `use unit.[<org>.]<family>[.{sfx}|.*|.<sfx>]` (org
//! omitted = simple-lang) or a same-file `unit X: T as sfx` declaration.
//! Scope entries are keyed `"<org>/<name>"`. Reset per interpreter run.
//!
//! Per-module scope: `UnitScopeGuard::enter_module` saves the importer's scope,
//! starts the module with an empty scope and restores on drop, so imports recorded
//! while evaluating an imported module never leak across modules (mirrors pure
//! Simple `unit_scope_save`/`unit_scope_restore`).

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use simple_parser::ast::{ImportTarget, UseStmt};

const UNIT_DEFAULT_ORG: &str = "simple-lang";

#[derive(Default)]
struct UnitScope {
    /// `"<org>/<suffix>"` admitted by a selective or bare import.
    names: HashSet<String>,
    /// `"<org>/<family>"` admitted by a bare / glob import.
    families: HashSet<String>,
    /// (`"<org>/<last>"`, note) for imports that admitted nothing (org/family collision).
    ambiguous: Vec<(String, String)>,
}

thread_local! {
    static UNIT_SCOPE: RefCell<UnitScope> = RefCell::new(UnitScope::default());
    /// (root, suffix) -> sorted "<org>/<family>" keys whose unit module defines it.
    static UNIT_FAMILY_CACHE: RefCell<HashMap<(PathBuf, String), Vec<String>>> = RefCell::new(HashMap::new());
    /// Explicit root (tests only); `None` = auto resolution on every lookup.
    static UNIT_LIBRARY_ROOT_OVERRIDE: RefCell<Option<PathBuf>> = const { RefCell::new(None) };
}

/// Clear the per-run scope (called with the other unit registries).
pub fn unit_scope_reset() {
    UNIT_SCOPE.with(|s| *s.borrow_mut() = UnitScope::default());
}

/// RAII per-module scope boundary: saves the current scope, starts the module
/// with an empty one, and restores the saved scope on drop (also on `?` exits).
pub struct UnitScopeGuard {
    saved: Option<UnitScope>,
}

impl UnitScopeGuard {
    pub fn enter_module() -> Self {
        let saved = UNIT_SCOPE.with(|s| std::mem::take(&mut *s.borrow_mut()));
        Self { saved: Some(saved) }
    }
}

impl Drop for UnitScopeGuard {
    fn drop(&mut self) {
        if let Some(saved) = self.saved.take() {
            UNIT_SCOPE.with(|s| *s.borrow_mut() = saved);
        }
    }
}

/// Point lookups at an explicit unit library root (`None` restores auto).
pub fn unit_library_root_set(root: Option<PathBuf>) {
    UNIT_LIBRARY_ROOT_OVERRIDE.with(|c| *c.borrow_mut() = root);
}

/// Unit root for a `$SIMPLE_LIB` value: `<lib>/unit`, or sibling `<src>/unit`
/// when `<lib>` ends in `/lib` (same as `unit_library_root_from_simple_lib`).
pub fn unit_library_root_from_simple_lib(simple_lib: &str) -> Option<PathBuf> {
    let lib = simple_lib.replace('\\', "/");
    let lib = lib.trim_end_matches('/');
    if lib.is_empty() {
        return None;
    }
    let lib = Path::new(lib);
    let direct = lib.join("unit");
    if direct.is_dir() {
        return Some(direct);
    }
    if lib.file_name().map(|n| n == "lib").unwrap_or(false) {
        let sibling = lib.parent()?.join("unit");
        if sibling.is_dir() {
            return Some(sibling);
        }
    }
    None
}

/// Resolved on every call (not frozen per thread): override, then the
/// worktree `src/unit`, then `$SIMPLE_LIB`.
fn unit_library_root() -> Option<PathBuf> {
    if let Some(p) = UNIT_LIBRARY_ROOT_OVERRIDE.with(|c| c.borrow().clone()) {
        return if p.is_dir() { Some(p) } else { None };
    }
    if let Some(p) = super::registry::find_unit_tree_root().and_then(|p| p.parent().map(Path::to_path_buf)) {
        return Some(p);
    }
    std::env::var("SIMPLE_LIB").ok().and_then(|lib| unit_library_root_from_simple_lib(&lib))
}

fn sorted_dir_names(dir: &Path) -> Vec<String> {
    let mut out: Vec<String> = std::fs::read_dir(dir)
        .map(|rd| {
            rd.filter_map(|e| e.ok())
                .filter(|e| e.path().is_dir())
                .map(|e| e.file_name().to_string_lossy().into_owned())
                .collect()
        })
        .unwrap_or_default();
    out.sort();
    out
}

fn unit_org_name(org_dir: &str) -> &str {
    org_dir.strip_suffix(".com").unwrap_or(org_dir)
}

fn is_primitive_numeric_suffix(suffix: &str) -> bool {
    matches!(
        suffix,
        "i8" | "i16" | "i32" | "i64" | "i128" | "u8" | "u16" | "u32" | "u64" | "u128" | "isize" | "usize" | "f16" | "f32" | "f64"
    )
}

/// True when `<root>/<org>[.com]/<rest>` exists as a module or directory.
fn unit_path_exists(root: &Path, org_dir_base: &str, rest: &[String]) -> bool {
    if rest.is_empty() {
        return false;
    }
    let joined = rest.join("/");
    [org_dir_base.to_string(), format!("{}.com", org_dir_base)].iter().any(|dir| {
        let base = root.join(dir).join(&joined);
        PathBuf::from(format!("{}.spl", base.display())).is_file() || base.exists()
    })
}

/// Org of a `unit.<...>` import (`segs` include "unit"), or `None` when the
/// path names both an org dir and a simple-lang family (ambiguous: admits nothing).
fn unit_import_org(scope: &mut UnitScope, segs: &[String], module_path: &str) -> Option<String> {
    if segs.len() < 3 {
        return Some(UNIT_DEFAULT_ORG.to_string());
    }
    let cand = &segs[1];
    if cand == UNIT_DEFAULT_ORG || *cand == format!("{}.com", UNIT_DEFAULT_ORG) {
        return Some(UNIT_DEFAULT_ORG.to_string());
    }
    let Some(root) = unit_library_root() else {
        return Some(UNIT_DEFAULT_ORG.to_string());
    };
    let orgs = sorted_dir_names(&root);
    if !orgs.iter().any(|o| o == cand || *o == format!("{}.com", cand)) {
        return Some(UNIT_DEFAULT_ORG.to_string());
    }
    let mut rest: &[String] = &segs[2..];
    if rest.first().map(String::as_str) == Some("com") {
        rest = &rest[1..];
    }
    let org_hit = unit_path_exists(&root, cand, rest);
    let default_hit = unit_path_exists(&root, UNIT_DEFAULT_ORG, &segs[1..]);
    if org_hit && default_hit {
        scope.ambiguous.push((
            format!("{}/{}", unit_org_name(cand), segs[segs.len() - 1]),
            format!(
                "`use {}` is ambiguous: both org '{}' and simple-lang family '{}' provide it",
                module_path, cand, cand
            ),
        ));
        return None;
    }
    if default_hit && !org_hit {
        return Some(UNIT_DEFAULT_ORG.to_string());
    }
    Some(unit_org_name(cand).to_string())
}

/// Record a `use unit.<...>` import. `{a, b}` scopes those suffixes of the
/// import's org; a bare path, `.<x>` or `.*` scopes its last segment as a
/// family and as a suffix.
pub fn unit_scope_record_use(stmt: &UseStmt) {
    let segs = &stmt.path.segments;
    if segs.first().map(String::as_str) != Some("unit") {
        return;
    }
    let mut path: Vec<String> = segs.clone();
    let group: Option<Vec<String>> = match &stmt.target {
        ImportTarget::Group(items) => Some(
            items
                .iter()
                .filter_map(|item| match item {
                    ImportTarget::Single(n) | ImportTarget::Aliased { name: n, .. } => Some(n.clone()),
                    _ => None,
                })
                .collect(),
        ),
        ImportTarget::Single(n) | ImportTarget::Aliased { name: n, .. } => {
            path.push(n.clone());
            None
        }
        ImportTarget::Glob => None,
    };
    let module_path = path.join(".");
    UNIT_SCOPE.with(|s| {
        let mut s = s.borrow_mut();
        let Some(org) = unit_import_org(&mut s, &path, &module_path) else { return };
        match group {
            Some(names) => {
                for n in names {
                    s.names.insert(format!("{}/{}", org, n));
                }
            }
            None => {
                let Some(last) = path.last() else { return };
                let key = format!("{}/{}", org, last);
                s.families.insert(key.clone());
                s.names.insert(key);
            }
        }
    });
}

/// Sorted `"<org>/<family>"` keys whose library unit module defines `suffix`.
pub fn unit_library_families_in(root: &Path, suffix: &str) -> Vec<String> {
    let mut found: Vec<String> = Vec::new();
    for org_dir in sorted_dir_names(root) {
        let org_root = root.join(&org_dir);
        for fam in sorted_dir_names(&org_root) {
            if org_root.join(&fam).join(format!("{}.spl", suffix)).is_file() {
                let key = format!("{}/{}", unit_org_name(&org_dir), fam);
                if !found.contains(&key) {
                    found.push(key);
                }
            }
        }
    }
    found.sort();
    found
}

/// Diagnostic text for an out-of-scope library suffix (exact pure-Simple format).
pub fn unit_suffix_scope_message(suffix: &str, families: &[String]) -> String {
    let hints: Vec<String> = families
        .iter()
        .map(|key| {
            let (org, fam) = key.split_once('/').unwrap_or((UNIT_DEFAULT_ORG, key));
            let prefix = if org == UNIT_DEFAULT_ORG { String::new() } else { format!("{}.", org) };
            format!("`use unit.{}{}.{{{}}}`", prefix, fam, suffix)
        })
        .collect();
    format!(
        "unit suffix '{}' is not in scope; add {} (or declare `unit X: T as {}`)",
        suffix,
        hints.join(" or "),
        suffix
    )
}

/// `None` when `suffix` may be used here, else the diagnostic text.
/// `declared` = a same-file unit declaration provides the suffix.
pub fn unit_suffix_scope_error(suffix: &str, declared: bool) -> Option<String> {
    if is_primitive_numeric_suffix(suffix) || declared {
        return None;
    }
    let Some(root) = unit_library_root() else {
        // Fail closed: without the library tree we cannot prove the suffix is
        // not a library unit.
        return Some(format!(
            "unit suffix '{}' cannot be checked: unit library root not found (looked for src/unit under the working directory and next to $SIMPLE_LIB)",
            suffix
        ));
    };
    let families = UNIT_FAMILY_CACHE.with(|c| {
        c.borrow_mut()
            .entry((root.clone(), suffix.to_string()))
            .or_insert_with(|| unit_library_families_in(&root, suffix))
            .clone()
    });
    if families.is_empty() {
        return None;
    }
    UNIT_SCOPE.with(|s| {
        let s = s.borrow();
        for key in &families {
            let org = key.split_once('/').map(|(o, _)| o).unwrap_or(UNIT_DEFAULT_ORG);
            if s.families.contains(key) || s.names.contains(&format!("{}/{}", org, suffix)) {
                return None;
            }
        }
        let mut msg = unit_suffix_scope_message(suffix, &families);
        for (key, note) in &s.ambiguous {
            if families.contains(key) {
                msg.push_str("; ");
                msg.push_str(note);
            }
        }
        Some(msg)
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::ast::ModulePath;
    use simple_parser::token::Span;

    fn use_stmt(segs: &[&str], target: ImportTarget) -> UseStmt {
        UseStmt {
            span: Span::new(0, 0, 0, 0),
            path: ModulePath::new(segs.iter().map(|s| s.to_string()).collect()),
            target,
            is_type_only: false,
            is_lazy: false,
        }
    }

    fn group(names: &[&str]) -> ImportTarget {
        ImportTarget::Group(names.iter().map(|n| ImportTarget::Single((*n).into())).collect())
    }

    /// Fixture root: simple-lang/{velocity/kmph, acme/speed} and acme/speed/kmph.
    fn fixture_root(tag: &str) -> PathBuf {
        let root = std::env::temp_dir().join(format!("seed-unit-scope-{}-{}", tag, std::process::id()));
        let _ = std::fs::remove_dir_all(&root);
        for p in ["simple-lang/velocity/kmph.spl", "simple-lang/acme/speed/kmph.spl", "acme/speed/kmph.spl"] {
            let f = root.join(p);
            std::fs::create_dir_all(f.parent().unwrap()).unwrap();
            std::fs::write(&f, "").unwrap();
        }
        root
    }

    #[test]
    fn unscoped_library_suffix_errors_with_hint() {
        unit_library_root_set(None);
        unit_scope_reset();
        let err = unit_suffix_scope_error("kmph", false).expect("kmph must be out of scope");
        assert!(
            err.starts_with(
                "unit suffix 'kmph' is not in scope; add `use unit.composite.{kmph}` or `use unit.velocity.{kmph}`"
            ),
            "{}",
            err
        );
        assert!(err.ends_with("(or declare `unit X: T as kmph`)"), "{}", err);
    }

    #[test]
    fn group_import_scopes_suffix() {
        unit_library_root_set(None);
        unit_scope_reset();
        unit_scope_record_use(&use_stmt(&["unit", "velocity"], group(&["kmph"])));
        assert_eq!(unit_suffix_scope_error("kmph", false), None);
    }

    #[test]
    fn glob_and_bare_family_import_scope_family() {
        unit_library_root_set(None);
        unit_scope_reset();
        unit_scope_record_use(&use_stmt(&["unit", "velocity"], ImportTarget::Glob));
        assert_eq!(unit_suffix_scope_error("kmph", false), None);
        unit_scope_reset();
        unit_scope_record_use(&use_stmt(&["unit"], ImportTarget::Single("velocity".into())));
        assert_eq!(unit_suffix_scope_error("kmph", false), None);
    }

    #[test]
    fn other_family_import_does_not_scope() {
        unit_library_root_set(None);
        unit_scope_reset();
        unit_scope_record_use(&use_stmt(&["unit", "length"], ImportTarget::Glob));
        assert!(unit_suffix_scope_error("kmph", false).is_some());
    }

    #[test]
    fn declaration_primitive_and_non_library_suffix_pass() {
        unit_library_root_set(None);
        unit_scope_reset();
        assert_eq!(unit_suffix_scope_error("kmph", true), None);
        assert_eq!(unit_suffix_scope_error("zz_not_a_library_unit", false), None);
        assert_eq!(unit_suffix_scope_error("i64", false), None);
    }

    #[test]
    fn message_uses_org_prefix_for_non_default_org() {
        let fams = vec!["acme/speed".to_string(), "simple-lang/velocity".to_string()];
        assert_eq!(
            unit_suffix_scope_message("kmph", &fams),
            "unit suffix 'kmph' is not in scope; add `use unit.acme.speed.{kmph}` or `use unit.velocity.{kmph}` (or declare `unit X: T as kmph`)"
        );
    }

    // Item 1: a selective import from another org must not admit the simple-lang suffix.
    #[test]
    fn org_selective_import_does_not_admit_default_org_suffix() {
        let root = fixture_root("orgkey");
        std::fs::remove_dir_all(root.join("simple-lang/acme")).unwrap();
        unit_library_root_set(Some(root.clone()));
        unit_scope_reset();
        unit_scope_record_use(&use_stmt(&["unit", "acme", "speed"], group(&["kmph"])));
        // acme/speed/kmph is admitted, so the shared suffix passes via acme...
        assert_eq!(unit_suffix_scope_error("kmph", false), None);
        // ...but with only simple-lang/velocity defining it, acme's import admits nothing.
        std::fs::remove_dir_all(root.join("acme/speed")).unwrap();
        std::fs::create_dir_all(root.join("acme/speed")).unwrap();
        UNIT_FAMILY_CACHE.with(|c| c.borrow_mut().clear());
        let err = unit_suffix_scope_error("kmph", false).expect("simple-lang kmph must stay out of scope");
        assert!(err.contains("`use unit.velocity.{kmph}`"), "{}", err);
        unit_library_root_set(None);
        let _ = std::fs::remove_dir_all(&root);
    }

    // Item 2: org dir and simple-lang family both providing the path is ambiguous.
    #[test]
    fn org_family_collision_admits_nothing_and_notes_it() {
        let root = fixture_root("ambig");
        unit_library_root_set(Some(root.clone()));
        unit_scope_reset();
        unit_scope_record_use(&use_stmt(&["unit", "acme", "speed"], group(&["kmph"])));
        let err = unit_suffix_scope_error("kmph", false).expect("ambiguous import admits nothing");
        assert!(
            err.contains("; `use unit.acme.speed` is ambiguous: both org 'acme' and simple-lang family 'acme' provide it"),
            "{}",
            err
        );
        unit_library_root_set(None);
        let _ = std::fs::remove_dir_all(&root);
    }

    // Item 2: an explicit simple-lang org segment routes to the default org.
    #[test]
    fn explicit_simple_lang_org_is_default_org() {
        let root = fixture_root("dflt");
        unit_library_root_set(Some(root.clone()));
        unit_scope_reset();
        unit_scope_record_use(&use_stmt(&["unit", "simple-lang", "velocity"], group(&["kmph"])));
        assert_eq!(unit_suffix_scope_error("kmph", false), None);
        assert_eq!(unit_org_name("simple-lang.com"), "simple-lang");
        unit_library_root_set(None);
        let _ = std::fs::remove_dir_all(&root);
    }

    // Item 5: $SIMPLE_LIB fallback and per-call root resolution.
    #[test]
    fn simple_lib_fallback_and_root_not_frozen() {
        let root = fixture_root("lib");
        let src = root.parent().unwrap().join(format!("seed-unit-scope-src-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&src);
        std::fs::create_dir_all(src.join("lib")).unwrap();
        std::fs::create_dir_all(src.join("unit")).unwrap();
        assert_eq!(unit_library_root_from_simple_lib(&src.display().to_string()), Some(src.join("unit")));
        assert_eq!(
            unit_library_root_from_simple_lib(&format!("{}/lib/", src.display())),
            Some(src.join("unit"))
        );
        assert_eq!(unit_library_root_from_simple_lib(""), None);
        // Root is re-resolved per call: switching the override changes the answer.
        unit_scope_reset();
        unit_library_root_set(Some(src.join("unit")));
        assert_eq!(unit_suffix_scope_error("kmph", false), None);
        unit_library_root_set(Some(root.clone()));
        assert!(unit_suffix_scope_error("kmph", false).is_some());
        unit_library_root_set(Some(src.join("missing")));
        assert!(unit_suffix_scope_error("kmph", false).unwrap().contains("cannot be checked"));
        unit_library_root_set(None);
        let _ = std::fs::remove_dir_all(&root);
        let _ = std::fs::remove_dir_all(&src);
    }
}

#[cfg(test)]
mod module_scope_tests {
    use super::*;
    use simple_parser::ast::ModulePath;
    use simple_parser::token::Span;

    fn use_group(names: &[&str]) -> UseStmt {
        UseStmt {
            span: Span::new(0, 0, 0, 0),
            path: ModulePath::new(vec!["unit".into(), "velocity".into()]),
            target: ImportTarget::Group(names.iter().map(|n| ImportTarget::Single((*n).into())).collect()),
            is_type_only: false,
            is_lazy: false,
        }
    }

    fn in_scope(sfx: &str) -> bool {
        UNIT_SCOPE.with(|s| s.borrow().names.contains(&format!("{}/{}", UNIT_DEFAULT_ORG, sfx)))
    }

    #[test]
    fn imported_module_scope_does_not_leak_into_importer() {
        unit_scope_reset();
        unit_scope_record_use(&use_group(&["kmph"]));
        {
            let _g = UnitScopeGuard::enter_module();
            assert!(!in_scope("kmph"), "importer scope must not leak into module");
            unit_scope_record_use(&use_group(&["mph"]));
            assert!(in_scope("mph"));
        }
        assert!(in_scope("kmph"), "importer scope restored");
        assert!(!in_scope("mph"), "module import must not leak to importer");
        unit_scope_reset();
    }
}

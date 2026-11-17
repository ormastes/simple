//! Library unit suffix scoping — mirrors the pure-Simple rule in
//! `src/compiler/10.frontend/core/interpreter/eval_units.spl`.
//!
//! A suffix backed by a library unit module (`src/unit/<org>[.com]/<family>/<sfx>.spl`)
//! is usable only after `use unit.[<org>.]<family>[.{sfx}|.*|.<sfx>]` (org
//! omitted = simple-lang) or a same-file `unit X: T as sfx` declaration.
//! Families are tracked as `"<org>/<family>"`. Reset per interpreter run.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};

use simple_parser::ast::{ImportTarget, UseStmt};

const UNIT_DEFAULT_ORG: &str = "simple-lang";

#[derive(Default)]
struct UnitScope {
    names: HashSet<String>,
    families: HashSet<String>,
}

thread_local! {
    static UNIT_SCOPE: RefCell<UnitScope> = RefCell::new(UnitScope::default());
    /// suffix -> sorted "<org>/<family>" keys whose unit module defines it.
    static UNIT_FAMILY_CACHE: RefCell<HashMap<String, Vec<String>>> = RefCell::new(HashMap::new());
    /// `src/unit` root, resolved once per thread (None = not found).
    static UNIT_LIBRARY_ROOT: RefCell<Option<Option<PathBuf>>> = const { RefCell::new(None) };
}

/// Clear the per-run scope (called with the other unit registries).
pub fn unit_scope_reset() {
    UNIT_SCOPE.with(|s| *s.borrow_mut() = UnitScope::default());
}

fn unit_library_root() -> Option<PathBuf> {
    UNIT_LIBRARY_ROOT.with(|cell| {
        cell.borrow_mut()
            .get_or_insert_with(|| super::registry::find_unit_tree_root().and_then(|p| p.parent().map(Path::to_path_buf)))
            .clone()
    })
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

fn org_name(org_dir: &str) -> &str {
    org_dir.strip_suffix(".com").unwrap_or(org_dir)
}

/// Record a `use unit.<...>` import. `{a, b}` scopes those suffixes; a bare
/// path, `.<x>` or `.*` scopes its last segment as a family and as a suffix.
pub fn unit_scope_record_use(stmt: &UseStmt) {
    let segs = &stmt.path.segments;
    if segs.first().map(String::as_str) != Some("unit") {
        return;
    }
    let mut path: Vec<String> = segs.clone();
    match &stmt.target {
        ImportTarget::Group(items) => {
            UNIT_SCOPE.with(|s| {
                let mut s = s.borrow_mut();
                for item in items {
                    match item {
                        ImportTarget::Single(n) | ImportTarget::Aliased { name: n, .. } => {
                            s.names.insert(n.clone());
                        }
                        _ => {}
                    }
                }
            });
            return;
        }
        ImportTarget::Single(n) | ImportTarget::Aliased { name: n, .. } => path.push(n.clone()),
        ImportTarget::Glob => {}
    }
    let Some(last) = path.last().cloned() else { return };
    let mut org = UNIT_DEFAULT_ORG.to_string();
    if path.len() >= 3 {
        if let Some(root) = unit_library_root() {
            let orgs = sorted_dir_names(&root);
            let seg = &path[1];
            if orgs.iter().any(|o| o == seg || *o == format!("{}.com", seg)) {
                org = seg.clone();
            }
        }
    }
    UNIT_SCOPE.with(|s| {
        let mut s = s.borrow_mut();
        s.families.insert(format!("{}/{}", org, last));
        s.names.insert(last);
    });
}

/// Sorted `"<org>/<family>"` keys whose library unit module defines `suffix`.
pub fn unit_library_families_in(root: &Path, suffix: &str) -> Vec<String> {
    let mut found: Vec<String> = Vec::new();
    for org_dir in sorted_dir_names(root) {
        let org_root = root.join(&org_dir);
        for fam in sorted_dir_names(&org_root) {
            if org_root.join(&fam).join(format!("{}.spl", suffix)).is_file() {
                let key = format!("{}/{}", org_name(&org_dir), fam);
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
/// `declared` = a same-file `unit X: T as suffix` declaration exists.
pub fn unit_suffix_scope_error(suffix: &str, declared: bool) -> Option<String> {
    if declared || UNIT_SCOPE.with(|s| s.borrow().names.contains(suffix)) {
        return None;
    }
    let Some(root) = unit_library_root() else {
        // Fail closed: without the library tree we cannot prove the suffix is
        // not a library unit.
        return Some(format!(
            "unit suffix '{}' scope check failed: unit library root `src/unit` not found (set SIMPLE_UNIT_TREE_ROOT)",
            suffix
        ));
    };
    let families = UNIT_FAMILY_CACHE.with(|c| {
        c.borrow_mut()
            .entry(suffix.to_string())
            .or_insert_with(|| unit_library_families_in(&root, suffix))
            .clone()
    });
    if families.is_empty() {
        return None;
    }
    if UNIT_SCOPE.with(|s| families.iter().any(|f| s.borrow().families.contains(f))) {
        return None;
    }
    Some(unit_suffix_scope_message(suffix, &families))
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

    #[test]
    fn unscoped_library_suffix_errors_with_hint() {
        unit_scope_reset();
        let err = unit_suffix_scope_error("kmph", false).expect("kmph must be out of scope");
        // kmph lives in both composite/ and velocity/: one hint per family, sorted.
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
        unit_scope_reset();
        unit_scope_record_use(&use_stmt(&["unit", "velocity"], ImportTarget::Group(vec![ImportTarget::Single("kmph".into())])));
        assert_eq!(unit_suffix_scope_error("kmph", false), None);
    }

    #[test]
    fn glob_and_bare_family_import_scope_family() {
        unit_scope_reset();
        unit_scope_record_use(&use_stmt(&["unit", "velocity"], ImportTarget::Glob));
        assert_eq!(unit_suffix_scope_error("kmph", false), None);
        unit_scope_reset();
        unit_scope_record_use(&use_stmt(&["unit"], ImportTarget::Single("velocity".into())));
        assert_eq!(unit_suffix_scope_error("kmph", false), None);
    }

    #[test]
    fn other_family_import_does_not_scope() {
        unit_scope_reset();
        unit_scope_record_use(&use_stmt(&["unit", "length"], ImportTarget::Glob));
        assert!(unit_suffix_scope_error("kmph", false).is_some());
    }

    #[test]
    fn declaration_scopes_and_non_library_suffix_passes() {
        unit_scope_reset();
        assert_eq!(unit_suffix_scope_error("kmph", true), None);
        assert_eq!(unit_suffix_scope_error("zz_not_a_library_unit", false), None);
    }

    #[test]
    fn message_uses_org_prefix_for_non_default_org() {
        let fams = vec!["acme/speed".to_string(), "simple-lang/velocity".to_string()];
        assert_eq!(
            unit_suffix_scope_message("kmph", &fams),
            "unit suffix 'kmph' is not in scope; add `use unit.acme.speed.{kmph}` or `use unit.velocity.{kmph}` (or declare `unit X: T as kmph`)"
        );
    }
}

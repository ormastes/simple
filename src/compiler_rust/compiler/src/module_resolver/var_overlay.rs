//! Variant overlay (`variants/`) candidate-root computation for the resolver.
//!
//! Mirrors the self-hosted logic in
//! `src/compiler/99.loader/module_resolver/var_resolution.spl`. Reads
//! `<project_root>/config/var.sdn` (active profile selections) and
//! `<project_root>/variants/__init__.spl` (group order), and returns the
//! candidate roots in precedence order (selected before default). Returns an
//! empty list when the overlay is not configured, so resolution is unchanged for
//! projects that don't use it. No new grammar: these are SDN-ish data files read
//! with a minimal line parser (the resolver precedes the full SDN parser).

use crate::fs_probe::{p_exists, p_is_dir, p_is_file};
use std::cell::RefCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};

thread_local! {
    /// One entry per project root. The inputs are two data files that are read
    /// in full on every miss; without this memo they were re-read once per
    /// module resolution (measured 132 reads each of `config/var.sdn` and
    /// `variants/__init__.spl` for a single tiny spec run).
    ///
    /// Stamp policy: none, per process — the same policy the module caches next
    /// to this one already use (`IMPORTED_MODULE_AST`, `MODULE_EXPORTS_CACHE`,
    /// and `fs_probe`'s own `PATH_KIND_CACHE` are all plain per-process memos).
    /// Editing `config/var.sdn` mid-process was never picked up by the caches
    /// downstream of it, so this is no weaker than what it replaces.
    static VAR_ROOTS_CACHE: RefCell<HashMap<PathBuf, Vec<PathBuf>>> =
        RefCell::new(HashMap::new());
}

/// Candidate variant roots for a project, absolute, in precedence order
/// (all selected roots, then all group-default roots, then the global default).
pub(crate) fn compute_var_roots(project_root: &Path) -> Vec<PathBuf> {
    if let Some(hit) = VAR_ROOTS_CACHE.with(|c| c.borrow().get(project_root).cloned()) {
        return hit;
    }
    // The borrow is dropped before the computation and re-taken to insert, so a
    // fill can never re-enter a live borrow.
    let roots = compute_var_roots_uncached(project_root);
    VAR_ROOTS_CACHE.with(|c| {
        c.borrow_mut()
            .insert(project_root.to_path_buf(), roots.clone())
    });
    roots
}

/// Test hook: drop the memo so a fixture can rewrite `config/var.sdn` and
/// `variants/__init__.spl` between calls in one process.
#[cfg(test)]
pub(crate) fn clear_var_roots_cache_for_tests() {
    VAR_ROOTS_CACHE.with(|c| c.borrow_mut().clear());
}

fn compute_var_roots_uncached(project_root: &Path) -> Vec<PathBuf> {
    let variants_dir = project_root.join("variants");
    if !p_is_dir(&variants_dir) {
        return Vec::new();
    }
    let cfg = match std::fs::read_to_string(project_root.join("config").join("var.sdn")) {
        Ok(s) => s,
        Err(_) => return Vec::new(),
    };
    let selections = parse_active_profile(&cfg);
    if selections.is_empty() {
        return Vec::new();
    }
    let order = read_group_order(&variants_dir);

    // Iterate manifest order first, then any selection groups not listed there.
    let mut groups: Vec<String> = Vec::new();
    for g in &order {
        if selections.iter().any(|(k, _)| k == g) {
            groups.push(g.clone());
        }
    }
    for (k, _) in &selections {
        if !groups.contains(k) {
            groups.push(k.clone());
        }
    }

    let mut selected: Vec<PathBuf> = Vec::new();
    let mut defaults: Vec<PathBuf> = Vec::new();
    for g in &groups {
        let value = selections
            .iter()
            .find(|(k, _)| k == g)
            .map(|(_, v)| v.clone())
            .unwrap_or_else(|| "default".to_string());
        let gdir = g.replace('.', "/");
        // `auto` has no host detection here -> treat as the group default.
        if value != "default" && value != "auto" {
            selected.push(variants_dir.join(&gdir).join(&value));
        }
        defaults.push(variants_dir.join(&gdir).join("default"));
    }

    let mut roots = Vec::new();
    roots.extend(selected);
    roots.extend(defaults);
    roots.push(variants_dir.join("default"));
    roots
}

/// Parse the active profile's `{ k: v, ... }` line into (group, value) pairs.
fn parse_active_profile(cfg: &str) -> Vec<(String, String)> {
    let mut active = String::new();
    for line in cfg.lines() {
        let t = line.trim();
        if let Some(rest) = t.strip_prefix("profile:") {
            active = rest.trim().to_string();
        }
    }
    if active.is_empty() {
        return Vec::new();
    }
    let prefix = format!("{active}:");
    for line in cfg.lines() {
        let t = line.trim();
        if t.starts_with(&prefix) && t.contains('{') {
            return parse_inline_pairs(t);
        }
    }
    Vec::new()
}

fn parse_inline_pairs(line: &str) -> Vec<(String, String)> {
    let inner = match (line.find('{'), line.rfind('}')) {
        (Some(a), Some(b)) if b > a => &line[a + 1..b],
        _ => return Vec::new(),
    };
    let mut out = Vec::new();
    for pair in inner.split(',') {
        if let Some((k, v)) = pair.split_once(':') {
            let (k, v) = (k.trim(), v.trim());
            if !k.is_empty() && !v.is_empty() {
                out.push((k.to_string(), v.to_string()));
            }
        }
    }
    out
}

/// Read `order: [a, b, c]` from `variants/__init__.spl`; empty if absent.
fn read_group_order(variants_dir: &Path) -> Vec<String> {
    let manifest_path = variants_dir.join("__init__.spl");
    let manifest = match crate::read_trace::rts(file!(), line!(), &manifest_path) {
        Ok(s) => s,
        Err(_) => return Vec::new(),
    };
    for line in manifest.lines() {
        let t = line.trim();
        if t.starts_with("order:") {
            if let (Some(a), Some(b)) = (t.find('['), t.find(']')) {
                if b > a {
                    return t[a + 1..b]
                        .split(',')
                        .map(|s| s.trim().to_string())
                        .filter(|s| !s.is_empty())
                        .collect();
                }
            }
        }
    }
    Vec::new()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn write_project(dir: &Path, profile: &str, order: &str) {
        fs::create_dir_all(dir.join("config")).unwrap();
        fs::create_dir_all(dir.join("variants")).unwrap();
        fs::write(dir.join("config").join("var.sdn"), profile).unwrap();
        fs::write(dir.join("variants").join("__init__.spl"), order).unwrap();
    }

    #[test]
    fn var_roots_are_computed_once_per_project_root() {
        let temp = tempfile::tempdir().unwrap();
        let root = temp.path();
        write_project(
            root,
            "profile: dev\ndev: { hw: board, lib: crypto }\n",
            "order: [hw, lib]\n",
        );
        clear_var_roots_cache_for_tests();

        let first = compute_var_roots(root);
        assert_eq!(
            first,
            vec![
                root.join("variants").join("hw").join("board"),
                root.join("variants").join("lib").join("crypto"),
                root.join("variants").join("hw").join("default"),
                root.join("variants").join("lib").join("default"),
                root.join("variants").join("default"),
            ]
        );

        // Rewriting the inputs must NOT change the answer within the process:
        // the memo is the documented per-process policy, and proving it here is
        // what keeps that policy from being re-broken by accident.
        fs::write(root.join("config").join("var.sdn"), "profile: dev\ndev: { hw: other }\n").unwrap();
        assert_eq!(compute_var_roots(root), first);

        clear_var_roots_cache_for_tests();
        assert_eq!(
            compute_var_roots(root),
            vec![
                root.join("variants").join("hw").join("other"),
                root.join("variants").join("hw").join("default"),
                root.join("variants").join("default"),
            ]
        );
    }

    #[test]
    fn memo_is_keyed_by_project_root_not_shared_across_projects() {
        let a = tempfile::tempdir().unwrap();
        let b = tempfile::tempdir().unwrap();
        write_project(a.path(), "profile: p\np: { hw: alpha }\n", "order: [hw]\n");
        write_project(b.path(), "profile: p\np: { hw: beta }\n", "order: [hw]\n");
        clear_var_roots_cache_for_tests();

        assert_eq!(
            compute_var_roots(a.path())[0],
            a.path().join("variants").join("hw").join("alpha")
        );
        assert_eq!(
            compute_var_roots(b.path())[0],
            b.path().join("variants").join("hw").join("beta")
        );
    }

    #[test]
    fn a_project_without_a_variants_dir_has_no_roots() {
        let temp = tempfile::tempdir().unwrap();
        clear_var_roots_cache_for_tests();
        assert!(compute_var_roots(temp.path()).is_empty());
    }
}

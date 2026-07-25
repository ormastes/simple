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

use std::path::{Path, PathBuf};

/// Candidate variant roots for a project, absolute, in precedence order
/// (all selected roots, then all group-default roots, then the global default).
pub(crate) fn compute_var_roots(project_root: &Path) -> Vec<PathBuf> {
    let variants_dir = project_root.join("variants");
    if !variants_dir.is_dir() {
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
    let manifest = match std::fs::read_to_string(variants_dir.join("__init__.spl")) {
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

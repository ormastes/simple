//! AST-level function reachability for the seed JIT, run before HIR lowering.
//!
//! `run_file_jit` flattens the whole import closure into one AST and lowers
//! every function to HIR and MIR before [`super::retain_reachable_functions`]
//! drops the unreachable ones. Measured 2026-11-28 on
//! `scripts/tool/riscv64-unknown-elf-tool-wrapper.spl`: 1,283 functions
//! lowered, 174 reachable, ~400 ms of HIR+MIR spent on the rest.
//! [`retain_reachable_ast_functions`] drops those bodies first.
//!
//! # Soundness rule
//!
//! This pass must never drop a function the MIR pass would keep, so it is
//! strictly more conservative than it:
//!
//! - Only free module-level functions that came from an IMPORTED file (they
//!   carry the flatten owner attribute, and the owner is not the entry file)
//!   are candidates. The entry file's own functions, every method inside a
//!   class/struct/impl/trait, and every non-function item are kept and are
//!   roots, so diagnostics on the user's own code are unchanged.
//! - A candidate with a decorator, a [`super::reachability::ROOT_ATTRIBUTES`]
//!   attribute, a `__module_init` name, or a name that shadows a codegen
//!   runtime function is a root, as in the MIR pass.
//! - References are every identifier-like word inside a quoted string of a
//!   kept item's `Debug` text: every name the AST carries is a `String`, so
//!   identifiers, paths and string-literal contents (by-name dispatch) are all
//!   seen; bare field and variant names are not. Both the
//!   reference and the definition are expanded with the MIR pass's
//!   `name_keys`, so suffix / `$dup` / `.`-`::`-`__` spellings match the same
//!   way. A word that only *looks* like a reference keeps a function — the
//!   error is always toward keeping.
//! - No `main` at AST level: nothing is pruned (the interpreter path reads
//!   every item).
//!
//! Verified by the invariant that the MIR pass's `reachable=` count is the
//! same with and without this pass (see the guard spec in
//! `test/05_perf/startup/`). `SIMPLE_JIT_AST_PRUNE=0` disables it.

use std::collections::{HashMap, HashSet};
use std::path::Path;

use simple_parser::ast::{FunctionDef, Node};

fn imported_owner(f: &FunctionDef, entry: &str, owners: &mut HashMap<String, bool>) -> bool {
    let Some(raw) = f.attributes.iter().find_map(|a| {
        a.name
            .strip_prefix(crate::interpreter::FLATTEN_MODULE_OWNER_ATTR_PREFIX)
    }) else {
        return false;
    };
    *owners
        .entry(raw.to_string())
        .or_insert_with(|| crate::interpreter::normalize_path_key(Path::new(raw)).to_string_lossy() != entry)
}

fn is_root(f: &FunctionDef) -> bool {
    f.name == "main"
        || f.name.starts_with("__module_init")
        || !f.decorators.is_empty()
        || f.attributes
            .iter()
            .any(|a| super::reachability::ROOT_ATTRIBUTES.contains(&a.name.as_str()))
        || crate::codegen::runtime_sffi::spec_for(&f.name).is_some()
}

/// Contents of every `"..."` in `Debug` text. Every name the AST carries
/// (identifiers, paths, method names, string literals) is a `String`, which
/// `Debug` prints quoted; field and variant names print bare and are skipped.
fn quoted_strings(text: &str) -> Vec<&str> {
    let bytes = text.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        if bytes[i] == b'"' {
            let start = i + 1;
            i += 1;
            while i < bytes.len() && bytes[i] != b'"' {
                i += if bytes[i] == b'\\' { 2 } else { 1 };
            }
            out.push(&text[start..i.min(bytes.len())]);
        }
        i += 1;
    }
    out
}

fn keys_of(name: &str) -> Vec<String> {
    let mut out = Vec::new();
    super::reachability::name_keys(name, &mut out);
    out
}

/// Drop imported free functions no kept item can name. Returns
/// `(before, after)` item counts, or `None` when nothing was attempted.
pub fn retain_reachable_ast_functions(items: &mut Vec<Node>, entry: &Path) -> Option<(usize, usize)> {
    if !items.iter().any(|n| matches!(n, Node::Function(f) if f.name == "main")) {
        return None;
    }
    let entry = crate::interpreter::normalize_path_key(entry)
        .to_string_lossy()
        .to_string();
    let mut owners = HashMap::new();
    let mut keep = vec![true; items.len()];
    let mut by_key: HashMap<String, Vec<usize>> = HashMap::new();
    for (i, item) in items.iter().enumerate() {
        if let Node::Function(f) = item {
            if imported_owner(f, &entry, &mut owners) && !is_root(f) {
                keep[i] = false;
                for k in keys_of(&f.name) {
                    by_key.entry(k).or_default().push(i);
                }
            }
        }
    }
    let mut work: Vec<usize> = (0..items.len()).filter(|&i| keep[i]).collect();
    let mut seen: HashSet<String> = HashSet::new();
    while let Some(i) = work.pop() {
        let text = format!("{:?}", items[i]);
        let is_word = |c: char| c.is_alphanumeric() || matches!(c, '_' | '$' | '.' | ':');
        for quoted in quoted_strings(&text) {
            for word in quoted.split(|c: char| !is_word(c)).filter(|w| !w.is_empty()) {
                if seen.contains(word) {
                    continue;
                }
                seen.insert(word.to_string());
                let mut keys = keys_of(word);
                keys.extend(word.split(['.', ':']).filter(|p| !p.is_empty()).flat_map(keys_of));
                for k in keys {
                    if let Some(idxs) = by_key.get(&k) {
                        for &j in idxs {
                            if !keep[j] {
                                keep[j] = true;
                                work.push(j);
                            }
                        }
                    }
                }
            }
        }
    }
    let before = items.len();
    let mut idx = 0;
    items.retain(|_| {
        idx += 1;
        keep[idx - 1]
    });
    Some((before, items.len()))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn names(items: &[Node]) -> Vec<String> {
        items
            .iter()
            .filter_map(|n| match n {
                Node::Function(f) => Some(f.name.clone()),
                _ => None,
            })
            .collect()
    }

    /// Imported free functions are kept when named from a kept body, a method
    /// body, a closure value or a string literal; an unnamed one is dropped,
    /// and the entry file's own unreferenced function stays.
    #[test]
    fn keeps_every_named_import_and_drops_the_rest() {
        let src = r#"
fn main():
    val f = via_closure
    helper()
    call_by_name("via_string")

fn entry_unused():
    0

fn helper():
    nested()

fn nested():
    1

fn via_closure():
    2

fn via_string():
    3

fn call_by_name(n: text):
    0

class Box:
    fn get() -> i64:
        via_method()

fn via_method():
    4

fn never_named():
    5
"#;
        let mut module = simple_parser::Parser::new(src).parse().expect("parse");
        for item in module.items.iter_mut() {
            if let Node::Function(f) = item {
                let owner = if f.name == "main" || f.name == "entry_unused" {
                    "/entry.spl"
                } else {
                    "/lib/x.spl"
                };
                crate::interpreter::tag_function_module_owner(f, owner);
            }
        }
        let (before, after) =
            retain_reachable_ast_functions(&mut module.items, Path::new("/entry.spl")).expect("has main");
        let kept = names(&module.items);
        assert_eq!(before - after, 1, "only never_named is dropped: {kept:?}");
        assert!(!kept.contains(&"never_named".to_string()));
        for want in [
            "entry_unused",
            "helper",
            "nested",
            "via_closure",
            "via_string",
            "via_method",
        ] {
            assert!(kept.contains(&want.to_string()), "{want} kept: {kept:?}");
        }
    }

    #[test]
    fn no_main_prunes_nothing() {
        let mut module = simple_parser::Parser::new("fn a():\n    0\n").parse().expect("parse");
        assert!(retain_reachable_ast_functions(&mut module.items, Path::new("/e.spl")).is_none());
        assert_eq!(names(&module.items), vec!["a".to_string()]);
    }
}

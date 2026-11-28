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
//!   are candidates. The entry file's own functions and methods and every
//!   non-function item are kept and are roots, so diagnostics on the user's own code are unchanged.
//! - Methods of imported classes/structs/enums and plain (non-trait) impls are
//!   candidates too (each method carries the owner tag). They are taken out of
//!   their containers before the worklist so the container's own text does not
//!   name them, and kept ones are restored in original order. A method is alive
//!   when its bare name appears in any kept item, whatever the receiver type.
//!   Always kept: methods of traits, mixins, actors and trait impls, `__*`
//!   names, and [`IMPLICIT_METHODS`] (names the runtime calls by convention).
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

/// Method names the compiler or runtime calls by convention (operators on
/// `for`/`+`/interpolation, drop, indexing, ...) without the name appearing in
/// the AST. Always kept, as are `__*` names and anything in a trait, mixin,
/// actor or trait impl.
const IMPLICIT_METHODS: &[&str] = &[
    "to_string", "str", "fmt", "debug", "format", "repr", "iter", "into_iter", "next", "has_next", "drop", "close",
    "finalize", "dispose", "eq", "hash", "cmp", "compare", "len", "get", "set", "index", "contains", "call", "clone",
    "default", "new", "init", "unwrap",
];

fn method_is_root(m: &FunctionDef) -> bool {
    m.name.starts_with("__") || IMPLICIT_METHODS.contains(&m.name.as_str()) || is_root(m)
}

/// A pruning candidate taken out of its container: where it came from and the
/// method itself.
struct TakenMethod {
    container: usize,
    position: usize,
    method: FunctionDef,
}

/// Move the candidate methods of `methods` (imported, not roots) out into
/// `taken`, remembering their original position.
fn take_candidates(
    methods: &mut Vec<FunctionDef>,
    container: usize,
    entry: &str,
    owners: &mut HashMap<String, bool>,
    taken: &mut Vec<TakenMethod>,
) {
    let mut position = 0;
    let all = std::mem::take(methods);
    for method in all {
        if imported_owner(&method, entry, owners) && !method_is_root(&method) {
            taken.push(TakenMethod { container, position, method });
        } else {
            methods.push(method);
        }
        position += 1;
    }
}

fn container_methods(item: &mut Node) -> Option<&mut Vec<FunctionDef>> {
    match item {
        Node::Class(c) => Some(&mut c.methods),
        Node::Struct(s) => Some(&mut s.methods),
        Node::Enum(e) => Some(&mut e.methods),
        Node::Impl(i) if i.trait_name.is_none() => Some(&mut i.methods),
        _ => None,
    }
}

/// Drop imported free functions and methods no kept item can name. Returns
/// `(before, after)` counts of free items plus candidate methods, or `None`
/// when nothing was attempted.
///
/// Methods of imported classes, structs, enums and plain (non-trait) impls are
/// candidates; they are taken out of their containers first so a container's
/// own text does not count as naming them, and the survivors are put back in
/// their original order. A method is alive when its bare name appears in any
/// kept item or kept method, whatever the receiver type.
pub fn retain_reachable_ast_functions(items: &mut Vec<Node>, entry: &Path) -> Option<(usize, usize)> {
    if !items.iter().any(|n| matches!(n, Node::Function(f) if f.name == "main")) {
        return None;
    }
    let entry = crate::interpreter::normalize_path_key(entry)
        .to_string_lossy()
        .to_string();
    let mut owners = HashMap::new();
    let mut taken: Vec<TakenMethod> = Vec::new();
    for (ci, item) in items.iter_mut().enumerate() {
        if let Some(methods) = container_methods(item) {
            take_candidates(methods, ci, &entry, &mut owners, &mut taken);
        }
    }
    // Ids `0..n_items` are free items; `n_items + t` is `taken[t]`.
    let n_items = items.len();
    let mut keep = vec![true; n_items + taken.len()];
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
    for (t, tm) in taken.iter().enumerate() {
        keep[n_items + t] = false;
        for k in keys_of(&tm.method.name) {
            by_key.entry(k).or_default().push(n_items + t);
        }
    }
    let mut work: Vec<usize> = (0..keep.len()).filter(|&i| keep[i]).collect();
    let mut seen: HashSet<String> = HashSet::new();
    while let Some(i) = work.pop() {
        let text = if i < n_items {
            format!("{:?}", items[i])
        } else {
            format!("{:?}", taken[i - n_items].method)
        };
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
    let before = n_items + taken.len();
    let mut kept_methods = 0;
    let (mut last_container, mut dropped) = (usize::MAX, 0);
    // Ascending original position per container restores the original order.
    for (t, tm) in taken.into_iter().enumerate() {
        if tm.container != last_container {
            (last_container, dropped) = (tm.container, 0);
        }
        if !keep[n_items + t] {
            dropped += 1;
            continue;
        }
        kept_methods += 1;
        if let Some(methods) = container_methods(&mut items[tm.container]) {
            // Earlier dropped siblings no longer occupy their slots.
            let at = (tm.position - dropped).min(methods.len());
            methods.insert(at, tm.method);
        }
    }
    let mut idx = 0;
    items.retain(|_| {
        idx += 1;
        keep[idx - 1]
    });
    Some((before, items.len() + kept_methods))
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

    fn method_names(items: &[Node], container: &str) -> Vec<String> {
        for n in items {
            match n {
                Node::Class(c) if c.name == container => return c.methods.iter().map(|m| m.name.clone()).collect(),
                Node::Struct(s) if s.name == container => return s.methods.iter().map(|m| m.name.clone()).collect(),
                Node::Enum(e) if e.name == container => return e.methods.iter().map(|m| m.name.clone()).collect(),
                _ => {}
            }
        }
        panic!("no container {container}");
    }

    /// Imported methods are dropped unless their bare name appears in a kept
    /// item or they are on the implicit/dunder/trait keep lists; survivors keep
    /// their original order.
    #[test]
    fn prunes_unused_imported_methods_only() {
        let src = r#"
fn main():
    val b = make()
    b.used_one()

fn make():
    0

class Box:
    fn unused_a() -> i64:
        0
    fn used_one() -> i64:
        chained()
    fn chained() -> i64:
        1
    fn unused_b() -> i64:
        2
    fn len() -> i64:
        3
    fn __enter__() -> i64:
        4

struct Pt:
    x: i64
    fn dead_pt() -> i64:
        0

enum Color:
    Red
    fn dead_enum() -> i64:
        0

impl Pt:
    fn dead_impl() -> i64:
        0

trait Shape:
    fn area() -> i64

impl Shape for Pt:
    fn area() -> i64:
        1
    fn never_called_trait_impl() -> i64:
        2
"#;
        let mut module = simple_parser::Parser::new(src).parse().expect("parse");
        for item in module.items.iter_mut() {
            match item {
                Node::Function(f) if f.name == "main" => crate::interpreter::tag_function_module_owner(f, "/entry.spl"),
                Node::Function(f) => crate::interpreter::tag_function_module_owner(f, "/lib/x.spl"),
                Node::Class(c) => c
                    .methods
                    .iter_mut()
                    .for_each(|m| crate::interpreter::tag_function_module_owner(m, "/lib/x.spl")),
                Node::Struct(s) => s
                    .methods
                    .iter_mut()
                    .for_each(|m| crate::interpreter::tag_function_module_owner(m, "/lib/x.spl")),
                Node::Enum(e) => e
                    .methods
                    .iter_mut()
                    .for_each(|m| crate::interpreter::tag_function_module_owner(m, "/lib/x.spl")),
                Node::Impl(i) => i
                    .methods
                    .iter_mut()
                    .for_each(|m| crate::interpreter::tag_function_module_owner(m, "/lib/x.spl")),
                _ => {}
            }
        }
        retain_reachable_ast_functions(&mut module.items, Path::new("/entry.spl")).expect("has main");
        assert_eq!(
            method_names(&module.items, "Box"),
            vec!["used_one", "chained", "len", "__enter__"],
            "order preserved; unused dropped; implicit + dunder kept"
        );
        assert!(method_names(&module.items, "Color").is_empty(), "dead enum method dropped");
        // Struct `Pt` has two containers (struct + impl); the trait impl is untouched.
        let pt_methods: Vec<String> = module
            .items
            .iter()
            .filter_map(|n| match n {
                Node::Struct(s) => Some(s.methods.iter().map(|m| m.name.clone()).collect::<Vec<_>>()),
                Node::Impl(i) if i.trait_name.is_none() => {
                    Some(i.methods.iter().map(|m| m.name.clone()).collect::<Vec<_>>())
                }
                _ => None,
            })
            .flatten()
            .collect();
        assert!(pt_methods.is_empty(), "dead struct/impl methods dropped: {pt_methods:?}");
        let trait_impl: Vec<String> = module
            .items
            .iter()
            .filter_map(|n| match n {
                Node::Impl(i) if i.trait_name.is_some() => Some(i.methods.iter().map(|m| m.name.clone()).collect::<Vec<_>>()),
                _ => None,
            })
            .flatten()
            .collect();
        assert_eq!(trait_impl, vec!["area", "never_called_trait_impl"], "trait impls untouched");
    }

    #[test]
    fn no_main_prunes_nothing() {
        let mut module = simple_parser::Parser::new("fn a():\n    0\n").parse().expect("parse");
        assert!(retain_reachable_ast_functions(&mut module.items, Path::new("/e.spl")).is_none());
        assert_eq!(names(&module.items), vec!["a".to_string()]);
    }
}

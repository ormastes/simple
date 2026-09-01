//! Census of names that `lenient_types` lowers to `HirExprKind::Global`.
//!
//! # What this measures and why
//!
//! Under `lenient_types` an identifier that HIR lowering cannot resolve becomes
//! a `Global`, then a `GlobalLoad`, then an undeclared symbol that only fails at
//! **link** time -- with no file, no line and no function. Every such name is a
//! potential future blocker of exactly that shape.
//!
//! Most of them are perfectly fine: `native_project` lowers one file at a time,
//! so a reference to a function or const defined in a *sibling* file is
//! necessarily unresolved at HIR time and is resolved later against
//! `use_map` / `import_map`. Counting raw attributions therefore massively
//! over-reports.
//!
//! So this census reports two numbers:
//!
//! * **attributed** -- every name that took the lenient fallback. Includes all
//!   the legitimate cross-module references. Not a bug count.
//! * **undefined-tree-wide** -- attributed names for which NO file in the
//!   scanned source set defines a matching function, class, struct, enum,
//!   enum variant or module-level binding. These cannot be satisfied by any
//!   sibling module, so they are the actual queue of future link blockers.
//!
//! # Running it
//!
//! Ignored by default because it parses the whole source set. Run explicitly:
//!
//! ```text
//! cargo test -p simple-compiler --test lenient_global_census -- --ignored --nocapture
//! ```
//!
//! Override the scanned roots with `SIMPLE_CENSUS_ROOTS` (colon-separated,
//! repo-relative). Default is the stage4 source set: `src/compiler`, `src/lib`,
//! `src/app`.

use simple_compiler::hir::Lowerer;
use simple_compiler::module_resolver::ModuleResolver;
use simple_parser::ast::Node;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

fn repo_root() -> PathBuf {
    // CARGO_MANIFEST_DIR is <repo>/src/compiler_rust/compiler
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(3)
        .expect("repo root")
        .to_path_buf()
}

fn scan_roots() -> Vec<PathBuf> {
    let root = repo_root();
    match std::env::var("SIMPLE_CENSUS_ROOTS") {
        Ok(value) if !value.is_empty() => value.split(':').map(|r| root.join(r)).collect(),
        _ => vec![root.join("src/compiler"), root.join("src/lib"), root.join("src/app")],
    }
}

fn collect_spl_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        // Do not follow symlinked layer aliases: the compiler tree has ~17 of
        // them and following would double-count whole subtrees.
        let Ok(meta) = std::fs::symlink_metadata(&path) else {
            continue;
        };
        if meta.file_type().is_symlink() {
            continue;
        }
        if meta.is_dir() {
            collect_spl_files(&path, out);
        } else if path.extension().and_then(|e| e.to_str()) == Some("spl") {
            out.push(path);
        }
    }
}

/// Root identifier(s) bound by a pattern (`val x`, `val (a, b)`, `val x: T`).
fn pattern_names(pattern: &simple_parser::Pattern, out: &mut BTreeSet<String>) {
    use simple_parser::Pattern;
    match pattern {
        Pattern::Identifier(n) | Pattern::MutIdentifier(n) | Pattern::MoveIdentifier(n) => {
            out.insert(n.clone());
        }
        Pattern::Typed { pattern, .. } => pattern_names(pattern, out),
        Pattern::Tuple(items) => {
            for item in items {
                pattern_names(item, out);
            }
        }
        _ => {}
    }
}

/// Every name any module in the source set defines, in any binding form.
///
/// Module-level `val` / `const` / `static` MUST be included: the compiler tree
/// is full of protocol constants (`DNS_TYPE_A`, `CONNECT_FLAG_PASSWORD`, ...)
/// declared that way, and omitting them makes every one of them look like an
/// undefined name -- which inflates the blocker count with pure noise.
fn definitions_in(module: &simple_parser::Module, out: &mut BTreeSet<String>) {
    for item in &module.items {
        match item {
            Node::Let(l) => pattern_names(&l.pattern, out),
            Node::Const(c) => {
                out.insert(c.name.clone());
            }
            Node::Static(s) => {
                out.insert(s.name.clone());
            }
            Node::Extern(e) => {
                out.insert(e.name.clone());
                out.insert(format!("@{}", e.name));
            }
            Node::TypeAlias(t) => {
                out.insert(t.name.clone());
            }
            Node::Actor(a) => {
                out.insert(a.name.clone());
            }
            Node::Function(f) => {
                out.insert(f.name.clone());
            }
            Node::Class(c) => {
                out.insert(c.name.clone());
                for m in &c.methods {
                    out.insert(m.name.clone());
                    out.insert(format!("{}.{}", c.name, m.name));
                }
            }
            Node::Impl(i) => {
                for m in &i.methods {
                    out.insert(m.name.clone());
                }
            }
            Node::Struct(s) => {
                out.insert(s.name.clone());
            }
            Node::Enum(e) => {
                out.insert(e.name.clone());
                for v in &e.variants {
                    out.insert(v.name.clone());
                    out.insert(format!("{}.{}", e.name, v.name));
                }
            }
            _ => {}
        }
    }
}

#[test]
#[ignore = "whole-source-set census; run explicitly with --ignored"]
fn census_of_lenient_unresolved_globals() {
    let roots = scan_roots();
    let mut files = Vec::new();
    for root in &roots {
        collect_spl_files(root, &mut files);
    }
    files.sort();
    assert!(!files.is_empty(), "no .spl files found under {roots:?}");

    let mut parsed_ok = 0usize;
    let mut parse_failed = 0usize;
    let mut lower_failed = 0usize;
    let mut defined: BTreeSet<String> = BTreeSet::new();
    // name -> list of "file:line in function"
    let mut attributed: BTreeMap<String, Vec<String>> = BTreeMap::new();

    for path in &files {
        let Ok(source) = std::fs::read_to_string(path) else {
            continue;
        };
        let mut parser = simple_parser::Parser::new(&source);
        let Ok(module) = parser.parse() else {
            parse_failed += 1;
            continue;
        };
        parsed_ok += 1;
        definitions_in(&module, &mut defined);

        let mut lowerer = Lowerer::with_module_resolver(ModuleResolver::single_file(path), path.to_path_buf());
        lowerer.set_strict_mode(false);
        lowerer.set_lenient_types(true);
        let Ok(output) = lowerer.lower_module_with_warnings(&module) else {
            lower_failed += 1;
            continue;
        };
        for entry in output.lenient_globals.entries() {
            let location = format!(
                "{}:{} in {}",
                entry.file.as_deref().unwrap_or("<unknown>"),
                entry
                    .function_line
                    .map(|l| l.to_string())
                    .unwrap_or_else(|| "?".to_string()),
                entry.function.as_deref().unwrap_or("<toplevel>")
            );
            attributed.entry(entry.name.clone()).or_default().push(location);
        }
    }

    // A dotted name counts as defined if its last segment is defined, since
    // `a.b.c` paths are joined into one global name by `lower_path`.
    let is_defined = |name: &str| -> bool {
        if defined.contains(name) {
            return true;
        }
        let bare = name.trim_start_matches('@');
        if defined.contains(bare) {
            return true;
        }
        bare.rsplit('.').next().is_some_and(|last| defined.contains(last))
    };

    let undefined: BTreeMap<&String, &Vec<String>> = attributed.iter().filter(|(name, _)| !is_defined(name)).collect();

    println!("\n=== lenient unresolved-global census ===");
    println!("roots:                    {roots:?}");
    println!("files scanned:            {}", files.len());
    println!("  parsed ok:              {parsed_ok}");
    println!("  parse failed:           {parse_failed}");
    println!("  lowering failed:        {lower_failed}");
    println!("distinct names defined:   {}", defined.len());
    println!("distinct names attributed:{}", attributed.len());
    println!(
        "  of those, UNDEFINED tree-wide (future link blockers): {}",
        undefined.len()
    );
    println!("\n--- undefined tree-wide (name -> sites) ---");
    for (name, sites) in &undefined {
        println!("{name}  [{} site(s)]", sites.len());
        for site in sites.iter().take(4) {
            println!("    {site}");
        }
        if sites.len() > 4 {
            println!("    ... {} more", sites.len() - 4);
        }
    }
    println!("=== end census ===\n");

    // The census is a report, not a gate. It only asserts it actually ran.
    assert!(parsed_ok > 0, "census parsed no files; the scan is broken");
}

//! Real-corpus counterpart to `relative_import_not_soft_keyword_ident.rs`.
//!
//! Bug: doc/08_tracking/bug/soft_keyword_use_as_ident_broke_all_relative_imports_2026-08-17.md
//! Census: doc/08_tracking/bug/unparseable_spl_files_on_origin_main_sweep_2026-08-17.md
//!
//! `3c4e6551b7a` added `TokenKind::Use` to the `soft_kw_stmt_as_ident` `.`-peek
//! predicate in `parser_impl/core.rs`. `use .mod.X` IS the relative-import
//! statement form, so `use` followed by `Dot` was rerouted to an expression and
//! every relative import with a brace group or a glob tail died with
//! `expected identifier, found LBrace` / `found Star`. `579a0e1a171` excluded
//! `use` from the `.`-peek half.
//!
//! The sibling test pins hand-written fixtures. This one is deliberately
//! different in kind: it harvests the offending `use` lines from the REAL tree
//! and parses those, so the test cannot drift away from the syntax the codebase
//! actually contains. A hand-written fixture can be accidentally narrower than
//! the defect — the census recorded exactly that failure mode for the
//! or-pattern gap, where a synthetic repro parsed fine while the real file did
//! not.

use std::path::{Path, PathBuf};

use simple_parser::Parser;

/// Walk up from the parser crate to the repository root.
fn repo_root() -> PathBuf {
    // CARGO_MANIFEST_DIR = <repo>/src/compiler_rust/parser
    let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    manifest
        .ancestors()
        .nth(3)
        .expect("parser crate should be 3 levels below the repo root")
        .to_path_buf()
}

/// True for a relative import whose tail is a brace group or a glob:
/// `use .foo.{A, B}` / `use ..foo.*` / `use ...foo.{A}`.
fn is_relative_brace_or_glob_import(line: &str) -> bool {
    let rest = match line.strip_prefix("use ") {
        Some(r) => r,
        None => return false,
    };
    if !rest.starts_with('.') {
        return false;
    }
    let rest = rest.trim_end();
    rest.ends_with('*') || (rest.ends_with('}') && rest.contains('{'))
}

fn collect_spl_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let entries = match std::fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            // Vendored trees are out of scope per CLAUDE.md Owned-Code Scope.
            if path.file_name().is_some_and(|n| n == "vendor") {
                continue;
            }
            collect_spl_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "spl") {
            out.push(path);
        }
    }
}

/// Harvest every real `use .…{…}` / `use .…*` line under `src/`, paired with
/// the file it came from so a failure names a real call site.
fn harvest() -> Vec<(PathBuf, usize, String)> {
    let src = repo_root().join("src");
    let mut files = Vec::new();
    collect_spl_files(&src, &mut files);
    files.sort();

    let mut found = Vec::new();
    for file in files {
        let text = match std::fs::read_to_string(&file) {
            Ok(t) => t,
            Err(_) => continue, // non-UTF8 or unreadable: not this test's subject
        };
        for (idx, line) in text.lines().enumerate() {
            if is_relative_brace_or_glob_import(line) {
                found.push((file.clone(), idx + 1, line.to_string()));
            }
        }
    }
    found
}

#[test]
fn every_real_relative_brace_or_glob_import_in_the_tree_parses() {
    let lines = harvest();

    // Non-vacuity: a run that parsed nothing is a broken test, not a pass.
    // The sweep of 2026-08-17 measured 93 such lines across 46 files; the tree
    // moves, so assert a floor rather than an exact count.
    assert!(
        lines.len() >= 50,
        "harvested only {} relative brace/glob import lines — the harvester is \
         broken or the corpus vanished; this test would otherwise pass vacuously",
        lines.len()
    );

    let mut failures: Vec<String> = Vec::new();
    for (path, lineno, line) in &lines {
        // Parse the import statement on its own. A whole-file parse would also
        // surface the tree's genuinely-malformed files (7 in `src/lib` per the
        // census), which are a different defect and must not be conflated.
        let mut parser = Parser::new(line);
        if let Err(err) = parser.parse() {
            failures.push(format!("{}:{}: {}\n    {}", path.display(), lineno, err, line.trim()));
        }
    }

    assert!(
        failures.is_empty(),
        "{} of {} real relative brace/glob imports failed to parse:\n{}",
        failures.len(),
        lines.len(),
        failures.join("\n")
    );
}

#[test]
fn the_harvester_recognises_the_shapes_it_claims_to() {
    // Guards the predicate itself: if this drifts, the corpus test above goes
    // quietly vacuous and the non-vacuity floor is the only thing left.
    assert!(is_relative_brace_or_glob_import("use .vhdl_validation.*"));
    assert!(is_relative_brace_or_glob_import("use .vhdl.vhdl_builder.{VhdlBuilder}"));
    assert!(is_relative_brace_or_glob_import("use ..linker.smf_reader.*"));
    assert!(is_relative_brace_or_glob_import("use ...monomorphize.note_sdn.{A, B}"));

    // Absolute imports are a separate path that never regressed; parenthesised
    // and bare relative imports are not this defect's shape.
    assert!(!is_relative_brace_or_glob_import("use foo.bar.{A, B}"));
    assert!(!is_relative_brace_or_glob_import("use ..linker.smf_header (X)"));
    assert!(!is_relative_brace_or_glob_import("use .compiler_sffi"));
    assert!(!is_relative_brace_or_glob_import("val x = 1"));
}

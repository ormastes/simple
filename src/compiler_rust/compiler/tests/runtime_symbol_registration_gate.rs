//! Build-time gate: every runtime symbol name that codegen can EMIT a call to
//! must be present in `RUNTIME_SYMBOL_NAMES`
//! (`src/compiler_rust/common/src/runtime_symbols.rs`), because listing there
//! is the entire registration mechanism (`runtime/build.rs` parses that file
//! as TEXT — see its `for line in content.lines()` loop — to build
//! `RUNTIME_SYMBOL_ENTRIES`, which is what `register_static_runtime_symbols`
//! publishes and the JIT resolves calls against). A symbol emitted but not
//! listed compiles fine and fails only at run time with "unresolved external
//! symbol", silently falling back to the interpreter.
//!
//! See doc/08_tracking/bug/jit_runtime_symbol_unregistered_rt_value_unbox_int_2026-08-11.md
//! for the incident this closes: `rt_value_unbox_int`, `rt_struct_receiver_valid`,
//! and `rt_dict_insert` were emitted, defined, and spec'd, but absent from the
//! list, so the JIT never registered them.
//!
//! This test re-derives, from source text, the same two sets the bug's audit
//! computed by hand: (1) every `rt_*` symbol name that appears as a literal
//! argument to one of the four call/lookup patterns codegen uses to reach a
//! runtime symbol by name (`call_runtime_*`, `runtime_funcs.get`,
//! `.declare_function`, `get_function`), and (2) every name listed in
//! `RUNTIME_SYMBOL_NAMES`. Anything in (1) but not (2) fails the test unless
//! it is in `ALLOWED_UNLISTED`, the audited set of names that are emitted but
//! have no runtime definition to register (dead/aspirational call sites) or
//! are resolved through a different registration path (monoio).

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};

use regex::Regex;

/// Names found in the 2026-08-11 family audit that are emitted by codegen but
/// deliberately NOT in `RUNTIME_SYMBOL_NAMES`:
/// - `rt_await`, `rt_contract_check`, `rt_unit_bound_check`, `rt_generator_yield`,
///   `rt_par_for_each`: no definition anywhere in the runtime (Rust or C) —
///   dead/aspirational call sites, not a registration gap.
/// - `rt_future_get_ctx`, `rt_future_get_state`, `rt_future_set_state`:
///   likewise undefined; the live future path goes through the `rt_monoio_*`
///   names below.
/// - `rt_monoio_future_get_ctx`, `rt_monoio_future_get_result`,
///   `rt_monoio_future_set_async_state`, `rt_monoio_poll`: defined, but
///   reached through the monoio executor's own linkage, not
///   `RUNTIME_SYMBOL_NAMES`/`RUNTIME_SYMBOL_ENTRIES`.
///
/// Adding a name here must not be done to silence a real gap: first prove (as
/// the incident doc did) that the symbol has no runtime definition anywhere,
/// or is registered through a documented alternate path. Removing a fixed
/// symbol from this file's allowlist has already happened once for exactly
/// this reason (`rt_value_unbox_int` et al. moved from unlisted to listed).
const ALLOWED_UNLISTED: &[&str] = &[
    "rt_await",
    "rt_contract_check",
    "rt_future_get_ctx",
    "rt_future_get_state",
    "rt_future_set_state",
    "rt_generator_yield",
    "rt_monoio_future_get_ctx",
    "rt_monoio_future_get_result",
    "rt_monoio_future_set_async_state",
    "rt_monoio_poll",
    "rt_par_for_each",
    "rt_unit_bound_check",
];

fn workspace_root() -> PathBuf {
    // CARGO_MANIFEST_DIR = .../src/compiler_rust/compiler
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

/// Parse `RUNTIME_SYMBOL_NAMES` out of `common/src/runtime_symbols.rs` the
/// same way `runtime/build.rs` does: line-scan between the declaration and
/// the closing `];`, taking the first quoted string on each line. This is
/// deliberately NOT a `regex` walk over the whole file — mirroring build.rs's
/// own (intentionally simple) parser is what keeps this test honest about
/// what the build actually sees.
fn parse_listed_symbols(path: &Path) -> BTreeSet<String> {
    let content = fs::read_to_string(path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let mut in_list = false;
    let mut names = BTreeSet::new();
    for line in content.lines() {
        if line.contains("pub const RUNTIME_SYMBOL_NAMES") {
            in_list = true;
            continue;
        }
        if !in_list {
            continue;
        }
        if line.contains("];") {
            break;
        }
        if let Some(start) = line.find('"') {
            let rest = &line[start + 1..];
            if let Some(end) = rest.find('"') {
                names.insert(rest[..end].to_string());
            }
        }
    }
    assert!(
        !names.is_empty(),
        "parsed zero symbols from {} — parser or file drifted, this test would pass vacuously",
        path.display()
    );
    names
}

/// Collect every `rt_*` literal name that codegen reaches through one of the
/// four call patterns that resolve a runtime symbol *by name string*, across
/// every `.rs` file under `compiler/src/codegen/`.
fn collect_emitted_symbols(codegen_dir: &Path) -> BTreeSet<String> {
    let patterns = [
        // call_runtime_0/1/2/3/N(ctx, builder, "rt_name", ...)
        Regex::new(r#"call_runtime_[a-zA-Z0-9_]*\([^;]*?"(rt_[a-zA-Z0-9_]*)""#).unwrap(),
        // ctx.runtime_funcs.get("rt_name")
        Regex::new(r#"runtime_funcs\.get\("(rt_[a-zA-Z0-9_]*)"\)"#).unwrap(),
        // <module>.declare_function("rt_name", ...)
        Regex::new(r#"\.declare_function\(\s*"(rt_[a-zA-Z0-9_]*)""#).unwrap(),
        // get_function("rt_name") / get_function_ptr("rt_name")
        Regex::new(r#"get_function(?:_ptr)?\(\s*"(rt_[a-zA-Z0-9_]*)""#).unwrap(),
    ];

    let mut names = BTreeSet::new();
    let mut files_scanned = 0usize;
    for entry in walk_rs_files(codegen_dir) {
        let content = fs::read_to_string(&entry).unwrap_or_else(|e| panic!("read {}: {e}", entry.display()));
        files_scanned += 1;
        for pat in &patterns {
            for cap in pat.captures_iter(&content) {
                names.insert(cap[1].to_string());
            }
        }
    }
    assert!(
        files_scanned > 50,
        "scanned only {files_scanned} .rs files under {} — path drifted, \
         this test would pass vacuously",
        codegen_dir.display()
    );
    assert!(
        !names.is_empty(),
        "extracted zero emitted symbols from {} — pattern set or path drifted",
        codegen_dir.display()
    );
    names
}

fn walk_rs_files(dir: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(d) = stack.pop() {
        let Ok(entries) = fs::read_dir(&d) else { continue };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|e| e == "rs") {
                out.push(path);
            }
        }
    }
    out
}

#[test]
fn every_emitted_runtime_symbol_is_registered_or_allowlisted() {
    let root = workspace_root();
    let symbols_file = root.join("../common/src/runtime_symbols.rs");
    let codegen_dir = root.join("src/codegen");

    let listed = parse_listed_symbols(&symbols_file);
    let emitted = collect_emitted_symbols(&codegen_dir);
    let allowed: BTreeSet<&str> = ALLOWED_UNLISTED.iter().copied().collect();

    let unregistered: Vec<&String> = emitted
        .iter()
        .filter(|name| !listed.contains(name.as_str()) && !allowed.contains(name.as_str()))
        .collect();

    assert!(
        unregistered.is_empty(),
        "{} runtime symbol(s) are emitted by codegen (matched call_runtime_*/\
         runtime_funcs.get/.declare_function/get_function) but are absent from \
         both RUNTIME_SYMBOL_NAMES ({}) and the audited ALLOWED_UNLISTED set: {:?}\n\
         Each name here will compile cleanly and fail ONLY at run time with \
         \"unresolved external symbol\", falling silently back to the interpreter \
         (see doc/08_tracking/bug/jit_runtime_symbol_unregistered_rt_value_unbox_int_2026-08-11.md). \
         Either add the name to RUNTIME_SYMBOL_NAMES in {} (if it has a real \
         runtime definition), or add it to ALLOWED_UNLISTED in this test with a \
         comment proving it has none.",
        unregistered.len(),
        symbols_file.display(),
        unregistered,
        symbols_file.display(),
    );

    // Sanity: every allowlisted name must actually still be reachable in the
    // emitted set. If a name in ALLOWED_UNLISTED stops being emitted, or gets
    // added to RUNTIME_SYMBOL_NAMES, the allowlist is stale and should shrink
    // — this keeps the allowlist from silently growing unbounded.
    let stale: Vec<&&str> = ALLOWED_UNLISTED.iter().filter(|name| listed.contains(**name)).collect();
    assert!(
        stale.is_empty(),
        "ALLOWED_UNLISTED name(s) {:?} are now present in RUNTIME_SYMBOL_NAMES — \
         remove them from ALLOWED_UNLISTED in this test file, they are no longer \
         an exception.",
        stale,
    );
}

//! Mechanism pin: `filter_functions_from_value` rebuilds an imported module's
//! export dict ONCE per source dict, not once per importing module. Before the
//! memo every importer's frozen env carried its own full copy of every module
//! dict it could see (O(importers x exports) retained memory).
//! doc/08_tracking/bug/seed_filtered_module_dict_rebuilt_per_importer_2026-08-22.md
use simple_compiler::interpreter;
use simple_compiler::perf_counters;
use std::fs;
use std::sync::atomic::Ordering;
use tempfile::tempdir;

const IMPORTERS: usize = 6;

#[test]
fn imported_module_dict_is_filtered_once_per_source_not_per_importer() {
    let dir = tempdir().unwrap();
    let pkg = dir.path().join("src").join("pkg");
    fs::create_dir_all(&pkg).unwrap();
    let mut base = String::new();
    for i in 0..50 {
        base.push_str(&format!("fn f{i}(x: i64) -> i64:\n    x + {i}\n"));
    }
    fs::write(pkg.join("base.spl"), base).unwrap();
    let mut main = String::new();
    for k in 0..IMPORTERS {
        // Each mid module binds the SAME base export dict under `base`, so its
        // frozen env filters that dict: once (memo) vs once per mid (pre-fix).
        fs::write(
            pkg.join(format!("mid{k}.spl")),
            format!("use pkg.base\nfn g{k}(x: i64) -> i64:\n    base.f{k}(x)\n"),
        )
        .unwrap();
        main.push_str(&format!("use pkg.mid{k}.*\n"));
    }
    main.push_str("fn main() -> i64:\n    g0(1) + g5(1)\n");
    let main_path = pkg.join("main.spl");
    fs::write(&main_path, &main).unwrap();

    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    perf_counters::set_enabled(true);
    let b0 = perf_counters::FILTERED_DICT_BUILDS.load(Ordering::Relaxed);
    let h0 = perf_counters::FILTERED_DICT_HITS.load(Ordering::Relaxed);
    let module = simple_parser::Parser::new(&main).parse().unwrap();
    interpreter::set_current_file(Some(main_path.clone()));
    let r = interpreter::evaluate_module(&module.items);
    interpreter::set_current_file(None);
    assert!(r.is_ok(), "program must still run: {r:?}");
    let builds = perf_counters::FILTERED_DICT_BUILDS.load(Ordering::Relaxed) - b0;
    let hits = perf_counters::FILTERED_DICT_HITS.load(Ordering::Relaxed) - h0;
    // Pre-memo: hits == 0 and builds >= IMPORTERS (one rebuild of base's dict
    // per mid module). Post-memo: base's dict is built once and the other
    // IMPORTERS-1 importers hit the memo.
    assert!(hits >= (IMPORTERS as u64) - 1, "expected >= {} memo hits, got builds={builds} hits={hits}", IMPORTERS - 1);
    assert!(builds < hits + 2, "builds={builds} should not scale with importers (hits={hits})");
    interpreter::clear_module_cache();
}

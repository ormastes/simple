//! Targeted regression and verification tests for Wave 1 BF-4 Rust seed
//! interpreter semantics & parser bugs on `release/1.0.0`.

use std::collections::HashSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Mutex;

use simple_compiler::interpreter::{
    clear_bdd_state, clear_interpreter_state, clear_module_cache, evaluate_module, get_ignored_tests,
    get_test_results, set_current_file,
};
use simple_compiler::pipeline::module_loader::load_module_with_imports;
use simple_parser::Parser;

static LOCK: Mutex<()> = Mutex::new(());

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../..")
        .canonicalize()
        .expect("repo root")
}

struct DirGuard(PathBuf);

impl DirGuard {
    fn enter_repo_root() -> Self {
        let orig = std::env::current_dir().expect("cwd");
        std::env::set_current_dir(repo_root()).expect("set cwd to repo root");
        Self(orig)
    }
}

impl Drop for DirGuard {
    fn drop(&mut self) {
        let _ = std::env::set_current_dir(&self.0);
    }
}

fn setup_env(safety_profile: Option<&str>) {
    let src_dir = repo_root().join("src");
    std::env::set_var("SIMPLE_LIB", &src_dir);
    match safety_profile {
        Some(p) => std::env::set_var("SIMPLE_SAFETY_PROFILE", p),
        None => std::env::remove_var("SIMPLE_SAFETY_PROFILE"),
    }
}

fn eval_parse_only(source: &str) -> Result<i32, String> {
    let _g = LOCK.lock().unwrap();
    let _dir = DirGuard::enter_repo_root();
    setup_env(None);
    clear_module_cache();
    clear_interpreter_state();
    clear_bdd_state();
    let module = Parser::new(source).parse().map_err(|e| format!("parse err: {e:?}"))?;
    let res = evaluate_module(&module.items).map_err(|e| format!("{e}"));
    clear_bdd_state();
    res
}

fn eval_with_imports(
    source: &str,
    safety_profile: Option<&str>,
) -> Result<(i32, Vec<(String, String, bool, bool)>, Vec<String>), String> {
    let _g = LOCK.lock().unwrap();
    let _dir = DirGuard::enter_repo_root();
    setup_env(safety_profile);
    let dir = tempfile::tempdir().unwrap();
    let main_path = dir.path().join("main.spl");
    fs::write(&main_path, source).unwrap();

    clear_module_cache();
    clear_interpreter_state();
    clear_bdd_state();

    let res = (|| {
        let module =
            load_module_with_imports(&main_path, &mut HashSet::new()).map_err(|e| format!("load err: {e}"))?;
        set_current_file(Some(main_path.clone()));
        let code = evaluate_module(&module.items).map_err(|e| format!("{e}"));
        set_current_file(None);
        let results = get_test_results();
        let ignored = get_ignored_tests();
        code.map(|c| (c, results, ignored))
    })();
    std::env::remove_var("SIMPLE_SAFETY_PROFILE");
    clear_bdd_state();
    res
}

fn run_repo_spec(
    rel: &str,
    safety_profile: Option<&str>,
) -> Result<(i32, Vec<(String, String, bool, bool)>, Vec<String>), String> {
    let _g = LOCK.lock().unwrap();
    let _dir = DirGuard::enter_repo_root();
    setup_env(safety_profile);
    let path = repo_root().join(rel);
    assert!(path.exists(), "missing spec file: {}", path.display());

    clear_module_cache();
    clear_interpreter_state();
    clear_bdd_state();

    let res = (|| {
        let module = load_module_with_imports(&path, &mut HashSet::new()).map_err(|e| format!("load err: {e}"))?;
        set_current_file(Some(path.clone()));
        let code = evaluate_module(&module.items).map_err(|e| format!("{e}"));
        set_current_file(None);
        let results = get_test_results();
        let ignored = get_ignored_tests();
        code.map(|c| (c, results, ignored))
    })();
    std::env::remove_var("SIMPLE_SAFETY_PROFILE");
    clear_bdd_state();
    res
}

#[test]
fn bug1_rejects_literal_non_bool_across_all_call_paths() {
    let cases = [
        (
            "direct",
            "fn takes_bool(b: bool) -> i64:\n    if b: return 1\n    return 0\nmain = takes_bool(42)\n",
        ),
        (
            "direct named",
            "fn takes_bool(flag: bool) -> i64:\n    if flag: return 1\n    return 0\nmain = takes_bool(flag: 42)\n",
        ),
        (
            "overloaded",
            "fn ov(b: bool) -> i64:\n    if b: return 1\n    return 0\nfn ov(b: bool, extra: i64) -> i64:\n    if b: return extra\n    return 0\nmain = ov(42)\n",
        ),
        (
            "overloaded named",
            "fn ov(flag: bool) -> i64:\n    if flag: return 1\n    return 0\nfn ov(flag: bool, extra: i64) -> i64:\n    if flag: return extra\n    return 0\nmain = ov(flag: 42)\n",
        ),
        (
            "immutable method",
            "class Boxed:\n    v: i64\n    fn check(b: bool) -> i64:\n        if b: return 1\n        return 0\nval b = Boxed(v: 1)\nmain = b.check(42)\n",
        ),
        (
            "mutating me method",
            "class Boxed:\n    v: i64\n    me mut_check(b: bool) -> i64:\n        self.v = self.v + 1\n        if b: return 1\n        return 0\nvar b = Boxed(v: 1)\nmain = b.mut_check(42)\n",
        ),
        (
            "static class method",
            "class Gate:\n    v: i64\n    static fn make(b: bool) -> i64:\n        if b: return 1\n        return 0\nmain = Gate.make(42)\n",
        ),
        (
            "ufcs method",
            "class Tag:\n    v: i64\nfn ufcs_check(t: Tag, b: bool) -> i64:\n    if b: return t.v\n    return 0\nval t = Tag(v: 7)\nmain = t.ufcs_check(42)\n",
        ),
        (
            "chained ufcs method",
            "class Tag:\n    v: i64\nfn make_tag() -> Tag:\n    Tag(v: 7)\nfn ufcs_check(t: Tag, b: bool) -> i64:\n    if b: return t.v\n    return 0\nfn run() -> i64:\n    make_tag().ufcs_check(42)\n    return 0\nmain = run()\n",
        ),
    ];

    for (label, src) in cases {
        let err = eval_parse_only(src).expect_err(&format!("{label} must reject non-bool literal"));
        assert!(
            err.contains("declared 'bool'"),
            "{label} returned wrong error: {err}"
        );
    }
}

#[test]
fn bug1_preserves_bool_and_presence_query_contract() {
    let src = r#"
fn check_presence(b: bool) -> i64:
    if b: return 1
    return 0

val some_zero: i64? = Some(0)
val none_val: i64? = nil
main = check_presence(true) * 1000 + check_presence(false) * 100 + check_presence(some_zero.?) * 10 + check_presence(none_val.?)
"#;
    assert_eq!(eval_parse_only(src), Ok(1010));
}

#[test]
fn bug2_pending_and_skip_execute_spl_body_and_honor_governance() {
    let (code, results, ignored) = run_repo_spec("test/01_unit/lib/spec/pending_inside_it_not_pass_spec.spl", None)
        .expect("pending_inside_it_not_pass_spec");
    assert_eq!(code, 0);
    assert_eq!(
        results,
        vec![
            (
                "pending inside it".to_string(),
                "is a real passing example".to_string(),
                true,
                false
            ),
            (
                "pending inside it".to_string(),
                "is only pending, not passed".to_string(),
                true,
                true
            ),
        ]
    );
    assert_eq!(ignored, vec!["is only pending, not passed".to_string()]);

    let (acct_code, _, _) =
        run_repo_spec("test/01_unit/lib/std/spec/pending_runtime_accounting_spec.spl", None).unwrap();
    assert_eq!(acct_code, 0);

    let (probe_code, probe_res, _) =
        run_repo_spec("test/01_unit/lib/std/spec/skip_governance_probe_spec.spl", None).unwrap();
    assert_eq!(probe_code, 0);
    assert_eq!(probe_res.len(), 4);
    assert!(probe_res.iter().all(|(_, _, p, s)| *p && !*s), "{probe_res:?}");

    let (gov_code, gov_res, _) =
        run_repo_spec("test/01_unit/lib/std/spec/skip_governance_spec.spl", None).unwrap();
    assert_eq!(gov_code, 0);
    assert_eq!(gov_res.len(), 23);
    assert!(gov_res.iter().all(|(_, _, p, s)| *p && !*s), "{gov_res:?}");

    // Critical safety profile MUST fail rejected pending/skip instead of silently skipping.
    let crit_pending = r#"
use std.spec.*

describe "critical pending":
    it "rejects bare pending inside it":
        pending("not ready")
        expect(true).to_equal(true)
"#;
    let (c1, r1, i1) = eval_with_imports(crit_pending, Some("critical")).unwrap();
    assert_eq!(c1, 0);
    assert_eq!(r1.len(), 1);
    assert!(!r1[0].2 && !r1[0].3, "critical pending inside it must fail: {r1:?}");
    assert!(i1.is_empty(), "rejected pending must not enter ignored list: {i1:?}");

    let crit_skip_in_it = r#"
use std.spec.*

describe "critical skip in it":
    it "rejects weak skip inside it":
        skip("case", "todo")
        expect(true).to_equal(true)
"#;
    let (c2, r2, i2) = eval_with_imports(crit_skip_in_it, Some("critical")).unwrap();
    assert_eq!(c2, 0);
    assert_eq!(r2.len(), 1);
    assert!(!r2[0].2 && !r2[0].3, "critical skip inside it must fail: {r2:?}");
    assert!(i2.is_empty(), "rejected skip must not enter ignored list: {i2:?}");

    let crit_describe_context = r#"
use std.spec.*

describe "critical describe skip_context":
    skip_context("weak context")
    pending("bare describe pending")
"#;
    let (c3a, r3a, i3a) = eval_with_imports(crit_describe_context, Some("critical")).unwrap();
    assert_eq!(c3a, 0);
    assert_eq!(r3a.len(), 2, "{r3a:?}");
    assert!(
        r3a.iter().all(|(_, _, p, s)| !*p && !*s),
        "rejected describe skip_context/pending under critical must fail: {r3a:?}"
    );
    assert!(i3a.is_empty(), "rejected describe skips must not enter ignored list: {i3a:?}");

    std::env::set_var("SIMPLE_TEST_FILTER", "skipped");
    let crit_describe_level = r#"
use std.spec.*

describe "critical describe level":
    skip_it("rejects skip_it", fn():
        expect(true).to_equal(true)
    )
    skip("rejects weak skip", "todo")
"#;
    let res_3b = eval_with_imports(crit_describe_level, Some("critical"));
    std::env::remove_var("SIMPLE_TEST_FILTER");
    let (c3, r3, i3) = res_3b.unwrap();
    assert_eq!(c3, 0);
    assert_eq!(r3.len(), 2, "{r3:?}");
    assert!(
        r3.iter().all(|(_, _, p, s)| !*p && !*s),
        "all rejected skips under critical (with filter=skipped) must record failure: {r3:?}"
    );
    assert!(i3.is_empty(), "rejected describe skips must not enter ignored list: {i3:?}");

    // Default/moderate profile: valid skip inside `it` works without SIMPLE_TEST_FILTER,
    // and describe-level `skip_it` marks skipped when SIMPLE_TEST_FILTER=skipped.
    let moderate_in_it = r#"
use std.spec.*

describe "moderate skip in it":
    it "allows skip inside it without filter":
        skip("inner", "valid reason for moderate")
        expect(false).to_equal(true)
"#;
    let (c4a, r4a, i4a) = eval_with_imports(moderate_in_it, Some("moderate")).unwrap();
    assert_eq!(c4a, 0);
    assert_eq!(r4a.len(), 1, "{r4a:?}");
    assert!(r4a[0].2 && r4a[0].3, "valid moderate skip inside it must skip: {r4a:?}");
    assert_eq!(i4a.len(), 1, "{i4a:?}");

    std::env::set_var("SIMPLE_TEST_FILTER", "skipped");
    let moderate_skips = r#"
use std.spec.*

describe "moderate skips":
    skip_it("describe skip_it", fn():
        expect(true).to_equal(true)
    )
"#;
    let res_4 = eval_with_imports(moderate_skips, Some("moderate"));
    std::env::remove_var("SIMPLE_TEST_FILTER");
    let (c4, r4, i4) = res_4.unwrap();
    assert_eq!(c4, 0);
    assert_eq!(r4.len(), 1, "{r4:?}");
    assert!(
        r4.iter().all(|(_, _, p, s)| *p && *s),
        "valid moderate describe skip_it must mark skipped: {r4:?}"
    );
    assert_eq!(i4.len(), 1, "{i4:?}");
}

#[test]
fn bug3_manycall_sum_300_and_f64_user_fn() {
    let mut src = String::new();
    for i in 0..300 {
        src.push_str(&format!("fn f{i}() -> i64:\n    return {i}\n"));
    }
    let expr = (0..300).map(|i| format!("f{i}()")).collect::<Vec<_>>().join(" + ");
    src.push_str(&format!("main = {expr}\n"));
    assert_eq!(eval_parse_only(&src), Ok(44850));

    let f64_user = "fn f64() -> i64:\n    return 64\n\nmain = f64()\n";
    assert_eq!(eval_parse_only(f64_user), Ok(64));
}

#[test]
fn bug4_postfix_matchers_work_on_chained_receivers_with_and_without_std_spec() {
    let (code, results, _) = run_repo_spec("test/01_unit/lib/spec/postfix_matcher_chained_receiver_spec.spl", None)
        .expect("postfix_matcher_chained_receiver_spec");
    assert_eq!(code, 0);
    assert_eq!(results.len(), 6);
    assert!(results.iter().all(|(_, _, p, s)| *p && !*s), "{results:?}");

    // Even when `use std.spec.*` loads `ExpectScalarMatcher for i64`, bare chained
    // `xs.len().to_*()` and all other matchers must work without hitting `_expect_helper_slots[0]`.
    let chained_all = r#"
use std.spec.*

describe "all chained postfix matchers":
    it "supports comparison matchers":
        val xs = [1, 2, 3]
        xs.len().to_equal(3)
        xs.len().to_be(3)
        xs.len().to_not_equal(4)
        xs.len().to_be_greater_than(2)
        xs.len().to_be_less_than(5)
        xs.len().to_be_gte(3)
        xs.len().to_be_lte(3)

    it "supports string and nil matchers":
        val xs = [10, 20]
        "  hello world  ".trim().to_contain("world")
        "  hello world  ".trim().to_not_contain("missing")
        "  hello world  ".trim().to_start_with("hello")
        "  hello world  ".trim().to_end_with("world")
        xs.get(99).to_be_nil()
        xs.get(0).to_be_some()

    it "records failures cleanly on mismatch":
        val xs = [1, 2]
        xs.len().to_be_greater_than(99)
"#;
    let (c, r, _) = eval_with_imports(chained_all, None).unwrap();
    assert_eq!(c, 0);
    assert_eq!(r.len(), 3, "{r:?}");
    assert!(r[0].2 && !r[0].3, "{r:?}");
    assert!(r[1].2 && !r[1].3, "{r:?}");
    assert!(!r[2].2 && !r[2].3, "mismatch must fail: {r:?}");

    // Outside `it`, a mismatched chained matcher must error cleanly just like `expect(...)`.
    let outside_eq = "val xs = [1, 2, 3]\nxs.len().to_equal(99)\nmain = 0\n";
    let err_eq = eval_parse_only(outside_eq).expect_err("outside-it mismatch must error");
    assert!(err_eq.contains("expected 3 to equal 99"), "{err_eq}");

    let outside_gt = "val xs = [1, 2, 3]\nxs.len().to_be_greater_than(99)\nmain = 0\n";
    let err_gt = eval_parse_only(outside_gt).expect_err("outside-it mismatch must error");
    assert!(err_gt.contains("expected 3 to be greater than 99"), "{err_gt}");
}

#[test]
fn bug4_ml_kem_768_kat_spec() {
    let (code, results, _) =
        run_repo_spec("test/01_unit/lib/crypto/ml_kem_768_kat_spec.spl", None).expect("ml_kem_768_kat_spec");
    assert_eq!(code, 0);
    assert_eq!(results.len(), 10);
    assert!(results.iter().all(|(_, _, p, s)| *p && !*s), "{results:?}");
}

#[test]
fn bug5_wildcard_import_does_not_leak_main_or_poison_session() {
    let c_stubs_no_main = r#"
use std.spec.*
use plugins.backend_c.c_backend_translate.{MirToC}
use plugins.backend_c.c_backend_stubs.*

describe "c_backend_stubs wildcard without main":
    it "exits cleanly with 0":
        expect(1).to_equal(1)
"#;
    let (c1, r1, _) = eval_with_imports(c_stubs_no_main, None).unwrap();
    assert_eq!(c1, 0);
    assert_eq!(r1.len(), 1);
    assert!(r1[0].2 && !r1[0].3, "{r1:?}");

    let wasm_no_main = r#"
use std.spec.*
use plugins.backend_wasm.wasm_backend.*

describe "wasm_backend wildcard without main":
    it "exits cleanly with 0":
        expect(1).to_equal(1)
"#;
    let (c2, r2, _) = eval_with_imports(wasm_no_main, None).unwrap();
    assert_eq!(c2, 0);
    assert_eq!(r2.len(), 1);
    assert!(r2[0].2 && !r2[0].3, "{r2:?}");

    for spec in [
        "test/01_unit/compiler/backend/wildcard_import_backend_api_prevention_spec.spl",
        "test/01_unit/compiler/backend/wildcard_import_backend_helpers_prevention_spec.spl",
        "test/01_unit/compiler/backend/wildcard_import_codegen_factory_prevention_spec.spl",
        "test/01_unit/compiler/backend/wildcard_import_common_type_mapper_prevention_spec.spl",
        "test/01_unit/compiler/backend/c_backend_async_spec.spl",
        "test/01_unit/compiler/backend/backend_capability_spec.spl",
        "test/feature/usage/wasm_compile_spec.spl",
    ] {
        let (code, results, _) = run_repo_spec(spec, None).expect(spec);
        assert_eq!(code, 0, "{spec} exited non-zero");
        assert!(
            results.iter().all(|(_, _, p, _)| *p),
            "{spec} failed an example: {results:?}"
        );
    }
}

#[test]
fn bug6_legacy_import_string_and_namespace_specs() {
    let basic = "import string\n\nval ch = string.char_at(\"hello\", 1)\nmain = if ch == \"e\": 0 else: 1\n";
    let (code, _, _) = eval_with_imports(basic, None).unwrap();
    assert_eq!(code, 0);

    let (u_code, u_res, _) = run_repo_spec("test/01_unit/compiler/interpreter/full_module_source_namespace_spec.spl", None)
        .expect("full_module_source_namespace_spec");
    assert_eq!(u_code, 0);
    assert_eq!(u_res.len(), 4);
    assert!(u_res.iter().all(|(_, _, p, s)| *p && !*s), "{u_res:?}");

    let (i_code, i_res, _) =
        run_repo_spec("test/02_integration/compiler/interpreter/legacy_string_source_namespace_spec.spl", None)
            .expect("legacy_string_source_namespace_spec");
    assert_eq!(i_code, 0);
    assert_eq!(i_res.len(), 2);
    assert!(i_res.iter().all(|(_, _, p, s)| *p && !*s), "{i_res:?}");
}

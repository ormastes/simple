//! Seed JIT: a primitive optional (`i64?` / `f64?` / `bool?`) is a real
//! `Option` -- it prints as `Option::Some(v)` / `Option::None`, exactly like the
//! tree-walk interpreter (the oracle), while `??`, `.?`, `match` and the stored
//! value 3 (the old nil-sentinel word) keep their values.
//!
//! Bug: doc/08_tracking/bug/parse_family_strips_option_jit_native_2026-08-02.md
//! Owner rule 2026-11-06: seed optional semantics = pure Simple.

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, interpreter, mir};
use simple_parser::Parser;
use simple_runtime::value::{rt_capture_stdout_start, rt_capture_stdout_stop};

fn run_interpreter(src: &str) -> String {
    interpreter::clear_module_cache();
    interpreter::clear_interpreter_state();
    // evaluate_module already invokes `main`; do not append a second call.
    let module = Parser::new(src).parse().expect("parse (interpreter)");
    rt_capture_stdout_start();
    let r = interpreter::evaluate_module(&module.items);
    let out = rt_capture_stdout_stop();
    r.expect("interpreter run");
    out
}

fn run_jit(src: &str) -> String {
    let ast = Parser::new(src).parse().expect("parse (JIT)");
    let hir_module = hir::lower(&ast).expect("HIR lower");
    let mir_module = mir::lower_to_mir(&hir_module).expect("MIR lower");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("MIR compile");
    rt_capture_stdout_start();
    let rc = unsafe { jit.call_i64_void("main").expect("main executes") };
    let out = rt_capture_stdout_stop();
    assert_eq!(rc, 0, "JIT main returned failing row {rc}; stdout={out:?}");
    out
}

fn assert_parity(src: &str, expected: &str) {
    let interp = run_interpreter(src);
    assert_eq!(interp.trim(), expected, "interpreter oracle drifted");
    let jit = run_jit(src);
    assert_eq!(jit.trim(), expected, "JIT must match the interpreter oracle");
}

#[test]
fn parse_int_prints_some_and_none() {
    assert_parity(
        r#"
fn main() -> i64:
    val a = "12".parse_int()
    val b = "abc".parse_int()
    print "{a}"
    print "{b}"
    0
"#,
        "Option::Some(12)\nOption::None",
    );
}

#[test]
fn stored_three_is_some_not_none() {
    assert_parity(
        r#"
fn get(v: i64) -> i64?:
    return v

fn none_i64() -> i64?:
    return None

fn main() -> i64:
    val t = get(3)
    val n = none_i64()
    print "{t}"
    print "{n}"
    if (t ?? -1) != 3: return 1
    if (n ?? -1) != -1: return 2
    if not t.?: return 3
    if n.?: return 4
    0
"#,
        "Option::Some(3)\nOption::None",
    );
}

#[test]
fn coalesce_and_exists_on_parse() {
    assert_parity(
        r#"
fn main() -> i64:
    val c = "3".parse_int() ?? -1
    val d = "abc".parse_int() ?? -1
    print "{c} {d}"
    if not "5".parse_int().?: return 1
    if "x".parse_int().?: return 2
    0
"#,
        "3 -1",
    );
}

#[test]
fn match_arms_on_primitive_option() {
    assert_parity(
        r#"
fn classify(o: i64?) -> i64:
    match o:
        case Some(v): v
        case None: -1

fn main() -> i64:
    if classify("42".parse_int()) != 42: return 1
    if classify("zz".parse_int()) != -1: return 2
    if classify("3".parse_int()) != 3: return 3
    0
"#,
        "",
    );
}

#[test]
fn float_and_bool_options_print_as_option() {
    assert_parity(
        r#"
fn gf(f: bool) -> f64?:
    if f:
        return 1.5
    None

fn gb(f: bool) -> bool?:
    if f:
        return true
    None

fn main() -> i64:
    print "{gf(true)}"
    print "{gf(false)}"
    print "{gb(true)}"
    print "{gb(false)}"
    0
"#,
        "Option::Some(1.5)\nOption::None\nOption::Some(true)\nOption::None",
    );
}

#[test]
fn parse_float_prints_some_and_none() {
    assert_parity(
        r#"
fn main() -> i64:
    val a = "1.5".parse_float()
    val b = "abc".parse_float()
    print "{a}"
    print "{b}"
    0
"#,
        "Option::Some(1.5)\nOption::None",
    );
}

#[test]
fn parse_float_and_f64_unwrap_to_f64() {
    assert_parity(
        r#"
fn main() -> i64:
    val a = "1.5".parse_float().unwrap()
    if a != 1.5: return 1
    val b = "2.25".parse_f64().unwrap()
    if b != 2.25: return 2
    0
"#,
        "",
    );
}

#[test]
fn match_binds_parse_result_payload() {
    // The lane-4 pure_sql reopen manifestation: a `case Some(n)` over a
    // parse-call subject must bind the payload, not the nil sentinel.
    assert_parity(
        r#"
fn main() -> i64:
    val parsed = "87".parse_int()
    match parsed:
        case Some(length):
            if length != 87: return 1
        case None:
            return 2
    match "42".parse_int():
        case Some(n):
            if n != 42: return 3
        case None:
            return 4
    0
"#,
        "",
    );
}

#[test]
fn match_binds_parse_float_payload() {
    assert_parity(
        r#"
fn main() -> i64:
    match "1.5".parse_float():
        case Some(x):
            if x != 1.5: return 1
        case None:
            return 2
    0
"#,
        "",
    );
}

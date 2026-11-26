//! Cranelift JIT parity regressions for:
//! - Bug 3: `jit_unsafe_optional_as_cast_garbage_2026_11_09` (interpolated + width/float `unsafe:` `T? as U` casts)
//! - Bug 4: `jit_text_repeat_dispatch_and_silent_error_substitution_2026-08-01`
//! - Bug 5: `jit_dispatch_worklist_2026-07-29`

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run_jit(source: &str) -> i64 {
    simple_runtime::register_static_runtime_symbols();
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir_jit(&hir_module).expect("source must JIT-lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn bug3_unsafe_optional_as_cast_jit_variants_and_interpolation() {
    let source = r#"
fn get_u64(ok: bool) -> u64?:
    if ok:
        return 42u64
    return nil

fn get_i64(ok: bool) -> i64?:
    if ok:
        return 77i64
    return nil

fn get_f64(ok: bool) -> f64?:
    if ok:
        return 3.5
    return nil

fn main() -> i64:
    val r: u64? = get_u64(true)
    val ri: i64? = get_i64(true)
    val rf: f64? = get_f64(true)
    unsafe:
        val a = r as u64
        if a != 42u64:
            return 1
        val rendered = "{r as u64}"
        if rendered != "42":
            return 2
        val b = ri as u64
        if b != 77u64:
            return 3
        val c = r as i64
        if c != 42:
            return 4
        val f = rf as f64
        if f < 3.4 or f > 3.6:
            return 5
    0
"#;
    assert_eq!(run_jit(source), 0);
}

#[test]
fn bug4_text_repeat_parse_ptr_and_helpers_in_jit() {
    let source = r#"
fn main() -> i64:
    if " ".repeat(4) != "    ":
        return 1
    if "x".repeat(-2) != "":
        return 2
    val ok_num = "42".parse_i64() ?? -1
    if ok_num != 42:
        return 3
    val bad_num = "bad".parse_i64() ?? -99
    if bad_num != -99:
        return 4
    unsafe:
        val p = "hi".ptr()
        if p == 0:
            return 5
    if "hello".capitalize() != "Hello":
        return 6
    if !"12345".is_digit() or "12a".is_digit():
        return 7
    if "7".pad_left(3, "0") != "007":
        return 8
    if "hello".substr(1, 3) != "ell":
        return 9
    if "hello".substr(2) != "llo":
        return 10
    if "hello".substring(1, 4) != "ell":
        return 14
    val parts = "a=b".partition("=")
    if parts.len() != 3 or parts[0] != "a" or parts[1] != "=" or parts[2] != "b":
        return 11
    if "cab".sorted() != "abc":
        return 12
    if "héllo".char_count() != 5:
        return 13
    0
"#;
    assert_eq!(run_jit(source), 0);
}

#[test]
fn bug5_dispatch_worklist_clean_lowering_methods_in_jit() {
    let source = r#"
fn main() -> i64:
    val xs = [3, 1, 2]
    val desc = xs.sort_desc()
    if desc.len() != 3 or desc[0] != 3 or desc[1] != 2 or desc[2] != 1:
        return 1
    if xs[0] != 3 or xs[1] != 1 or xs[2] != 2:
        return 2
    val asc = xs.sorted()
    if asc[0] != 1 or asc[1] != 2 or asc[2] != 3:
        return 3
    val zipped = [1, 2].zip([10, 20, 30])
    if zipped.len() != 2:
        return 4
    if [1, 2, 3].take(2).len() != 2:
        return 5
    if [1, 2, 3].take(-1).len() != 0:
        return 6
    val skipped = [1, 2, 3].skip(1)
    if skipped.len() != 2 or skipped[0] != 2 or skipped[1] != 3:
        return 7
    val dropped = [1, 2, 3].drop(1)
    if dropped.len() != 2 or dropped[0] != 2:
        return 8
    if "abc".appended("d") != "abcd":
        return 9
    if "abc".prepended("z") != "zabc":
        return 10
    if "abcdef".substr(1, 3) != "bcd":
        return 11
    if "abcdef".substring(1, 4) != "bcd":
        return 13
    if "hello".char_count() != 5:
        return 12
    0
"#;
    assert_eq!(run_jit(source), 0);
}

#[test]
fn bug2_stdio_facade_symbols_register_in_static_jit_provider() {
    use simple_native_loader::{static_provider, RuntimeSymbolProvider};
    simple_runtime::register_static_runtime_symbols();
    let provider = static_provider();
    for sym in ["rt_stdin_read", "rt_stdin_read_all", "rt_term_write", "rt_term_flush"] {
        assert!(
            provider.has_symbol(sym) && provider.get_symbol(sym).is_some(),
            "static runtime provider missing {sym}"
        );
    }
}

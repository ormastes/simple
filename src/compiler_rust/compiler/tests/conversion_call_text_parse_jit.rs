//! Cranelift JIT: the conversion CALL form `f64(text)` / `i32(text)` /
//! `i8(text)` / ... parses its text argument, exactly like `text.to_f64()` /
//! `text.to_int()` and like the interpreter's `T(x)` builtins
//! (`interpreter_call/builtins.rs`): unparsable text is `0.0` / `0`.
//! HIR lowered `T(x)` to the same `Cast` as `x as T`, whose text->number rule
//! is the single-character code point (`"x" as f64 == 120.0`), so under the
//! JIT `f64("x")` returned `120.0` and `i32("5")` returned `53`-class values.
//! Expected values are the interpreter's.
//! doc/08_tracking/bug/float_parse_call_failure_value_differs_from_seed_2026-10-10.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    simple_runtime::register_static_runtime_symbols();
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("MIR must compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn f64_call_of_unparsable_text_is_zero() {
    let source = r#"
fn main() -> i64:
    if f64("x") != 0.0:
        return 1
    if f64("1.5") != 1.5:
        return 2
    if f32("2.5") != 2.5:
        return 3
    0
"#;
    assert_eq!(run(source), 0);
}

#[test]
fn narrow_int_conversion_calls_parse_text_and_wrap() {
    let source = r#"
fn main() -> i64:
    val a: i64 = i32("5")
    val b: i64 = i8("7")
    val c: i64 = i16("9")
    val d: i64 = u8("200")
    val e: i64 = i64("12")
    val f: i64 = i32("x")
    val g: i64 = i8(300)
    a + b + c + d + e + f + g
"#;
    // 5 + 7 + 9 + 200 + 12 + 0 + 44
    assert_eq!(run(source), 277);
}

/// The `as` cast keeps its distinct single-character code-point rule
/// (`interpreter/expr/casting.rs`): only the call form parses.
#[test]
fn as_cast_of_single_char_text_keeps_code_point() {
    let source = r#"
fn main() -> i64:
    val s = "x"
    val f = s as f64
    if f != 120.0:
        return 1
    0
"#;
    assert_eq!(run(source), 0);
}

/// `int(text)` on a SINGLE-character text parses it like `text.to_int()`:
/// `int("6") == 6`, not the code point 54. Multi-char text was already right
/// (`int("13") == 13`), which hid the defect. Covers the similar shapes the
/// LSP sweep hit: literal, local, `[text]` element, fn return, slice, index.
/// doc/08_tracking/bug/lsp_refactor_tooling_audit_2026_11_07.md
/// (int_builtin_text_single_char_returns_char_code_jit_2026_11_07)
#[test]
fn int_call_of_single_char_text_parses_not_code_point() {
    let source = r#"
fn get(xs: [text], i: i64) -> text:
    xs[i]
fn main() -> i64:
    val a = "6"
    val xs = ["7", "13"]
    val s = "x5y"
    if int("6") != 6:
        return 1
    if int(a) != 6:
        return 2
    if int(xs[0]) != 7:
        return 3
    if int(get(xs, 0)) != 7:
        return 4
    if int(s[1:2]) != 5:
        return 5
    if int(s[1]) != 5:
        return 6
    if i64("0") != 0:
        return 7
    if int("x") != 0:
        return 8
    if int(xs[1]) != 13:
        return 9
    0
"#;
    assert_eq!(run(source), 0);
}

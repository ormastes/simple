//! `x as <int>` where `x` is one-codepoint TEXT held in an `any` slot must
//! yield that CODE POINT, like the interpreter (`"6" as i64 == 54`) and like
//! the STRING-typed cast arm (`rt_value_as_int`). `char_at` has no static
//! return type, so `s.char_at(i) as i64` is exactly this case. MIR lowered the
//! `any -> <int>` arm through `rt_any_to_int`, whose text leg PARSES (it backs
//! `.to_i64()`), so every ASCII digit became its numeric value and the
//! web renderer's PPM header began `P\x06` under the JIT.
//! doc/08_tracking/bug/char_at_as_i64_parses_digit_jit_ppm_header_2026-11-23.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    let mir_module = mir::lower_to_mir(&hir_module).expect("source must lower to MIR");
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    unsafe { jit.call_i64_void("main").expect("main must execute") }
}

#[test]
fn char_at_digit_as_i64_is_code_point() {
    let src = r#"
fn main() -> i64:
    val header = "P6\n12 34\n255\n"
    val d = header.char_at(1) as i64
    d
"#;
    assert_eq!(run(src), 54);
}

#[test]
fn char_at_header_bytes_match_code_points() {
    // Whole PPM header: every byte must equal its code point. Folded as a
    // checksum so `main` stays a small exit code.
    let src = r#"
fn main() -> i64:
    val header = "P6\n12 34\n255\n"
    var i = 0
    var acc = 0
    while i < header.len():
        acc = acc + (header.char_at(i) as i64) * (i + 1)
        i = i + 1
    acc % 251
"#;
    let expected: i64 = b"P6\n12 34\n255\n"
        .iter()
        .enumerate()
        .map(|(i, b)| (*b as i64) * (i as i64 + 1))
        .sum::<i64>()
        % 251;
    assert_eq!(run(src), expected);
}

#[test]
fn any_one_codepoint_text_as_int_is_code_point() {
    let src = r#"
fn box_any(v: any) -> any:
    v

fn main() -> i64:
    val digit = box_any("6")
    val letter = box_any("P")
    val accent = box_any("é")
    unsafe:
        val a = digit as i64
        val b = letter as i32
        val c = accent as i64
        var ok = 0
        if a == 54:
            ok = ok + 1
        if b == 80:
            ok = ok + 10
        if c == 233:
            ok = ok + 100
        ok
"#;
    assert_eq!(run(src), 111);
}

#[test]
fn to_i64_method_still_parses_text() {
    // `.to_i64()` keeps PARSE semantics on typed and erased receivers; only
    // the `as` cast takes the code point.
    let src = r#"
fn box_any(v: any) -> any:
    v

fn main() -> i64:
    val s = "6"
    val xs: [any] = [box_any("7")]
    s.to_i64() * 10 + xs[0].to_i64()
"#;
    assert_eq!(run(src), 67);
}

#[test]
fn any_float_int_bool_cast_legs_unchanged() {
    let src = r#"
fn box_any(v: any) -> any:
    v

fn main() -> i64:
    val f = box_any(41.75)
    val i = box_any(42)
    val t = box_any(true)
    unsafe:
        val a = f as i64
        val b = i as i64
        val c = t as i64
        a * 100 + b + c
"#;
    assert_eq!(run(src), 4143);
}

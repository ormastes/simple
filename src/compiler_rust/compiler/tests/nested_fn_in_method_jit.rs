//! A `fn` declared inside a METHOD body (an `impl` method or a class method)
//! must lower exactly like one declared inside a free function body: as a
//! local closure binding. Before the fix, HIR lowering did not register it, so
//! the call site failed with `Unknown variable: <name>` and the whole program
//! fell back to the interpreter (`JIT compilation failed, falling back to
//! interpreter: HIR lowering error: Unknown variable: clamp_f while lowering
//! EngineColor.to_rgba8`).
//!
//! "No fallback" is asserted directly: the JIT fallback is triggered by
//! `hir::lower` / `mir::lower_to_mir` / `compile_module` returning `Err`, so
//! each stage must succeed and the value must come from JIT-compiled `main`.
//!
//! Bug: doc/08_tracking/bug/jit_lowering_clamp_f_engine_color_2026-07-02.md

use simple_compiler::codegen::JitCompiler;
use simple_compiler::{hir, mir};
use simple_parser::Parser;

fn run_jit_no_fallback(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("source must parse");
    let hir_module = match hir::lower(&ast) {
        Ok(m) => m,
        Err(e) => panic!("HIR lowering failed (JIT would fall back to the interpreter): {e}"),
    };
    let mir_module = match mir::lower_to_mir(&hir_module) {
        Ok(m) => m,
        Err(e) => panic!("MIR lowering failed (JIT would fall back to the interpreter): {e}"),
    };
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    if let Err(e) = jit.compile_module(&mir_module) {
        panic!("JIT compile failed (would fall back to the interpreter): {e}");
    }
    unsafe { jit.call_i64_void("main").expect("main must execute under the JIT") }
}

/// The original incident shape: a nested fn inside a method of an `impl` block.
#[test]
fn nested_fn_inside_impl_method_runs_under_jit() {
    let source = r#"
struct Color:
    r: i64

impl Color:
    fn to_byte() -> i64:
        fn clamp_f(v: i64) -> i64:
            if v < 0:
                return 0
            if v > 255:
                return 255
            v
        clamp_f(self.r) + clamp_f(-5) + clamp_f(1000)

fn main() -> i64:
    val c = Color(r: 7)
    c.to_byte()
"#;
    assert_eq!(run_jit_no_fallback(source), 7 + 0 + 255);
}

/// The exact pre-workaround `EngineColor.to_rgba8` shape (commit e66eff434bb
/// hoisted it): an f64-parameter nested fn called four times inside a struct
/// constructor in an impl method.
#[test]
fn original_engine_color_to_rgba8_shape_runs_under_jit() {
    let source = r#"
struct Rgba8:
    r: i64
    g: i64
    b: i64
    a: i64

struct EngineColor:
    r: f64
    g: f64
    b: f64
    a: f64

impl EngineColor:
    fn to_rgba8() -> Rgba8:
        fn clamp_f(v: f64) -> i64:
            val i = (v * 255.0).to_i64()
            if i < 0:
                return 0
            if i > 255:
                return 255
            i
        Rgba8(r: clamp_f(self.r), g: clamp_f(self.g), b: clamp_f(self.b), a: clamp_f(self.a))

fn main() -> i64:
    val c = EngineColor(r: 1.0, g: 0.5, b: -1.0, a: 2.0)
    val p = c.to_rgba8()
    p.r * 1000000000 + p.g * 1000000 + p.b * 1000 + p.a
"#;
    assert_eq!(
        run_jit_no_fallback(source),
        255 * 1000000000 + 127 * 1000000 + 0 * 1000 + 255
    );
}

/// Same shape inside a class method.
#[test]
fn nested_fn_inside_class_method_runs_under_jit() {
    let source = r#"
class Counter:
    n: i64

    fn scaled(k: i64) -> i64:
        fn mul(a: i64, b: i64) -> i64:
            a * b
        mul(self.n, k) + 1

fn main() -> i64:
    val c = Counter(n: 6)
    c.scaled(7)
"#;
    assert_eq!(run_jit_no_fallback(source), 43);
}

/// A nested fn calling an earlier nested fn in the same method body.
#[test]
fn nested_fn_calling_nested_fn_inside_method_runs_under_jit() {
    let source = r#"
struct P:
    x: i64

impl P:
    fn combo() -> i64:
        fn inc(v: i64) -> i64:
            v + 1
        fn twice_inc(v: i64) -> i64:
            inc(inc(v)) * 2
        twice_inc(self.x)

fn main() -> i64:
    val p = P(x: 10)
    p.combo()
"#;
    assert_eq!(run_jit_no_fallback(source), 24);
}

/// Value pins for the nested-fn-calls-nested-fn family across return/param
/// types and body shapes. Each fell back at base (closure ABI `ANY` boundary)
/// except where noted; under the declared-signature binding each must answer
/// the interpreter's value, never a wrong one.
#[test]
fn nested_fn_calling_nested_fn_shapes_keep_their_values() {
    let cases: &[(&str, &str, i64)] = &[
        ("bool return", "fn main() -> i64:\n    fn pos(v: i64) -> bool:\n        v > 0\n    fn cnt(v: i64) -> i64:\n        if pos(v):\n            return 1\n        0\n    cnt(5) * 10 + cnt(-5)\n", 10),
        ("f64", "fn main() -> i64:\n    fn half(v: f64) -> f64:\n        v / 2.0\n    fn quarter(v: f64) -> f64:\n        half(half(v))\n    (quarter(10.0) * 100.0).to_i64()\n", 250),
        ("text", "fn main() -> i64:\n    fn greet(n: text) -> text:\n        \"hi \" + n\n    fn glen(n: text) -> i64:\n        greet(n).len()\n    glen(\"bob\")\n", 6),
        ("method-call tail", "fn main() -> i64:\n    fn ln(s: text) -> i64:\n        s.len()\n    fn twice(s: text) -> i64:\n        ln(s) * 2\n    twice(\"abcd\")\n", 8),
        ("if/else return", "fn main() -> i64:\n    fn sgn(v: i64) -> i64:\n        if v < 0:\n            return -1\n        else:\n            return 1\n    fn mag(v: i64) -> i64:\n        v * sgn(v)\n    mag(-7) + mag(3)\n", 10),
        ("if/else tail", "fn main() -> i64:\n    fn f(v: i64) -> i64:\n        if v > 0:\n            v\n        else:\n            0 - v\n    fn g(v: i64) -> i64:\n        f(v) + f(0 - v)\n    g(21)\n", 42),
        ("capture", "fn main() -> i64:\n    val k = 5\n    fn add_k(a: i64) -> i64:\n        a + k\n    fn add2k(a: i64) -> i64:\n        add_k(add_k(a))\n    add2k(32)\n", 42),
        // Capture snapshots at the declaration point, as in the interpreter.
        ("var rebound after decl", "fn main() -> i64:\n    var k = 1\n    fn get_k(a: i64) -> i64:\n        a + k\n    fn wrap(a: i64) -> i64:\n        get_k(a) * 10\n    k = 100\n    wrap(0)\n", 10),
        ("struct return", "struct P:\n    x: i64\n\nfn main() -> i64:\n    fn mk(v: i64) -> P:\n        P(x: v)\n    fn mk2(v: i64) -> P:\n        mk(v + 1)\n    mk2(41).x\n", 42),
        // Already compiled at base; must not move.
        ("passed as value", "fn apply(f: fn(i64) -> i64, x: i64) -> i64:\n    f(x)\n\nfn main() -> i64:\n    fn inc(v: i64) -> i64:\n        v + 1\n    val xs = [1, 2, 3].map(inc)\n    apply(inc, 40) + xs[2]\n", 45),
        ("generic outer fn", "fn wrap<T>(x: T) -> T:\n    fn id(v: T) -> T:\n        v\n    id(x)\n\nfn main() -> i64:\n    wrap(42)\n", 42),
        ("generic class method", "class Bx<T>:\n    v: T\n\n    fn get() -> T:\n        fn id(a: T) -> T:\n            a\n        id(self.v)\n\nfn main() -> i64:\n    Bx(v: 42).get()\n", 42),
        ("Self return", "struct P:\n    x: i64\n\nimpl P:\n    fn bump() -> P:\n        fn mk(v: i64) -> Self:\n            P(x: v)\n        mk(self.x + 1)\n\nfn main() -> i64:\n    P(x: 41).bump().x\n", 42),
    ];
    for (name, source, want) in cases {
        let got = std::panic::catch_unwind(|| run_jit_no_fallback(source));
        match got {
            Ok(v) => assert_eq!(v, *want, "shape `{name}` answered a wrong value under the JIT"),
            Err(_) => panic!("shape `{name}` did not compile under the JIT (see panic above)"),
        }
    }
}

/// Control: the already-working free-function shape stays green.
#[test]
fn nested_fn_inside_free_function_runs_under_jit() {
    let source = r#"
fn outer(x: i64) -> i64:
    fn inc(v: i64) -> i64:
        v + 1
    fn twice_inc(v: i64) -> i64:
        inc(inc(v)) * 2
    twice_inc(x)

fn main() -> i64:
    outer(10)
"#;
    assert_eq!(run_jit_no_fallback(source), 24);
}

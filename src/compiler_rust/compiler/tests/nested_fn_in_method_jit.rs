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
    assert_eq!(run_jit_no_fallback(source), 255 * 1000000000 + 127 * 1000000 + 0 * 1000 + 255);
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

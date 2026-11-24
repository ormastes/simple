//! A float flowing into an int-typed parameter or returned from an
//! int-typed function is a TYPE ERROR (owner decision 2026-11-24): the
//! program must say `as iN` / `.to_iN()`, which saturates the same way on
//! every engine. Before, the seed accepted it silently and the engines
//! disagreed: `r32(2.5)` returned `2.5` in the interpreter and the f64 bits
//! on the JIT; `take8(300.5)` gave 300 vs 0.
//! Bug: doc/08_tracking/bug/float_passed_to_int_typed_param_or_return_engines_disagree_2026-11-24.md
//!
//! int -> float widening stays allowed (owner decision 2026-11-13).

use simple_compiler::hir;
use simple_parser::Parser;

fn lower(src: &str) -> Result<(), String> {
    let ast = Parser::new(src).parse().map_err(|e| format!("parse: {e}"))?;
    hir::lower(&ast).map(|_| ()).map_err(|e| format!("{e}"))
}

fn assert_rejected(case: &str, src: &str) {
    match lower(src) {
        Ok(()) => panic!("{case}: a float into an int slot must be a type error, but it lowered"),
        Err(e) => assert!(
            e.to_lowercase().contains("mismatch"),
            "{case}: expected a type-mismatch error, got: {e}"
        ),
    }
}

fn assert_accepted(case: &str, src: &str) {
    if let Err(e) = lower(src) {
        panic!("{case}: must still compile, got: {e}");
    }
}

#[test]
fn float_returned_from_int_typed_function_is_rejected() {
    assert_rejected("implicit tail", "fn r32(x: f64) -> i32:\n    x\n\nfn main() -> i64:\n    r32(2.5) as i64\n");
    assert_rejected(
        "explicit return",
        "fn r(x: f64) -> i64:\n    if x > 0.0:\n        return x * 2.0\n    0\n\nfn main() -> i64:\n    r(1.5)\n",
    );
    assert_rejected("float literal tail", "fn k() -> u8:\n    3.5\n\nfn main() -> i64:\n    k() as i64\n");
}

#[test]
fn float_passed_to_int_typed_parameter_is_rejected() {
    assert_rejected(
        "free fn arg",
        "fn take8(v: u8) -> i64:\n    v as i64\n\nfn main() -> i64:\n    take8(300.5)\n",
    );
    assert_rejected(
        "nested call result",
        "fn half(x: f64) -> f64:\n    x / 2.0\n\nfn take(n: i64) -> i64:\n    n + 1\n\nfn main() -> i64:\n    take(half(5.0))\n",
    );
    assert_rejected(
        "float local",
        "fn take(n: i32) -> i64:\n    n as i64\n\nfn main() -> i64:\n    val f: f64 = 2.0\n    take(f)\n",
    );
    assert_rejected(
        "method arg",
        "class Counter:\n    n: i64\n    me add(k: i64):\n        self.n = self.n + k\n\nfn main() -> i64:\n    var c = Counter(n: 0)\n    c.add(1.5)\n    c.n\n",
    );
    assert_rejected(
        "generic fn, concrete int slot",
        "fn rep<T>(x: T, n: i64) -> i64:\n    n\n\nfn main() -> i64:\n    rep(1, 2.5)\n",
    );
    assert_rejected(
        "call through a function-typed value",
        "fn inc(n: i64) -> i64:\n    n + 1\n\nfn apply(f: fn(i64) -> i64, v: f64) -> i64:\n    f(v)\n\nfn main() -> i64:\n    apply(inc, 1.5)\n",
    );
}

#[test]
fn widening_and_explicit_casts_still_compile() {
    assert_accepted(
        "int arg into float param",
        "fn half(x: f64) -> f64:\n    x / 2.0\n\nfn main() -> i64:\n    half(3) as i64\n",
    );
    assert_accepted("int tail in float fn", "fn w() -> f64:\n    3\n\nfn main() -> i64:\n    w() as i64\n");
    assert_accepted(
        "explicit as casts",
        "fn take8(v: u8) -> i64:\n    v as i64\n\nfn r32(x: f64) -> i32:\n    x as i32\n\nfn main() -> i64:\n    take8(300.5 as u8) + r32(2.5) as i64\n",
    );
    assert_accepted(
        "to_iN conversion",
        "fn take(n: i64) -> i64:\n    n\n\nfn main() -> i64:\n    val f = 2.5\n    take(f.to_i64())\n",
    );
    assert_accepted(
        "generic slot takes a float",
        "fn id<T>(x: T) -> T:\n    x\n\nfn main() -> i64:\n    val y = id(2.5)\n    1\n",
    );
    assert_accepted(
        "int into int and float into float",
        "fn a(n: i32, x: f32) -> i64:\n    n as i64\n\nfn main() -> i64:\n    a(3, 1.5)\n",
    );
}

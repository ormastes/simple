//! seed_jit_explicit_f64_option_some_typed_readers_lose_low_mantissa_bits_2026-11-27:
//! an explicit `Some(x)` of a typed `f64?` / `Option<f64>` is the Option enum
//! holding the RAW IEEE bits of `x`. The typed readers (`??`, `if val`,
//! `.unwrap()`, returns, `[f64?]` elements, struct fields) decoded that word as
//! a tagged float and dropped the low 3 mantissa bits (`Some(0.1)` read back
//! 0.09999999999999998). Each reader sets one bit of the result on
//! a mismatch; 0 means every reader returned `x` exactly (equal, same sign of
//! zero, NaN stays NaN).
use simple_parser::Parser;

fn jit_evaluate(source: &str) -> i64 {
    let ast = Parser::new(source).parse().expect("valid source");
    let mut lowerer = simple_compiler::hir::Lowerer::new();
    lowerer.set_strict_mode(false);
    lowerer.set_lenient_types(true);
    let hir = lowerer.lower_module(&ast).expect("HIR lowering");
    let mir = simple_compiler::mir::lower_to_mir(&hir).expect("MIR lowering");
    let mut jit = simple_compiler::codegen::JitCompiler::new_static().expect("static JIT");
    jit.compile_module(&mir).expect("JIT compilation");
    unsafe { jit.call_i64_void("main").expect("JIT execution") }
}

const READERS: &str = "struct Holder:
    a: f64?

fn same(g: f64, w: f64) -> bool:
    if w != w:
        return g != g
    if w == 0.0:
        return g == 0.0 and (1.0 / g) == (1.0 / w)
    g == w

fn bit(ok: bool, k: i64) -> i64:
    if ok:
        return 0
    k

fn mk(x: f64) -> f64?:
    return Some(x)

fn mk_flat(x: f64) -> f64?:
    return x

fn mko(x: f64) -> Option<f64>:
    return Some(x)

fn readers(x: f64) -> i64:
    var r = 0
    val c: f64? = Some(x)
    r = r + bit(same(c ?? 9.0, x), 1)
    var iv = 9.0
    if val v = c:
        iv = v
    r = r + bit(same(iv, x), 2)
    r = r + bit(same(c.unwrap(), x), 4)
    var mv = 9.0
    match c:
        Some(v): mv = v
        None: mv = 8.0
    r = r + bit(same(mv, x), 8)
    r = r + bit(same(mk(x) ?? 9.0, x), 16)
    r = r + bit(same(mk(x).unwrap(), x), 32)
    r = r + bit(same(mk_flat(x) ?? 9.0, x), 64)
    r = r + bit(same(mk_flat(x).unwrap(), x), 128)
    r = r + bit(same(mko(x) ?? 9.0, x), 256)
    r = r + bit(same(mko(x).unwrap(), x), 512)
    val xs: [f64?] = [Some(x), None]
    r = r + bit(same(xs[0] ?? 9.0, x), 1024)
    var ev = 9.0
    if val e = xs[0]:
        ev = e
    r = r + bit(same(ev, x), 2048)
    val h = Holder(a: Some(x))
    r = r + bit(same(h.a ?? 9.0, x), 4096)
    r = r + bit(same(h.a.unwrap(), x), 8192)
    r
";

fn readers_for(value_expr: &str) -> i64 {
    let source = format!("{READERS}\nfn main() -> i64:\n    readers({value_expr})\n");
    jit_evaluate(&source)
}

#[test]
fn jit_f64_option_some_readers_keep_exact_bits_for_point_one() {
    assert_eq!(readers_for("0.1"), 0);
}

/// Bits 2: the low 3 bits equal TAG_FLOAT.
#[test]
fn jit_f64_option_some_readers_keep_exact_bits_for_denormal_two() {
    assert_eq!(readers_for("4.9e-324 * 2.0"), 0);
}

/// Bits 3: the raw payload word equals the nil sentinel. Every reader but `??`
/// is exact; `??` keeps its `Some(nil)` default test (an untyped `Some(nil)`
/// in an `f64?` slot is the same word), so it still takes the default. That
/// ambiguity needs a tag separate from the payload:
/// seed_typed_f64_option_some_heap_allocates_per_some_never_released_2026-11-27
#[test]
fn jit_f64_option_some_readers_keep_exact_bits_for_denormal_nil_word() {
    const COALESCE_READERS: i64 = 1 | 16 | 256 | 1024 | 4096;
    assert_eq!(readers_for("4.9e-324 * 3.0") & !COALESCE_READERS, 0);
}

#[test]
fn jit_f64_option_some_readers_keep_exact_bits_for_tiny_normal() {
    assert_eq!(readers_for("1e-300"), 0);
}

#[test]
fn jit_f64_option_some_readers_keep_negative_zero_inf_and_nan() {
    assert_eq!(readers_for("-0.0"), 0);
    assert_eq!(readers_for("1.0 / 0.0"), 0);
    assert_eq!(readers_for("0.0 / 0.0"), 0);
}

#[test]
fn jit_f32_option_some_readers_keep_exact_value() {
    let source = "fn main() -> i64:\n    val n: f32? = Some(0.1)\n    val w: f32 = 0.1\n    var r = 0\n    if (n ?? 9.0) != w:\n        r = r + 1\n    if n.unwrap() != w:\n        r = r + 2\n    if val v = n:\n        if v != w:\n            r = r + 4\n    r\n";
    assert_eq!(jit_evaluate(source), 0);
}

/// The Option enum can also hold a TAGGED heap float: `[f64].at`, a generic
/// `T?` producer and an untyped `Some(x)` box the payload. The typed readers
/// (including the typed `match Some(v)` arm) must read those as floats, not
/// reinterpret the boxed word as raw bits.
#[test]
fn jit_f64_option_readers_keep_boxed_payload_producers() {
    let source = "fn pick<T>(xs: [T]) -> T?:\n    return Some(xs[0])\n\nfn w(x):\n    return Some(x)\n\nfn miss(ok: bool) -> i64:\n    if ok:\n        return 0\n    1\n\nfn readers(c: f64?, x: f64) -> i64:\n    var r = miss((c ?? 9.0) == x)\n    var iv = 9.0\n    if val v = c:\n        iv = v\n    r = r + miss(iv == x)\n    r = r + miss(c.unwrap() == x)\n    var mv = 9.0\n    match c:\n        Some(v): mv = v\n        None: mv = 8.0\n    r + miss(mv == x)\n\nfn main() -> i64:\n    val xs: [f64] = [0.1, 0.2]\n    val a: f64? = xs.at(0)\n    val q: f64? = pick(xs)\n    val u: f64? = w(0.1)\n    readers(a, 0.1) + readers(q, 0.1) * 10 + readers(u, 0.1) * 100\n";
    assert_eq!(jit_evaluate(source), 0);
}

/// Bit-for-bit through the inline `spl_f64_to_bits` / `spl_bits_to_f64`
/// intrinsics: a quiet NaN with low payload bits, a negative NaN, and the
/// denormals whose raw word carries the heap tag (bits 1 and 9), the TAG_FLOAT
/// pattern (2); the nil word (3) is covered without `??` above.
#[test]
fn jit_f64_option_some_readers_are_bit_exact_for_nan_payloads_and_tag_patterns() {
    let source = "extern fn spl_f64_to_bits(value: f64) -> i64\nextern fn spl_bits_to_f64(bits: i64) -> f64\n\nfn mk(x: f64) -> f64?:\n    return Some(x)\n\nfn chk(bits: i64) -> i64:\n    val x = spl_bits_to_f64(bits)\n    val c: f64? = Some(x)\n    var r = 0\n    if spl_f64_to_bits(c ?? 9.0) != bits:\n        r = r + 1\n    if spl_f64_to_bits(c.unwrap()) != bits:\n        r = r + 2\n    if val v = c:\n        if spl_f64_to_bits(v) != bits:\n            r = r + 4\n    match c:\n        Some(v):\n            if spl_f64_to_bits(v) != bits:\n                r = r + 8\n        None: r = r + 16\n    if spl_f64_to_bits(mk(x) ?? 9.0) != bits:\n        r = r + 32\n    r\n\nfn main() -> i64:\n    chk(9221120237041090565) + chk(-2251799813685243) * 64 + chk(1) * 4096 + chk(9) * 262144 + chk(2) * 16777216\n";
    assert_eq!(jit_evaluate(source), 0);
}

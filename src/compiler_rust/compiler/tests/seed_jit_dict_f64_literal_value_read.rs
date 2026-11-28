//! seed_jit_dict_f64_literal_value_read_loses_low_mantissa_bits_2026-11-27:
//! a `{text: f64}` dict literal stores its values through `rt_dict_set`,
//! which takes TAGGED RuntimeValues, but the dict-literal lowering passed the
//! RAW f64 bit-pattern. Every typed read (`d[k]`, `d.get(k)` with `??` /
//! `if val` / `.unwrap()` / `match`) decodes the stored word with
//! `UnboxFloat` -> `rt_value_as_float`, which interprets a raw f64
//! bit-pattern whose low 3 bits alias TAG_FLOAT (0b010) as a legacy inline
//! float and shifts the payload, zeroing the low 3 mantissa bits
//! (`{"k": 0.1}` read back 0.09999999999999998 = 0x3fb9999999999998).
//! The `.set` / `.insert` method path shared the same raw write. Each reader
//! sets one bit of the result on a mismatch; 0 means every reader returned
//! `x` exactly (equal, same sign of zero, NaN stays NaN).
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

const HELPERS: &str = "fn same(g: f64, w: f64) -> bool:
    if w != w:
        return g != g
    if w == 0.0:
        return g == 0.0 and (1.0 / g) == (1.0 / w)
    g == w

fn bit(ok: bool, k: i64) -> i64:
    if ok:
        return 0
    k

";

/// Every typed read of a `{text: f64}` LITERAL value, bitmask per reader:
/// 1 `d[k]`, 2 `d.get(k) ?? default`, 4 `if val`, 8 `.unwrap()`,
/// 16 `match Some(v)`.
const LITERAL_READERS: &str = "fn readers(x: f64) -> i64:
    val d: {text: f64} = {\"k\": x}
    var r = bit(same(d[\"k\"], x), 1)
    val g: f64? = d.get(\"k\")
    r = r + bit(same(g ?? 9.0, x), 2)
    var iv = 9.0
    if val v = g:
        iv = v
    r = r + bit(same(iv, x), 4)
    r = r + bit(same(g.unwrap(), x), 8)
    var mv = 9.0
    match g:
        Some(v): mv = v
        None: mv = 8.0
    r + bit(same(mv, x), 16)

fn main() -> i64:
    readers(0.1) + readers(4.9e-324 * 2.0) * 32 + readers(1e-300) * 1024 + readers(-0.0) * 32768
";

#[test]
fn jit_dict_f64_literal_value_reads_keep_exact_bits() {
    let source = format!("{HELPERS}{LITERAL_READERS}");
    assert_eq!(jit_evaluate(&source), 0);
}

/// Bit-for-bit through the inline `spl_f64_to_bits` / `spl_bits_to_f64`
/// intrinsics: a quiet NaN with low payload bits, the denormals whose raw
/// word carries the heap tag (1) and TAG_FLOAT pattern (2), and a negative
/// NaN. Stored words must round-trip exactly regardless of which tag
/// pattern their low 3 bits alias.
#[test]
fn jit_dict_f64_literal_value_reads_are_bit_exact_for_nan_payloads_and_tag_patterns() {
    let source = format!(
        "{HELPERS}extern fn spl_f64_to_bits(value: f64) -> i64
extern fn spl_bits_to_f64(bits: i64) -> f64

fn chk(bits: i64) -> i64:
    val x = spl_bits_to_f64(bits)
    val d: {{text: f64}} = {{\"k\": x}}
    var r = 0
    if spl_f64_to_bits(d[\"k\"]) != bits:
        r = r + 1
    val g: f64? = d.get(\"k\")
    if spl_f64_to_bits(g ?? 9.0) != bits:
        r = r + 2
    if val v = g:
        if spl_f64_to_bits(v) != bits:
            r = r + 4
    if spl_f64_to_bits(g.unwrap()) != bits:
        r = r + 8
    r

fn main() -> i64:
    chk(9221120237041090565) + chk(1) * 16 + chk(2) * 256 + chk(-2251799813685243) * 4096
"
    );
    assert_eq!(jit_evaluate(&source), 0);
}

/// The `.set` / `.insert` method path emits its own `rt_dict_set` call with
/// the same raw-value defect as the literal; `d[k] = v` (rt_index_set)
/// already boxed floats and is the control.
#[test]
fn jit_dict_f64_insert_value_writes_keep_exact_bits() {
    let source = format!(
        "{HELPERS}fn readers(x: f64) -> i64:
    var d: {{text: f64}} = {{}}
    d.insert(\"k\", x)
    var r = bit(same(d[\"k\"], x), 1)
    val g: f64? = d.get(\"k\")
    r + bit(same(g ?? 9.0, x), 2)

fn control(x: f64) -> i64:
    var d: {{text: f64}} = {{}}
    d[\"k\"] = x
    var r = bit(same(d[\"k\"], x), 4)
    val g: f64? = d.get(\"k\")
    r + bit(same(g ?? 9.0, x), 8)

fn main() -> i64:
    readers(0.1) + control(0.1) * 16
"
    );
    assert_eq!(jit_evaluate(&source), 0);
}

/// A `{text: f32}` literal value: BoxFloat promotes f32 to f64, so the
/// stored heap box and the f32-typed `d[k]` read must round-trip 0.1f
/// exactly. (`.get` on an `f32?` goes through the inline-f64 Option
/// readers, a separate consumer path — the f64 arms above pin that
/// contract for `f64?`.)
#[test]
fn jit_dict_f32_literal_value_reads_keep_exact_value() {
    let source = "extern fn spl_f64_to_bits(value: f64) -> i64
extern fn spl_bits_to_f64(bits: i64) -> f64

fn main() -> i64:
    val d: {text: f32} = {\"k\": 0.1}
    var r = 0
    if d[\"k\"] != 0.1:
        r = r + 1
    # The literal 0.1 keeps its f64 bits (0x3FB999999999999A) in an
    # f32-typed dict; the raw-store bug read them back shifted
    # (0x3FB9999999999998).
    if spl_f64_to_bits(d[\"k\"]) != spl_f64_to_bits(spl_bits_to_f64(4591870180066957722)):
        r = r + 2
    r
";
    assert_eq!(jit_evaluate(source), 0);
}

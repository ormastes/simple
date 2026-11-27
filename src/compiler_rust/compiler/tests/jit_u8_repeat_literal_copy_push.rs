//! Regression tests for `jit_u8_repeat_literal_copy_push_leak_2026-11-27`.
//!
//! Dynamic `[0u8; n]` (and `: [u8]` `[0; n]`) repeat literals previously lowered
//! through `rt_array_repeat`, allocating an 8-byte-slot unpacked `RuntimeArray`
//! instead of a `BYTE_PACKED` buffer. When copied (`var r: [u8] = a`) and pushed
//! onto (`r.push(...)`), `rt_array_copy` replicated the unpacked layout and each
//! growth reallocated 8 bytes per byte element (e.g. 1024 B vs 128 B per call
//! in PBKDF2's `_pbkdf2_cat_u8` loop).

use std::sync::Mutex;

use simple_compiler::codegen::JitCompiler;
use simple_compiler::interpreter::evaluate_module;
use simple_compiler::{hir, mir};
use simple_parser::Parser;
use simple_runtime::value::heap::{rt_heap_aux_live_bytes, rt_heap_live_bytes};

static HEAP_MEASURE_LOCK: Mutex<()> = Mutex::new(());

fn lower_mir(src: &str, jit: bool) -> mir::MirModule {
    let ast = Parser::new(src).parse().expect("source must parse");
    let hir_module = hir::lower(&ast).expect("source must lower to HIR");
    if jit {
        mir::lower_to_mir_jit(&hir_module)
    } else {
        mir::lower_to_mir(&hir_module)
    }
    .expect("source must lower to MIR")
}

fn call_count(mir_module: &mir::MirModule, fn_name: &str, callee: &str) -> usize {
    let func = mir_module
        .functions
        .iter()
        .find(|f| f.name == fn_name)
        .unwrap_or_else(|| panic!("function {fn_name} not found"));
    func.blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .filter(|inst| matches!(inst, mir::MirInst::Call { target, .. } if target == &mir::CallTarget::from_name(callee)))
        .count()
}

fn run_jit_with_heap_deltas(src: &str) -> (i64, i64, i64) {
    let _guard = HEAP_MEASURE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    simple_runtime::register_static_runtime_symbols();
    let mir_module = lower_mir(src, true);
    let mut jit = JitCompiler::new_static().expect("static Cranelift JIT");
    jit.compile_module(&mir_module).expect("module must JIT-compile");
    let live0 = rt_heap_live_bytes();
    let aux0 = rt_heap_aux_live_bytes();
    let result = unsafe { jit.call_i64_void("main").expect("main must execute") };
    let d_live = rt_heap_live_bytes() - live0;
    let d_aux = rt_heap_aux_live_bytes() - aux0;
    (result, d_live, d_aux)
}

#[test]
fn mir_u8_repeat_uses_byte_array_new_len_not_rt_array_repeat() {
    let src = r#"
fn dyn_u8(n: i64) -> [u8]:
    var out: [u8] = [0u8; n]
    out

fn dyn_inferred_u8(n: i64) -> [u8]:
    var out = [0u8; n]
    out

fn dyn_declared_untyped_zero(n: i64) -> [u8]:
    var out: [u8] = [0; n]
    out

fn dyn_nonzero_u8(n: i64, fill: u8) -> [u8]:
    var out: [u8] = [fill; n]
    out

fn large_const_u8() -> [u8]:
    var out: [u8] = [0u8; 300]
    out

fn dyn_u32_control(n: i64) -> [u32]:
    var out: [u32] = [0u32; n]
    out

fn loop_const64_non_escaping() -> i64:
    var i = 0
    var acc = 0
    while i < 10:
        var buf = [0u8; 64]
        buf[0] = 7u8
        acc = acc + (buf[0] as i64)
        i = i + 1
    acc
"#;
    let mir = lower_mir(src, true);

    for name in ["dyn_u8", "dyn_inferred_u8", "dyn_declared_untyped_zero", "large_const_u8"] {
        assert_eq!(
            call_count(&mir, name, "rt_byte_array_new_len"),
            1,
            "{name} must lower via rt_byte_array_new_len"
        );
        assert_eq!(
            call_count(&mir, name, "rt_array_repeat"),
            0,
            "{name} must not lower via unpacked rt_array_repeat"
        );
        assert_eq!(
            call_count(&mir, name, "rt_array_fill_span"),
            0,
            "{name} zero fill needs no fill_span pass"
        );
    }

    assert_eq!(call_count(&mir, "dyn_nonzero_u8", "rt_byte_array_new_len"), 1);
    assert_eq!(call_count(&mir, "dyn_nonzero_u8", "rt_array_fill_span"), 1);
    assert_eq!(call_count(&mir, "dyn_nonzero_u8", "rt_array_repeat"), 0);

    // Non-u8 repeat literals keep rt_array_repeat.
    assert_eq!(call_count(&mir, "dyn_u32_control", "rt_array_repeat"), 1);
    assert_eq!(call_count(&mir, "dyn_u32_control", "rt_byte_array_new_len"), 0);

    // Constant [0u8; 64] non-escaping loop local registers for S1 block-end release.
    assert_eq!(
        call_count(&mir, "loop_const64_non_escaping", "rt_array_free"),
        1,
        "non-escaping [0u8; 64] local must release at block end under JIT MIR"
    );
}

#[test]
fn jit_u8_repeat_copy_push_is_byte_packed_and_matches_push_built_aux_bytes() {
    let make_src = |use_repeat: bool, iters: i64| {
        let builder = if use_repeat {
            r#"
fn make_pad(n: i64) -> [u8]:
    var out: [u8] = [0u8; n]
    var i: i64 = 0
    while i < n:
        out[i] = ((i ^ 0x36) & 0xff).to_u8()
        i = i + 1
    out
"#
        } else {
            r#"
fn make_pad(n: i64) -> [u8]:
    var out: [u8] = []
    var i: i64 = 0
    while i < n:
        out.push(((i ^ 0x36) & 0xff).to_u8())
        i = i + 1
    out
"#
        };
        format!(
            r#"extern fn rt_array_is_byte_packed(arr: [u8]) -> i64

fn cat_u8(a: [u8], b: [u8]) -> [u8]:
    var r: [u8] = a
    var i: i64 = 0
    val n = b.len() as i64
    while i < n:
        r.push(b[i])
        i = i + 1
    r

{builder}

fn main() -> i64:
    val pad = make_pad(64)
    val msg = make_pad(32)
    if rt_array_is_byte_packed(pad) != 1:
        return -1
    val probe = cat_u8(pad, msg)
    if rt_array_is_byte_packed(probe) != 1:
        return -2
    var j: i64 = 0
    var sum: i64 = 0
    while j < {iters}:
        val c = cat_u8(pad, msg)
        sum = sum + (c[0] as i64) + (c[64] as i64)
        j = j + 1
    sum
"#
        )
    };

    let (push_res_1k, push_live_1k, push_aux_1k) = run_jit_with_heap_deltas(&make_src(false, 1000));
    let (push_res_3k, push_live_3k, push_aux_3k) = run_jit_with_heap_deltas(&make_src(false, 3000));
    let (repeat_res_1k, repeat_live_1k, repeat_aux_1k) = run_jit_with_heap_deltas(&make_src(true, 1000));
    let (repeat_res_3k, repeat_live_3k, repeat_aux_3k) = run_jit_with_heap_deltas(&make_src(true, 3000));

    assert_eq!(push_res_1k, 1000 * (0x36 + 0x36));
    assert_eq!(push_res_3k, 3000 * (0x36 + 0x36));
    assert_eq!(repeat_res_1k, push_res_1k);
    assert_eq!(repeat_res_3k, push_res_3k);

    let push_aux_slope = push_aux_3k - push_aux_1k;
    let repeat_aux_slope = repeat_aux_3k - repeat_aux_1k;
    assert_eq!(
        repeat_aux_slope, push_aux_slope,
        "[0u8; n] copy+push per-call aux growth must match push-built [u8] (repeat_aux_slope={repeat_aux_slope}, push_aux_slope={push_aux_slope})"
    );
    assert_eq!(
        repeat_aux_slope,
        2000 * 128,
        "2000 cat_u8(64B, 32B) calls must use 128 packed bytes/call (got {repeat_aux_slope})"
    );
    assert!(
        repeat_aux_3k <= push_aux_3k,
        "[0u8; n] total aux bytes must not exceed push-built [u8] (repeat_aux_3k={repeat_aux_3k}, push_aux_3k={push_aux_3k})"
    );
    assert_eq!(
        repeat_live_3k - repeat_live_1k,
        push_live_3k - push_live_1k,
        "[0u8; n] copy+push per-call live bytes must match push-built [u8]"
    );
}

#[test]
fn jit_u8_repeat_variants_and_interpreter_parity() {
    let shared_src = r#"
fn cat_u8(a: [u8], b: [u8]) -> [u8]:
    var r: [u8] = a
    var i: i64 = 0
    val n = b.len() as i64
    while i < n:
        r.push(b[i])
        i = i + 1
    r

fn dyn_zero_pad(n: i64) -> [u8]:
    var out: [u8] = [0u8; n]
    var i: i64 = 0
    while i < n:
        out[i] = ((i ^ 0x36) & 0xff).to_u8()
        i = i + 1
    out

fn dyn_nonzero_pad(n: i64, fill: u8) -> [u8]:
    var out = [fill; n]
    out[0] = 0x11u8
    if n > 1:
        out[n - 1] = 0x22u8
    out

fn dyn_untyped_zero_pad(n: i64) -> [u8]:
    var out: [u8] = [0; n]
    out[0] = 0x5au8
    out

fn main() -> i64:
    val msg: [u8] = [1u8, 2u8, 3u8, 4u8]

    val p0 = dyn_zero_pad(64)
    val c0 = cat_u8(p0, msg)
    if c0.len() != 68:
        return 1
    if c0[0] != 0x36u8 or c0[63] != (63 ^ 0x36).to_u8() or c0[64] != 1u8 or c0[67] != 4u8:
        return 2

    val p1 = dyn_nonzero_pad(10, 0x5cu8)
    val c1 = cat_u8(p1, msg)
    if c1.len() != 14:
        return 3
    if c1[0] != 0x11u8 or c1[5] != 0x5cu8 or c1[9] != 0x22u8 or c1[10] != 1u8 or c1[13] != 4u8:
        return 4

    val p2 = dyn_untyped_zero_pad(8)
    val c2 = cat_u8(p2, msg)
    if c2.len() != 12 or c2[0] != 0x5au8 or c2[1] != 0u8 or c2[8] != 1u8:
        return 5

    val empty0: [u8] = [0u8; 0]
    val c_empty = cat_u8(empty0, msg)
    if empty0.len() != 0 or c_empty.len() != 4 or c_empty[3] != 4u8:
        return 6

    val large: [u8] = [0u8; 300]
    val c_large = cat_u8(large, msg)
    if c_large.len() != 304 or c_large[0] != 0u8 or c_large[299] != 0u8 or c_large[300] != 1u8 or c_large[303] != 4u8:
        return 7

    0
"#;

    let ast = Parser::new(shared_src).parse().expect("shared fixture must parse");
    let interp_result = evaluate_module(&ast.items).expect("interpreter must evaluate");
    assert_eq!(interp_result, 0, "interpreter failure code");

    let (jit_result, _, _) = run_jit_with_heap_deltas(shared_src);
    assert_eq!(jit_result, 0, "JIT failure code");

    // Preserve existing interpreter negative-count rejection while JIT supports unsigned/signed width counts and clamps <= 0 safely to empty.
    let neg_interp_src = r#"
fn main() -> i64:
    val empty_neg: [u8] = [0u8; -5]
    empty_neg.len() as i64
"#;
    let neg_ast = Parser::new(neg_interp_src).parse().expect("neg fixture must parse");
    let neg_interp_err = evaluate_module(&neg_ast.items)
        .expect_err("interpreter must preserve negative repeat count error");
    assert!(
        neg_interp_err.to_string().contains("cannot be negative"),
        "unexpected interpreter negative error: {neg_interp_err}"
    );

    let jit_edge_src = r#"
fn main() -> i64:
    val msg: [u8] = [1u8, 2u8, 3u8, 4u8]
    val empty_neg: [u8] = [0u8; -5]
    val empty_nz_neg: [u8] = [0x77u8; -2]
    val i32_neg: i32 = -3i32
    val from_neg_i32: [u8] = [0x44u8; i32_neg]
    if empty_neg.len() != 0 or empty_nz_neg.len() != 0 or from_neg_i32.len() != 0:
        return 1
    var r: [u8] = empty_neg
    r.push(msg[0])
    if r.len() != 1 or r[0] != 1u8:
        return 2
    val u32_count: u32 = 12u32
    val from_u32: [u8] = [0x44u8; u32_count]
    if from_u32.len() != 12 or from_u32[0] != 0x44u8 or from_u32[11] != 0x44u8:
        return 3
    0
"#;
    let (jit_edge_res, _, _) = run_jit_with_heap_deltas(jit_edge_src);
    assert_eq!(jit_edge_res, 0, "JIT width-cast & negative repeat clamping failure code");
}

#[test]
fn jit_non_escaping_const64_u8_repeat_loop_stays_flat() {
    let src = r#"
fn main() -> i64:
    var i: i64 = 0
    var acc: i64 = 0
    while i < 2000:
        var buf = [0u8; 64]
        buf[0] = ((i & 0xff).to_u8())
        acc = acc + (buf[0] as i64)
        i = i + 1
    acc
"#;
    let (res, d_live, d_aux) = run_jit_with_heap_deltas(src);
    assert!(res > 0);
    assert!(
        d_live <= 1024 && d_aux <= 1024,
        "non-escaping [0u8; 64] loop leaked: d_live={d_live}, d_aux={d_aux}"
    );
}

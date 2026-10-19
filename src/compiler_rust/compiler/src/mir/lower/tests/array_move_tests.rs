//! MIR-shape pins for `array_move.rs` (bug
//! seed_jit_array_copy_never_freed_2026-10-19).
//!
//! A struct-field array round-trip `var o = st.output; ...; st = St(output: o)`
//! must lower with NO `rt_array_copy` (the JIT lane never frees a copy, so each
//! one is retained forever). Every case the move analysis cannot prove dead
//! and uniquely owned must KEEP its copy -- one test per disqualifier.

use super::common::*;
use crate::mir::{CallTarget, MirInst};

fn copies_in(source: &str, function: &str) -> usize {
    let mir = compile_to_mir(source).expect("source must lower to MIR");
    let f = mir
        .functions
        .iter()
        .find(|f| f.name == function)
        .unwrap_or_else(|| panic!("function {function} not found"));
    f.blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .filter(|i| matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_array_copy")))
        .count()
}

const ST: &str = "struct St:\n    output: [u8]\n    tag: i64\n\n";

fn with_st(body: &str) -> String {
    format!("{ST}{body}")
}

#[test]
fn round_trip_through_struct_field_moves_both_sites() {
    let src = with_st(
        "fn f(n: i64) -> [u8]:
    var st = St(output: [1 as u8, 2 as u8, 3 as u8, 4 as u8], tag: 0)
    var i = 0
    while i < n:
        var o = st.output
        var k = 0
        while k < 8:
            o.push(o[o.len() - 4])
            k = k + 1
        st = St(output: o, tag: 1)
        i = i + 8
    st.output
",
    );
    assert_eq!(copies_in(&src, "f"), 0);
}

/// The alias probe: `val saved = st` keeps the Let copy, and the later
/// `o.push(4)` keeps the struct-literal copy (which is the aliasing fix).
#[test]
fn alias_probe_keeps_let_copy_and_struct_literal_copy() {
    let src = with_st(
        "fn f() -> i64:
    var st = St(output: [1 as u8, 2 as u8], tag: 0)
    val saved = st
    var o = st.output
    o.push(3 as u8)
    st = St(output: o, tag: 1)
    o.push(4 as u8)
    st.output.len() * 100 + o.len() * 10 + saved.output.len()
",
    );
    assert_eq!(copies_in(&src, "f"), 2);
}

/// A struct literal built from a still-live array local copies it.
#[test]
fn struct_literal_from_live_local_copies() {
    let src = with_st(
        "fn f() -> i64:
    var o: [u8] = [1 as u8]
    val st = St(output: o, tag: 0)
    o.push(2 as u8)
    st.output.len() + o.len()
",
    );
    assert_eq!(copies_in(&src, "f"), 1);
}

/// Only `var` locals are copied into struct literals. A parameter keeps the
/// base aliasing (copying projections/params at every functional update
/// re-created the leak: 128 KiB zstd decode 280 MB -> 2.0 GB).
#[test]
fn struct_literal_from_param_keeps_base_aliasing() {
    let src = with_st("fn f(buf: [u8]) -> St:\n    St(output: buf, tag: 0)\n");
    assert_eq!(copies_in(&src, "f"), 0);
}

/// The `zstd_bits.spl` functional-update shape must not copy per call.
#[test]
fn functional_update_from_projection_emits_no_copy() {
    let src = with_st("fn adv(st: St) -> St:\n    St(output: st.output, tag: st.tag + 1)\n");
    assert_eq!(copies_in(&src, "adv"), 0);
}

/// A struct whose array field shares another holder's buffer (uncopied
/// struct-literal argument) is not uniquely owned: its field read keeps the copy.
#[test]
fn struct_built_from_projection_keeps_let_copy() {
    keeps_let_copy(
        "fn f() -> i64:
    var other = St(output: [1 as u8], tag: 0)
    var st = St(output: other.output, tag: 0)
    var o = st.output
    o.push(2 as u8)
    st = St(output: [9 as u8], tag: 1)
    o.len() + other.output.len()
",
    );
}

#[test]
fn struct_built_from_val_local_keeps_let_copy() {
    keeps_let_copy(
        "fn f() -> i64:
    val v: [u8] = [1 as u8]
    var st = St(output: v, tag: 0)
    var o = st.output
    o.push(2 as u8)
    st = St(output: [9 as u8], tag: 1)
    o.len() + v.len()
",
    );
}

#[test]
fn struct_built_from_index_place_keeps_let_copy() {
    keeps_let_copy(
        "fn f(rows: [[u8]]) -> i64:
    var st = St(output: rows[0], tag: 0)
    var o = st.output
    o.push(2 as u8)
    st = St(output: [9 as u8], tag: 1)
    o.len() + rows[0].len()
",
    );
}

fn keeps_let_copy(body: &str) {
    let src = with_st(body);
    assert!(copies_in(&src, "f") >= 1, "the `var o = ...` copy must be kept:\n{src}");
}

#[test]
fn saved_alias_before_let_keeps_copy() {
    keeps_let_copy(
        "fn f() -> i64:
    var st = St(output: [1 as u8], tag: 0)
    val saved = st
    var o = st.output
    o.push(2 as u8)
    st = St(output: [9 as u8], tag: 1)
    saved.output.len() + o.len()
",
    );
}

#[test]
fn call_built_source_keeps_copy() {
    keeps_let_copy(
        "fn mk() -> St:
    St(output: [1 as u8], tag: 0)

fn f() -> i64:
    var st = mk()
    var o = st.output
    o.push(2 as u8)
    st = St(output: [9 as u8], tag: 1)
    o.len()
",
    );
}

#[test]
fn break_between_let_and_overwrite_keeps_copy() {
    keeps_let_copy(
        "fn f() -> i64:
    var st = St(output: [1 as u8], tag: 0)
    var i = 0
    while i < 4:
        var o = st.output
        o.push(2 as u8)
        if i == 2:
            break
        st = St(output: [9 as u8], tag: 1)
        i = i + 1
    st.output.len()
",
    );
}

#[test]
fn continue_between_let_and_overwrite_keeps_copy() {
    keeps_let_copy(
        "fn f() -> i64:
    var st = St(output: [1 as u8], tag: 0)
    var i = 0
    while i < 4:
        i = i + 1
        var o = st.output
        o.push(2 as u8)
        if i == 2:
            continue
        st = St(output: [9 as u8], tag: 1)
    st.output.len()
",
    );
}

#[test]
fn param_source_keeps_copy() {
    keeps_let_copy(
        "fn f(st: St) -> i64:
    var o = st.output
    o.push(2 as u8)
    o.len()
",
    );
}

#[test]
fn param_array_source_keeps_copy() {
    keeps_let_copy(
        "fn f(buf: [u8]) -> [u8]:
    var out = buf
    out.push(2 as u8)
    out
",
    );
}

#[test]
fn lambda_capture_keeps_copy() {
    keeps_let_copy(
        "fn f() -> i64:
    var st = St(output: [1 as u8], tag: 0)
    val g = \\x: x + st.output.len()
    var o = st.output
    o.push(2 as u8)
    st = St(output: [9 as u8], tag: 1)
    g(1) + o.len()
",
    );
}

#[test]
fn defer_keeps_copy() {
    keeps_let_copy(
        "fn f() -> i64:
    var st = St(output: [1 as u8], tag: 0)
    defer print(\"done\")
    var o = st.output
    o.push(2 as u8)
    st = St(output: [9 as u8], tag: 1)
    o.len()
",
    );
}

#[test]
fn field_set_with_array_rhs_keeps_copy() {
    keeps_let_copy(
        "fn f() -> i64:
    var other: [u8] = [5 as u8]
    var st = St(output: [1 as u8], tag: 0)
    st.output = other
    var o = st.output
    o.push(2 as u8)
    st = St(output: [9 as u8], tag: 1)
    o.len() + other.len()
",
    );
}

#[test]
fn use_in_nested_if_after_let_keeps_copy() {
    keeps_let_copy(
        "fn f(c: bool) -> i64:
    var st = St(output: [1 as u8], tag: 0)
    var o = st.output
    o.push(2 as u8)
    if c:
        print(st.output.len())
    st = St(output: [9 as u8], tag: 1)
    o.len()
",
    );
}

#[test]
fn use_in_nested_loop_after_let_keeps_copy() {
    keeps_let_copy(
        "fn f() -> i64:
    var st = St(output: [1 as u8], tag: 0)
    var o = st.output
    var k = 0
    while k < 2:
        o.push(st.output[0])
        k = k + 1
    st = St(output: [9 as u8], tag: 1)
    o.len()
",
    );
}

#[test]
fn overwrite_rhs_reading_source_keeps_copy() {
    keeps_let_copy(
        "fn f() -> i64:
    var st = St(output: [1 as u8], tag: 0)
    var o = st.output
    o.push(2 as u8)
    st = St(output: o, tag: st.tag + 1)
    st.output.len()
",
    );
}

#[test]
fn source_never_overwritten_keeps_copy() {
    keeps_let_copy(
        "fn f() -> i64:
    var st = St(output: [1 as u8], tag: 0)
    var i = 0
    while i < 2:
        var o = st.output
        o.push(2 as u8)
        i = i + 1
    st.output.len()
",
    );
}

/// Builder shape (`Series.fill_na`): a `var` array handed to a struct literal
/// in an early `return` and in the tail moves at both sites.
#[test]
fn struct_literal_in_return_and_tail_moves() {
    let src = with_st(
        "fn f(c: bool) -> St:
    var o: [u8] = []
    o.push(1 as u8)
    if c:
        return St(output: o, tag: 1)
    St(output: o, tag: 2)
",
    );
    assert_eq!(copies_in(&src, "f"), 0);
}

/// One struct-literal use that is not dead keeps the copy for that local.
#[test]
fn struct_literal_with_one_live_use_keeps_copy() {
    let src = with_st(
        "fn f(c: bool) -> St:
    var o: [u8] = []
    if c:
        val a = St(output: o, tag: 1)
        o.push(2 as u8)
        return a
    St(output: o, tag: 2)
",
    );
    assert!(copies_in(&src, "f") >= 1);
}

/// Hole A1: a type with an `@inject` constructor lowers `S(data: o)` to a
/// constructor CALL (no struct-literal copy), so `s.data` shares the live `o`.
/// The analysis must not treat `s` as uniquely owned: base shape is kept.
#[test]
fn inject_constructor_struct_keeps_let_copy() {
    let src = "struct S:
    data: [u8]

impl S:
    static fn new(data: [u8], @inject tag: i64) -> S:
        S(data: data)

fn make_tag() -> i64:
    7

fn f() -> i64:
    var o: [u8] = [1 as u8]
    var s = S(data: o)
    o.push(2 as u8)
    var p = s.data
    p.push(3 as u8)
    s = S(data: [9 as u8])
    p.len() * 10 + o.len()
";
    let di_toml = r#"
[di]
mode = "hybrid"

[di.profiles.default]
bindings = [
  { on = "pc{ type(i64) }", impl = "make_tag", scope = "Transient", priority = 10 }
]
"#;
    let mir = compile_to_mir_with_di(src, di_toml).expect("DI lowering");
    let f = mir.functions.iter().find(|f| f.name == "f").expect("f");
    let calls_ctor = f
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .any(|i| matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("S.new")));
    assert!(
        calls_ctor,
        "precondition: `S(data: o)` must lower to the @inject constructor call"
    );
    let copies = f
        .blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .filter(|i| matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_array_copy")))
        .count();
    assert!(copies >= 1, "the `var p = s.data` copy must be kept:\n{src}");
}

/// Hole A2: an `Any`-typed slot holding an array is not copied at the struct
/// literal, so the struct shares the argument's buffer and is not unique.
#[test]
fn any_typed_slot_keeps_let_copy() {
    let src = "struct Holder:
    value: Any

fn f() -> i64:
    var p: Any = [1 as u8]
    var s = Holder(value: p)
    var o: [u8] = s.value
    o.push(3 as u8)
    s = Holder(value: 0)
    o.len()
";
    assert!(
        copies_in(src, "f") >= 1,
        "the `var o = s.value` copy must be kept:\n{src}"
    );
}

/// Hole A2: a generic `T` slot holding an array keeps a copy somewhere.
#[test]
fn generic_slot_keeps_copy() {
    let src = "struct Box<T>:
    value: T

fn f() -> i64:
    var p: [u8] = [1 as u8]
    var s = Box(value: p)
    p.push(2 as u8)
    var o: [u8] = s.value
    o.push(3 as u8)
    s = Box(value: [9 as u8])
    o.len() * 10 + p.len()
";
    assert!(copies_in(src, "f") >= 1, "a copy must be kept:\n{src}");
}

/// Every non-primitive slot needs a private buffer, so a nested value-struct
/// argument disqualifies the outer struct (accepted loss; pins the rule).
#[test]
fn nested_value_struct_arg_keeps_let_copy() {
    let src = "struct Inner:
    v: i64

struct Outer:
    data: [u8]
    inner: Inner

fn f() -> i64:
    var st = Outer(data: [1 as u8], inner: Inner(v: 1))
    var o = st.data
    o.push(2 as u8)
    st = Outer(data: [9 as u8], inner: Inner(v: 2))
    o.len()
";
    assert!(
        copies_in(src, "f") >= 1,
        "the `var o = st.data` copy must be kept:\n{src}"
    );
}

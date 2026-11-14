//! MIR-shape pins for the S1 block-end array release (`array_move.rs`,
//! doc/05_design/compiler/jit_memory/seed_jit_array_reclamation.md).
//!
//! On the JIT lane (`lower_to_mir_jit`) a scalar-element array local whose
//! every mention is allowlisted gets ONE `rt_array_free` when its declaring
//! statement list falls through. Every other shape must emit none -- one test
//! row per disqualifier. The runtime effect (live-array counters, alias
//! values) is pinned by
//! test/01_unit/compiler_core/interpreter/jit_block_array_release_spec.spl.

use crate::hir;
use crate::mir::lower::{lower_to_mir, lower_to_mir_jit};
use crate::mir::{CallTarget, MirInst, MirModule};
use simple_parser::Parser;

const PRELUDE: &str = "struct Holder:
    xs: [i64]
    n: i64

var g_arr: [i64] = [1, 2, 3]
var g_slot: [i64] = [0]

fn ident(x: [i64]) -> [i64]:
    x

fn take_len(x: [i64]) -> i64:
    x.len()

";

fn lower(body: &str, jit: bool) -> MirModule {
    let source = format!("{PRELUDE}{body}");
    let mut parser = Parser::new(&source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    if jit {
        lower_to_mir_jit(&hir_module)
    } else {
        lower_to_mir(&hir_module)
    }
    .expect("source must lower to MIR")
}

fn frees_in(mir: &MirModule, function: &str) -> usize {
    let f = mir
        .functions
        .iter()
        .find(|f| f.name == function)
        .unwrap_or_else(|| panic!("function {function} not found"));
    f.blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .filter(|i| matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_array_free")))
        .count()
}

/// `body` is the loop body of `fn f`, already indented by 8 spaces.
fn loop_fn(setup: &str, body: &str) -> String {
    format!("fn f(n: i64, p: [i64]) -> i64:\n    var i = 0\n    var acc = 0\n{setup}    while i < n:\n{body}        i = i + 1\n    acc\n")
}

fn jit_frees(setup: &str, body: &str) -> usize {
    frees_in(&lower(&loop_fn(setup, body), true), "f")
}

#[track_caller]
fn releases(setup: &str, body: &str) {
    assert_eq!(jit_frees(setup, body), 1, "expected one block-end release");
}

#[track_caller]
fn keeps(setup: &str, body: &str) {
    assert_eq!(jit_frees(setup, body), 0, "must not release");
}

// ---- positive: the seven acceptance loop bodies ---------------------------

#[test]
fn releases_fresh_literal() {
    releases("", "        val a = [i, i + 1, i + 2]\n        acc = acc + a[1]\n");
}

#[test]
fn releases_copied_local_read_only() {
    releases("    val src = [1, 2, 3]\n", "        val c = src\n        acc = acc + c[0]\n");
}

#[test]
fn releases_copied_local_with_scalar_index_store() {
    releases(
        "    val src = [1, 2, 3]\n",
        "        var c = src\n        c[0] = i\n        acc = acc + c[0] + src[0]\n",
    );
}

#[test]
fn releases_copied_row_of_local_rows() {
    releases(
        "    val rows = [[1, 2], [3, 4]]\n",
        "        val row = rows[1]\n        acc = acc + row[0]\n",
    );
}

#[test]
fn releases_copied_global() {
    releases("", "        val a = g_arr\n        acc = acc + a[2]\n");
}

#[test]
fn releases_copied_parameter() {
    releases("", "        val a = p\n        acc = acc + a[0]\n");
}

#[test]
fn releases_copied_field() {
    releases(
        "    val h = Holder(xs: [5, 6], n: 1)\n",
        "        val xs = h.xs\n        acc = acc + xs[1] + xs.len()\n",
    );
}

#[test]
fn releases_bool_elements() {
    releases("", "        val a = [true, false]\n        if a[0]:\n            acc = acc + 1\n");
}

/// Float and u64 elements are heap-boxed; a shallow free would leak the
/// boxes, so those arrays are not on the allowlist (unified plan, S1
/// condition 4).
#[test]
fn keeps_float_and_u64_element_arrays() {
    keeps("", "        val a = [1.5, 2.5]\n        if a[0] > 1.0:\n            acc = acc + 1\n");
    keeps("    val h: f32 = 1.5\n", "        val a = [h, h]\n        if a[0] > 1.0:\n            acc = acc + 1\n");
    keeps("    val u: u64 = 1\n", "        val a = [u, u]\n        if a[0] > 0:\n            acc = acc + 1\n");
    // Control: the same shape with i64 elements is released.
    releases("", "        val a = [1, 2]\n        if a[0] > 0:\n            acc = acc + 1\n");
}

#[test]
fn releases_in_nested_if_list_and_at_function_level() {
    releases("", "        if i >= 0:\n            val a = [i, 1]\n            acc = acc + a[0]\n");
    let mir = lower("fn f(n: i64) -> i64:\n    val a = [n, 2, 3]\n    a[0] + a[1]\n", true);
    assert_eq!(frees_in(&mir, "f"), 1);
}

/// The release is the LAST instruction of the falling-through block: the
/// scalar tail value is computed before it.
#[test]
fn function_level_release_follows_the_tail_value() {
    let mir = lower("fn f(n: i64) -> i64:\n    val a = [n, 2, 3]\n    a[0] + a[1]\n", true);
    let f = mir.functions.iter().find(|f| f.name == "f").unwrap();
    let insts: Vec<&MirInst> = f.blocks.iter().flat_map(|b| &b.instructions).collect();
    let free_at = insts
        .iter()
        .position(|i| matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_array_free")))
        .expect("release emitted");
    assert!(
        insts[free_at + 1..].iter().all(|i| !matches!(i, MirInst::Call { .. })),
        "no call may follow the release"
    );
}

// ---- lane gate -------------------------------------------------------------

/// Only the in-process JIT lane releases; native-build / AOT lowering keeps
/// today's behaviour.
#[test]
fn default_lowering_emits_no_release() {
    let src = loop_fn("", "        val a = [i, i + 1, i + 2]\n        acc = acc + a[1]\n");
    assert_eq!(frees_in(&lower(&src, false), "f"), 0);
}

// ---- negative: every escape form of the design's section 2.5 -----------------

#[test]
fn keeps_call_argument_and_call_result() {
    // A5
    keeps("", "        val a = [i, 1, 2]\n        var b = ident(a)\n        b[0] = 9\n        acc = acc + a[0] + b[0]\n");
    keeps("", "        val a = [i, 1, 2]\n        acc = acc + take_len(a)\n");
}

#[test]
fn keeps_struct_literal_argument() {
    // A6, and the `var` hand-over form
    keeps("", "        var a = [i, 1, 2]\n        val h = Holder(xs: a, n: i)\n        a[0] = 9\n        acc = acc + h.xs[0]\n");
    keeps("", "        var o = [i, 1]\n        val h = Holder(xs: o, n: i)\n        acc = acc + h.n\n");
}

#[test]
fn keeps_closure_capture() {
    // A7
    keeps("", "        var a = [i, 1, 2]\n        val f = \\x: x + a[0]\n        a[0] = 9\n        acc = acc + f(1)\n");
}

#[test]
fn keeps_global_write() {
    // A8
    keeps("", "        var a = [i, 1, 2]\n        g_slot = a\n        a[0] = 9\n        acc = acc + g_slot[0]\n");
}

#[test]
fn keeps_push_into_another_array() {
    // A9
    keeps(
        "    var rows: [[i64]] = []\n",
        "        var a = [i, 1, 2]\n        rows.push(a)\n        a[0] = 9\n        acc = acc + rows[i][0]\n",
    );
}

#[test]
fn keeps_plain_assign_alias_and_reassigned_var() {
    // A10
    keeps("    var b = [0]\n", "        val a = [i, 1, 2]\n        b = a\n        b[0] = 9\n        acc = acc + a[0]\n");
    keeps("", "        var a = [i]\n        a = [i, 2]\n        acc = acc + a[0]\n");
}

#[test]
fn keeps_tuple_array_dict_and_option_elements() {
    // A13, A14, A15, A20
    keeps("", "        var a = [i, 1, 2]\n        val t = (a, 1)\n        a[0] = 9\n        acc = acc + a[0]\n");
    keeps("", "        var a = [i, 1, 2]\n        val o = [a]\n        a[0] = 9\n        acc = acc + o[0][0]\n");
    keeps("", "        var a = [i, 1, 2]\n        val d = {\"k\": a}\n        a[0] = 9\n        acc = acc + a[0]\n");
    keeps("", "        var a = [i, 1, 2]\n        val o = Some(a)\n        a[0] = 9\n        acc = acc + a[0]\n");
}

#[test]
fn keeps_for_element_alias_and_for_iterable() {
    // A16
    keeps("", "        val rows = [[i, 1], [2, 3]]\n        for r in rows:\n            acc = acc + r[0]\n        acc = acc + rows[0][0]\n");
    keeps("", "        val a = [i, 1, 2]\n        for x in a:\n            acc = acc + x\n");
}

#[test]
fn keeps_if_expression_alias() {
    // A17
    keeps(
        "    val a2 = [7, 8]\n",
        "        val a = [i, 1, 2]\n        var b = if i > 5: a else: a2\n        b[0] = 9\n        acc = acc + a[0]\n",
    );
}

#[test]
fn keeps_index_store_of_the_array_and_element_argument() {
    // A18, A19
    keeps(
        "    var rows = [[0], [1]]\n",
        "        var a = [i, 1, 2]\n        rows[0] = a\n        a[0] = 9\n        acc = acc + rows[0][0]\n",
    );
    keeps("", "        val rows = [[i, 1], [2, 3]]\n        acc = acc + take_len(rows[0]) + rows[0][0]\n");
}

#[test]
fn keeps_function_result() {
    let tail = lower("fn f(n: i64) -> [i64]:\n    val a = [n, 2, 3]\n    a\n", true);
    assert_eq!(frees_in(&tail, "f"), 0);
    let ret = lower("fn f(n: i64) -> [i64]:\n    val a = [n, 2, 3]\n    return a\n", true);
    assert_eq!(frees_in(&ret, "f"), 0);
}

#[test]
fn keeps_move_source_and_moved_let() {
    keeps("", "        var s = [i, 1]\n        var o = s\n        o.push(1)\n        acc = acc + o.len()\n");
    keeps("", "        val a = [i, 1, 2]\n        val b = a\n        acc = acc + b[0]\n");
}

#[test]
fn keeps_block_with_early_exit_after_the_declaration() {
    keeps("", "        val a = [i, 1]\n        if i == 5000:\n            break\n        acc = acc + a[0]\n");
    keeps("", "        val a = [i, 1]\n        if i == 5000:\n            i = i + 1\n            continue\n        acc = acc + a[0]\n");
    keeps("", "        val a = [i, 1]\n        if i == 5000:\n            return acc\n        acc = acc + a[0]\n");
}

#[test]
fn keeps_text_and_nested_arrays() {
    keeps("", "        val a = [\"x\", \"y\"]\n        acc = acc + a.len()\n");
    keeps("", "        val a = [[i], [2]]\n        acc = acc + a[0][0]\n");
}

#[test]
fn keeps_mutating_and_unlisted_methods() {
    keeps("", "        var a = [i, 1]\n        a.push(2)\n        acc = acc + a[0]\n");
    keeps("", "        var a = [i, 1]\n        acc = acc + a.pop()\n");
    keeps("", "        val a = [i, 1]\n        if a.contains(1):\n            acc = acc + 1\n");
}

#[test]
fn keeps_slice_source_and_parameter() {
    keeps("", "        val a = [i, 1, 2]\n        val s = a[0..2]\n        acc = acc + s[0]\n");
    // A parameter is the caller's array: never released.
    let mir = lower("fn f(p: [i64]) -> i64:\n    p[0] + p.len()\n", true);
    assert_eq!(frees_in(&mir, "f"), 0);
}

/// A mention earlier in the loop body than the `Let` would read the previous
/// iteration's freed handle; it sits outside `stmts[pos + 1..]`.
#[test]
fn keeps_local_declared_without_initializer_or_read_before_its_let() {
    keeps("", "        var a: [i64]\n        a = [i]\n        acc = acc + a[0]\n");
}

// ---- pins for the review fixes ------------------------------------------------

fn calls_in(mir: &MirModule, function: &str, callee: &str) -> usize {
    let f = mir.functions.iter().find(|f| f.name == function).expect("function");
    f.blocks
        .iter()
        .flat_map(|b| &b.instructions)
        .filter(|i| matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name(callee)))
        .count()
}

/// Loop invariants are not walked by lowering today. A local they mention is
/// disqualified, so a future invariant lowering cannot read a released slot.
#[test]
fn keeps_local_mentioned_in_a_loop_invariant() {
    let with_invariant = "fn f(n: i64) -> i64:\n    var acc = 0\n    if n > 0:\n        val a = [n, 1]\n        var i = 0\n        while i < n:\n            invariant: a[0] >= 0\n            acc = acc + i\n            i = i + 1\n    acc\n";
    assert_eq!(frees_in(&lower(with_invariant, true), "f"), 0);
    // Control: the same shape without the invariant mention is released.
    let without = "fn f(n: i64) -> i64:\n    var acc = 0\n    if n > 0:\n        val a = [n, 1]\n        var i = 0\n        while i < n:\n            acc = acc + i + a[0]\n            i = i + 1\n    acc\n";
    assert_eq!(frees_in(&lower(without, true), "f"), 1);
}

/// The `len` and index fast paths key on the expression type. A use site that
/// sees the local at another type (the `ANY` filler) is not on the allowlist.
#[test]
fn keeps_local_whose_use_site_type_differs_from_its_declared_type() {
    let source = format!("{PRELUDE}fn f(n: i64) -> i64:\n    val a = [n, 1, 2]\n    val k = a.len()\n    k\n");
    let parse = |source: &str| {
        let mut parser = Parser::new(source);
        hir::lower(&parser.parse().expect("parse failed")).expect("hir lower failed")
    };
    // Control: untouched HIR releases `a`.
    let mir = lower_to_mir_jit(&parse(&source)).expect("lower");
    assert_eq!(frees_in(&mir, "f"), 1);

    let mut module = parse(&source);
    let f = module.functions.iter_mut().find(|f| f.name == "f").expect("f");
    let mut retyped = false;
    for stmt in &mut f.body {
        if let hir::HirStmt::Let { value: Some(value), .. } = stmt {
            if let hir::HirExprKind::MethodCall { receiver, .. } = &mut value.kind {
                receiver.ty = hir::TypeId::ANY;
                retyped = true;
            }
        }
    }
    assert!(retyped, "fixture must contain `val k = a.len()`");
    let mir = lower_to_mir_jit(&module).expect("lower");
    assert_eq!(frees_in(&mir, "f"), 0);
}

/// `len_local_sources` is keyed by function-scoped local indices. Function
/// `a` records "local 1 is the length of local 0"; `b` reuses both indices
/// for plain integers and must not hoist an array data pointer from slot 0.
/// The bound proof needs an unsigned index, so both loops use `u64`. The pin
/// relies on params `p`/`q` and `n`/`m` getting local indices 0 and 1; if
/// local numbering changes, re-check that it still fails with the per-function
/// clear in `lower_function` removed.
#[test]
fn length_source_map_does_not_leak_into_the_next_function() {
    let source = "fn a(p: [i64]) -> i64:\n    val n: u64 = p.len().to_u64()\n    var i: u64 = 0\n    var acc = 0\n    while i < n:\n        acc = acc + p[i]\n        i = i + 1\n    acc\n\nfn b(q: u64, m: u64) -> u64:\n    var i: u64 = 0\n    var acc: u64 = 0\n    while i < m:\n        acc = acc + i\n        i = i + 1\n    acc + q\n";
    let mir = lower(source, true);
    // Control: the proof fires in `a`, so the map entry exists.
    assert!(calls_in(&mir, "a", "rt_array_data_ptr") >= 1);
    assert_eq!(calls_in(&mir, "b", "rt_array_data_ptr"), 0);
}

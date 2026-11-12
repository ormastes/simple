//! An `ANY`-typed operand is a tagged `RuntimeValue` word. Four lowering
//! sites used it as a raw machine word, giving a silent wrong value under the
//! JIT. See
//! `doc/08_tracking/bug/seed_jit_any_operand_lowering_gaps_block_lambda_any_default_2026-11-12.md`.

use super::common::*;
use crate::mir::{CallTarget, MirInst, VReg};

fn instructions_of(source: &str, function: &str) -> Vec<MirInst> {
    let mir = compile_to_mir(source).expect("mir lowering failed");
    mir.functions
        .iter()
        .find(|f| f.name == function)
        .unwrap_or_else(|| panic!("no function {function}"))
        .blocks
        .iter()
        .flat_map(|b| b.instructions.iter().cloned())
        .collect()
}

fn unboxed_int_regs(instructions: &[MirInst]) -> Vec<VReg> {
    instructions
        .iter()
        .filter_map(|inst| match inst {
            MirInst::UnboxInt { dest, .. } => Some(*dest),
            _ => None,
        })
        .collect()
}

fn calls_to<'a>(instructions: &'a [MirInst], name: &str) -> Vec<&'a Vec<VReg>> {
    instructions
        .iter()
        .filter_map(|inst| match inst {
            MirInst::Call { target, args, .. } if target.name() == name => Some(args),
            _ => None,
        })
        .collect()
}

/// `xs[i - 1]` with `i: any`: the index is a tagged word and must be decoded
/// once before it indexes an array. It used to reach the element read tagged
/// (or tagged twice), so `xs[i - 1] + xs[0]` on `[10, 20, 30]`, `i = 3`,
/// answered 13 instead of 40.
#[test]
fn any_index_into_an_array_is_decoded_to_a_raw_integer() {
    let insts = instructions_of("fn at(xs: [i64], i: any) -> i64:\n    return xs[i - 1]\n", "at");
    let unboxed = unboxed_int_regs(&insts);
    let index_args: Vec<VReg> = insts
        .iter()
        .filter_map(|inst| match inst {
            MirInst::Call { target, args, .. }
                if matches!(
                    target.name(),
                    "rt_typed_words_i64_at" | "rt_array_get" | "rt_array_get_text" | "rt_index_get"
                ) =>
            {
                args.get(1).copied()
            }
            _ => None,
        })
        .collect();
    assert_eq!(index_args.len(), 1, "one element read expected: {insts:?}");
    assert!(
        unboxed.contains(&index_args[0]),
        "the index operand must be the decoded integer: {insts:?}"
    );
    assert!(
        calls_to(&insts, "rt_index_get").is_empty(),
        "a decoded index takes a typed element read, not the boxed dispatcher: {insts:?}"
    );
}

/// `P(x: v)` with `v: any` and `x: i64`: the raw field slot must receive the
/// decoded integer. It stored the tagged word (`mk(4).x` read 32).
#[test]
fn any_value_stored_into_a_raw_struct_field_is_decoded() {
    let insts = instructions_of(
        "struct P:\n    x: i64\n\nfn mk(v: any) -> P:\n    return P(x: v)\n",
        "mk",
    );
    let unboxed = unboxed_int_regs(&insts);
    let stored: Vec<VReg> = insts
        .iter()
        .filter_map(|inst| match inst {
            MirInst::StructInit { field_values, .. } => field_values.first().copied(),
            _ => None,
        })
        .collect();
    assert_eq!(stored.len(), 1, "{insts:?}");
    assert!(unboxed.contains(&stored[0]), "field must hold the decoded integer: {insts:?}");
}

/// `v + 0.5` with `v: any`: the any side may be an int OR a float at run
/// time, so it cannot be statically decoded as a float (`UnboxFloat` of a
/// tagged int read 0.0, giving 0.5 for `v = 2`). Dispatch on the tag instead.
#[test]
fn any_plus_float_literal_dispatches_at_run_time() {
    for source in [
        "fn h(v: any) -> any:\n    return v + 0.5\n",
        "fn h(v: any) -> any:\n    return 0.5 + v\n",
    ] {
        let insts = instructions_of(source, "h");
        assert_eq!(calls_to(&insts, "rt_any_add").len(), 1, "{source}: {insts:?}");
        assert!(
            !insts.iter().any(|inst| matches!(inst, MirInst::UnboxFloat { .. })),
            "{source}: the any operand must not be statically decoded as a float: {insts:?}"
        );
    }
}

/// `-v` with `v: any`: a raw negate of the tagged word is right for a tagged
/// int only by coincidence and wrong for a float (`-anyf(2.5)` printed
/// `<value:0x...>`). Lower it as the dynamic `0 - v`.
#[test]
fn any_unary_minus_dispatches_at_run_time() {
    let insts = instructions_of("fn n(v: any) -> any:\n    return -v\n", "n");
    assert_eq!(calls_to(&insts, "rt_any_sub").len(), 1, "{insts:?}");
    assert!(
        !insts.iter().any(|inst| matches!(inst, MirInst::UnaryOp { .. })),
        "no raw unary op on a tagged word: {insts:?}"
    );
    let _ = CallTarget::from_name("rt_any_sub");
}

/// `for i in 0..v` with `v: any`: the bound is decoded once; the raw counter
/// was compared with the tagged word (`v = 4` ran 32 iterations).
#[test]
fn any_range_bound_is_decoded() {
    let insts = instructions_of(
        "fn r(v: any) -> i64:\n    var acc = 0\n    for i in 0..v:\n        acc = acc + i\n    return acc\n",
        "r",
    );
    assert_eq!(unboxed_int_regs(&insts).len(), 1, "the bound must be decoded exactly once: {insts:?}");
}

/// `p.x = v` with `v: any` and `x: i64` stores the decoded integer.
#[test]
fn any_value_assigned_to_a_raw_struct_field_is_decoded() {
    let insts = instructions_of(
        "struct P:\n    x: i64\n\nfn set(v: any) -> i64:\n    var p = P(x: 0)\n    p.x = v\n    return p.x\n",
        "set",
    );
    let unboxed = unboxed_int_regs(&insts);
    let stored: Vec<VReg> = insts
        .iter()
        .filter_map(|inst| match inst {
            MirInst::FieldSet { value, .. } => Some(*value),
            _ => None,
        })
        .collect();
    assert_eq!(stored.len(), 1, "{insts:?}");
    assert!(unboxed.contains(&stored[0]), "field must receive the decoded integer: {insts:?}");
}

/// `v as f64` with `v: any` must not convert the raw bits of a tagged word.
#[test]
fn any_cast_to_float_decodes_through_the_runtime() {
    let insts = instructions_of("fn c(v: any) -> f64:\n    return v as f64\n", "c");
    assert_eq!(calls_to(&insts, "rt_any_mul").len(), 1, "{insts:?}");
    let decoded: Vec<VReg> = insts
        .iter()
        .filter_map(|inst| match inst {
            MirInst::UnboxFloat { dest, .. } => Some(*dest),
            _ => None,
        })
        .collect();
    let cast_sources: Vec<VReg> = insts
        .iter()
        .filter_map(|inst| match inst {
            MirInst::Cast { source, .. } => Some(*source),
            _ => None,
        })
        .collect();
    assert!(
        cast_sources.iter().all(|source| decoded.contains(source)),
        "every cast must read the decoded float: {insts:?}"
    );
}

/// Inside a lambda body the parameter's type is the LAMBDA's, not whatever
/// later local of the enclosing function reuses its index. `val f = \\i: xs[i]`
/// recovered `f`'s own slot type for `i` and read the element with the tagged
/// index (`f(2)` on `[10, 20, 30]` answered 0).
#[test]
fn lambda_param_index_is_decoded_inside_the_lambda_body() {
    let mir = compile_to_mir("fn test() -> any:\n    val xs = [10, 20, 30]\n    val f = \\i: xs[i]\n    return f(2)\n")
        .expect("mir lowering failed");
    let insts: Vec<MirInst> = mir
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.instructions.iter().cloned())
        .collect();
    let unboxed = unboxed_int_regs(&insts);
    let index_args: Vec<VReg> = calls_to(&insts, "rt_typed_words_i64_at")
        .into_iter()
        .filter_map(|args| args.get(1).copied())
        .collect();
    assert_eq!(index_args.len(), 1, "{insts:?}");
    assert!(unboxed.contains(&index_args[0]), "index must be decoded: {insts:?}");
}

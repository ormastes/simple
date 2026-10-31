//! Regression tests for
//! doc/08_tracking/bug/erased_field_arg_into_scalar_param_tagged_seed_2026-10-31.md
//!
//! A generic type parameter `T` erases to `TypeId::ANY`, so an erased struct
//! field read / generic fn result is a TAGGED word. The val/return/if
//! boundaries decode it into a raw slot; the CALL-ARGUMENT boundary into a
//! declared scalar parameter did not (`double_it(a.value)` got `21 << 3`).
//! `coerce_args_for_param_slots` now mirrors `box_arg_for_any_param` in the
//! tagged->raw direction for direct, indirect, static, and virtual calls.

use super::common::*;
use crate::mir::function::MirFunction;
use crate::mir::MirInst;

fn function<'m>(mir: &'m crate::mir::function::MirModule, name: &str) -> &'m MirFunction {
    mir.functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("function {name} must lower"))
}

fn instructions(func: &MirFunction) -> Vec<&MirInst> {
    func.blocks.iter().flat_map(|b| &b.instructions).collect()
}

/// The call to `callee` must receive, as argument `arg_index`, a vreg produced
/// by `UnboxInt`. An empty callee matches indirect and virtual calls.
fn call_arg_is_unboxed_int(func: &MirFunction, callee: &str, arg_index: usize) -> bool {
    let insts = instructions(func);
    let unboxed: Vec<_> = insts
        .iter()
        .filter_map(|inst| match inst {
            MirInst::UnboxInt { dest, .. } => Some(*dest),
            _ => None,
        })
        .collect();
    insts.iter().any(|inst| match inst {
        MirInst::Call { target, args, .. } if target.name() == callee => {
            args.get(arg_index).is_some_and(|a| unboxed.contains(a))
        }
        MirInst::MethodCallStatic { func_name, args, .. } if func_name == callee => {
            args.get(arg_index).is_some_and(|a| unboxed.contains(a))
        }
        MirInst::IndirectCall { args, .. } | MirInst::MethodCallVirtual { args, .. }
            if callee.is_empty() =>
        {
            args.get(arg_index).is_some_and(|a| unboxed.contains(a))
        }
        _ => false,
    })
}

fn has_call(func: &MirFunction, name: &str) -> bool {
    instructions(func)
        .iter()
        .any(|inst| matches!(inst, MirInst::Call { target, .. } if target.name() == name))
}

const PRELUDE: &str =
    "struct Box<T>:\n    value: T\n\nfn id<T>(x: T) -> T:\n    x\n\nfn double_it(x: i64) -> i64:\n    x * 2\n\n";

#[test]
fn erased_field_read_into_i64_param_is_unboxed() {
    let source = format!("{PRELUDE}fn probe() -> i64:\n    val a: Box<i64> = Box(value: 21)\n    double_it(a.value)\n");
    let mir = compile_to_mir(&source).expect("lower");
    assert!(
        call_arg_is_unboxed_int(function(&mir, "probe"), "double_it", 0),
        "an erased `T` field read must be untagged before it reaches an i64 parameter"
    );
}

#[test]
fn untyped_local_holding_erased_field_is_unboxed_at_the_call() {
    let source = format!(
        "{PRELUDE}fn probe() -> i64:\n    val a: Box<i64> = Box(value: 21)\n    val y = a.value\n    double_it(y)\n"
    );
    let mir = compile_to_mir(&source).expect("lower");
    assert!(call_arg_is_unboxed_int(function(&mir, "probe"), "double_it", 0));
}

#[test]
fn generic_fn_result_into_i64_param_is_unboxed() {
    let source = format!("{PRELUDE}fn probe() -> i64:\n    double_it(id(7))\n");
    let mir = compile_to_mir(&source).expect("lower");
    assert!(call_arg_is_unboxed_int(function(&mir, "probe"), "double_it", 0));
}

#[test]
fn raw_literal_argument_is_not_unboxed() {
    let source = format!("{PRELUDE}fn probe() -> i64:\n    double_it(21)\n");
    let mir = compile_to_mir(&source).expect("lower");
    let probe = function(&mir, "probe");
    assert!(
        !instructions(probe)
            .iter()
            .any(|i| matches!(i, MirInst::UnboxInt { .. })),
        "a raw i64 literal must not be decoded as a tagged word"
    );
}

#[test]
fn erased_field_into_method_i64_param_is_unboxed() {
    let source = format!(
        "{PRELUDE}class Acc:\n    base: i64\n    fn add(x: i64) -> i64:\n        self.base + x\n\nfn probe() -> i64:\n    val a: Box<i64> = Box(value: 21)\n    val acc = Acc(base: 21)\n    acc.add(a.value)\n"
    );
    let mir = compile_to_mir(&source).expect("lower");
    assert!(
        call_arg_is_unboxed_int(function(&mir, "probe"), "Acc.add", 0),
        "method-call arguments must take the same tagged->raw boundary as direct calls"
    );
}

#[test]
fn erased_bool_field_into_bool_param_keeps_a_real_bool() {
    let source = format!(
        "{PRELUDE}fn flag(b: bool) -> i64:\n    if b: 1 else: 0\n\nfn probe() -> i64:\n    val bf: Box<bool> = Box(value: false)\n    flag(bf.value)\n"
    );
    let mir = compile_to_mir(&source).expect("lower");
    let probe = function(&mir, "probe");
    // Presence alone (`rt_is_some`) turned a tagged `false` into true; the
    // decoder must first ask whether the word IS a bool.
    assert!(
        has_call(probe, "rt_value_is_bool"),
        "dynamic bool argument must be type-tested"
    );
    assert!(has_call(probe, "rt_value_truthy"), "a real bool keeps its value");
    assert!(
        has_call(probe, "rt_is_some"),
        "a non-bool dynamic value keeps the presence rule"
    );
}

#[test]
fn erased_float_field_into_f64_param_is_unboxed() {
    let source = format!(
        "{PRELUDE}fn half(f: f64) -> f64:\n    f / 2.0\n\nfn probe() -> f64:\n    val ff: Box<f64> = Box(value: 1.5)\n    half(ff.value)\n"
    );
    let mir = compile_to_mir(&source).expect("lower");
    let probe = function(&mir, "probe");
    let insts = instructions(probe);
    let unboxed: Vec<_> = insts
        .iter()
        .filter_map(|inst| match inst {
            MirInst::UnboxFloat { dest, .. } => Some(*dest),
            _ => None,
        })
        .collect();
    assert!(insts
        .iter()
        .any(|inst| matches!(inst, MirInst::Call { target, args, .. }
        if target.name() == "half" && args.first().is_some_and(|a| unboxed.contains(a)))));
}

#[test]
fn erased_field_into_indirect_i64_param_is_unboxed() {
    let source = format!(
        "{PRELUDE}fn probe(callable: fn(i64) -> i64) -> i64:\n    val a: Box<i64> = Box(value: 21)\n    callable(a.value)\n"
    );
    let mir = compile_to_mir(&source).expect("lower");
    assert!(
        call_arg_is_unboxed_int(function(&mir, "probe"), "", 0),
        "known-signature indirect calls must untag erased arguments"
    );
}

#[test]
fn erased_field_into_virtual_i64_param_is_unboxed() {
    let source = format!(
        "{PRELUDE}trait Doubler:\n    fn apply(x: i64) -> i64\n\nstruct Impl:\n    base: i64\n\nimpl Doubler for Impl:\n    fn apply(self, x: i64) -> i64:\n        self.base + x\n\nfn probe(doubler: Doubler) -> i64:\n    val a: Box<i64> = Box(value: 21)\n    doubler.apply(a.value)\n"
    );
    let mir = compile_to_mir(&source).expect("lower");
    assert!(
        call_arg_is_unboxed_int(function(&mir, "probe"), "", 0),
        "virtual trait calls must untag erased arguments"
    );
}

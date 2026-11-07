//! Regression tests: an integer literal flowing into a DECLARED `f32`/`f64`
//! slot must lower to a float constant, not `ConstInt`.
//!
//! `fn takef(x: f64) -> f64: x * 2.0` / `print(takef(3))` printed the denormal
//! 3e-323 under `simple run` (the seed JIT lane): HIR types `3` as `i64`, MIR
//! emitted `ConstInt 3`, and codegen moved those raw bits into the f64 slot.
//! Same fix as the pure-Simple MIR (`lower_int_literal_for_float_slot`,
//! PR #7416), applied by `float_slot_from_int_literal` at every slot boundary.

use super::common::*;
use crate::mir::function::{MirFunction, MirModule};
use crate::mir::{MirInst, Terminator, VReg};

fn function<'m>(mir: &'m MirModule, name: &str) -> &'m MirFunction {
    mir.functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("function {name} must lower"))
}

fn instructions(func: &MirFunction) -> Vec<&MirInst> {
    func.blocks.iter().flat_map(|b| &b.instructions).collect()
}

/// vregs defined by `ConstFloat { value }`.
fn float_consts(func: &MirFunction, value: f64) -> Vec<VReg> {
    instructions(func)
        .iter()
        .filter_map(|inst| match inst {
            MirInst::ConstFloat { dest, value: v } if *v == value => Some(*dest),
            _ => None,
        })
        .collect()
}

/// A `ConstFloat { value }` exists AND is consumed by some instruction or
/// terminator (so the slot really receives the float, not a dead constant).
fn float_const_is_used(func: &MirFunction, value: f64) -> bool {
    let consts = float_consts(func, value);
    func.blocks.iter().any(|b| {
        b.instructions.iter().any(|i| i.uses().iter().any(|u| consts.contains(u)))
            || b.terminator.uses().iter().any(|u| consts.contains(u))
    })
}

fn call_arg_is_float_const(func: &MirFunction, callee: &str, value: f64) -> bool {
    let consts = float_consts(func, value);
    instructions(func).iter().any(|inst| match inst {
        MirInst::Call { target, args, .. } if target.name() == callee => {
            args.first().is_some_and(|a| consts.contains(a))
        }
        _ => false,
    })
}

fn returns_float_const(func: &MirFunction, value: f64) -> bool {
    let consts = float_consts(func, value);
    func.blocks
        .iter()
        .any(|b| matches!(b.terminator, Terminator::Return(Some(v)) if consts.contains(&v)))
}

const PRELUDE: &str = "fn takef(x: f64) -> f64:\n    x * 2.0\n\n";

#[test]
fn int_literal_call_arg_into_f64_param_is_float_const() {
    let source = format!("{PRELUDE}fn probe() -> f64:\n    takef(3)\n");
    let mir = compile_to_mir(&source).expect("lower");
    assert!(
        call_arg_is_float_const(function(&mir, "probe"), "takef", 3.0),
        "`takef(3)` must pass ConstFloat 3.0, not the raw i64 bits"
    );
}

#[test]
fn negated_int_literal_call_arg_is_float_const() {
    let source = format!("{PRELUDE}fn probe() -> f64:\n    takef(-3)\n");
    let mir = compile_to_mir(&source).expect("lower");
    assert!(call_arg_is_float_const(function(&mir, "probe"), "takef", -3.0));
}

#[test]
fn annotated_f64_binding_from_int_literal_is_float_const() {
    let source = "fn probe() -> f64:\n    val y: f64 = 3\n    y\n";
    let mir = compile_to_mir(source).expect("lower");
    assert!(float_const_is_used(function(&mir, "probe"), 3.0));
}

#[test]
fn assignment_of_int_literal_into_f64_local_is_float_const() {
    let source = "fn probe() -> f64:\n    var z: f64 = 1.0\n    z = 4\n    z\n";
    let mir = compile_to_mir(source).expect("lower");
    assert!(float_const_is_used(function(&mir, "probe"), 4.0));
}

#[test]
fn explicit_return_of_int_literal_from_f64_fn_is_float_const() {
    let source = "fn probe() -> f64:\n    return 3\n";
    let mir = compile_to_mir(source).expect("lower");
    assert!(returns_float_const(function(&mir, "probe"), 3.0));
}

#[test]
fn tail_int_literal_of_f64_fn_is_float_const() {
    let source = "fn probe() -> f64:\n    3\n";
    let mir = compile_to_mir(source).expect("lower");
    assert!(returns_float_const(function(&mir, "probe"), 3.0));
}

#[test]
fn int_literal_struct_field_into_f64_field_is_float_const() {
    let source = "struct P:\n    v: f64\n\nfn probe() -> P:\n    P(v: 3)\n";
    let mir = compile_to_mir(source).expect("lower");
    let func = function(&mir, "probe");
    let consts = float_consts(func, 3.0);
    assert!(
        instructions(func).iter().any(|inst| matches!(
            inst,
            MirInst::StructInit { field_values, .. } if field_values.first().is_some_and(|v| consts.contains(v))
        )),
        "`P(v: 3)` must store ConstFloat 3.0 in the f64 field"
    );
}

#[test]
fn int_literal_into_i64_slot_stays_int() {
    let source = "fn takei(x: i64) -> i64:\n    x\n\nfn probe() -> i64:\n    takei(3)\n";
    let mir = compile_to_mir(source).expect("lower");
    assert!(float_consts(function(&mir, "probe"), 3.0).is_empty());
}

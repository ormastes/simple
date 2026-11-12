//! Indirect-call typing for lambdas.
//!
//! `MirInst::IndirectCall` used to carry `return_type = ANY` / `param_types =
//! [ANY]` for every lambda whose callee expression has no static function type
//! (the common `val f = \x: ...` case). The JIT closure ABI cannot choose a
//! value encoding for an untyped call boundary, so it bailed out of the whole
//! module. See
//! `doc/08_tracking/bug/seed_jit_coverage_self_hosted_compiler_2026-08-21.md`.

use super::common::*;
use crate::hir::TypeId;
use crate::mir::MirInst;

fn indirect_call_types(source: &str) -> Vec<(Vec<TypeId>, TypeId)> {
    let mir = compile_to_mir(source).expect("mir lowering failed");
    let mut found = Vec::new();
    for function in &mir.functions {
        for block in &function.blocks {
            for inst in &block.instructions {
                if let MirInst::IndirectCall {
                    param_types,
                    return_type,
                    ..
                } = inst
                {
                    found.push((param_types.clone(), *return_type));
                }
            }
        }
    }
    found
}

/// Pre-fix these all reported `([ANY], ANY)`. The declared boundary type must
/// agree with what the outlined lambda body is actually compiled as: the
/// parameter with the type `lambda_params` gives the outlined function (an
/// UNTYPED lambda parameter defaults to I64), and the result with the HIR type
/// of the body expression.
#[test]
fn indirect_call_carries_the_lambda_result_type() {
    assert_eq!(
        indirect_call_types("fn test() -> i64:\n    val f = \\x: x * 10\n    return f(32)\n"),
        vec![(vec![TypeId::I64], TypeId::I64)]
    );
    // `x + 0.5` computes an f64 (codegen coerces a mixed int/float pair to
    // float) and must SAY f64 — the old `left_hir.ty` rule called it i64.
    assert_eq!(
        indirect_call_types("fn test() -> f64:\n    val f = \\x: x + 0.5\n    return f(32)\n"),
        vec![(vec![TypeId::I64], TypeId::F64)]
    );
    assert_eq!(
        indirect_call_types("fn test() -> str:\n    val f = \\x: \"a\"\n    return f(32)\n"),
        vec![(vec![TypeId::I64], TypeId::STRING)]
    );
}

/// A declared function-valued parameter owns the indirect-call ABI. Keep its
/// argument and result types when lowering a predicate call; otherwise the
/// backend builds a closure-only signature while the call supplies the
/// closure and predicate argument.
#[test]
fn typed_predicate_parameter_carries_its_declared_signature() {
    assert_eq!(
        indirect_call_types("fn apply(pred: fn(i64) -> bool) -> bool:\n    return pred(1)\n",),
        vec![(vec![TypeId::I64], TypeId::BOOL)]
    );
}

/// The outlined body is compiled with the lambda's parameter types, so a call
/// site that passes something ELSE must not be given a typed boundary — the
/// backend would reinterpret the argument's bits. The commonest case is an
/// untyped lambda parameter (HIR defaults it to I64) reached with an f64 or a
/// text: measured pre-poison, `\x: "v" + x` called with `"a"` printed the raw
/// string handle `v4483685820545` under the JIT instead of `va`.
#[test]
fn a_call_site_that_disagrees_with_the_lambda_is_poisoned_to_any() {
    assert_eq!(
        indirect_call_types("fn test() -> f64:\n    val f = \\x: x * 1.5\n    return f(32.0)\n"),
        vec![(vec![TypeId::ANY], TypeId::ANY)]
    );
    assert_eq!(
        indirect_call_types("fn test() -> str:\n    val f = \\x: \"v\" + x\n    return f(\"a\")\n"),
        vec![(vec![TypeId::ANY], TypeId::ANY)]
    );
}

/// A local reassigned to a second lambda with a DIFFERENT signature is
/// poisoned: propagating either branch's types would be a miscompile, so the
/// RESULT type stays ANY and the backend falls back. (The parameter slot keeps
/// the caller's own argument type, which is what the call site really passes.)
#[test]
fn conflicting_closures_in_one_local_propagate_nothing() {
    let types =
        indirect_call_types("fn test() -> i64:\n    var f = \\x: x * 10\n    f = \\x: x > 1\n    return f(32)\n");
    assert_eq!(types, vec![(vec![TypeId::I64], TypeId::ANY)]);
}

/// The outlined lambda function must DECLARE the type it returns. It used to
/// be hardcoded to I64, so an f64-bodied lambda's Cranelift signature
/// disagreed with the value its `Return` produced.
#[test]
fn outlined_lambda_declares_its_real_return_type() {
    let mir = compile_to_mir("fn test() -> f64:\n    val f = \\x: x * 1.5\n    return f(32.0)\n")
        .expect("mir lowering failed");
    let expanded = crate::codegen::shared::expand_with_outlined(&mir);
    let outlined = expanded
        .iter()
        .find(|f| f.name.contains("_outlined_"))
        .expect("no outlined lambda function");
    assert_eq!(outlined.return_type, TypeId::F64);
}

/// A lambda whose result is `any` returns an ALREADY tagged word, so its
/// outlined function must declare `ANY`, not I64: the boxed entry boxes an
/// I64 result, which tagged the word a second time and made
/// `[1, 2, 3].map(\\x: anyv(x))` answer `[8, 16, 24]`.
#[test]
fn outlined_any_result_lambda_declares_any_not_i64() {
    let mir = compile_to_mir(
        "fn anyv(x: i64) -> any:\n    x\n\nfn test() -> any:\n    val xs = [1, 2, 3]\n    return xs.map(\\x: anyv(x))\n",
    )
    .expect("mir lowering failed");
    let lambda_result = mir
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.instructions.iter())
        .find_map(|inst| match inst {
            MirInst::ClosureCreate { return_type, .. } => Some(*return_type),
            _ => None,
        })
        .expect("no ClosureCreate");
    assert_eq!(lambda_result, TypeId::ANY, "precondition: the lambda's result is `any`");
    let expanded = crate::codegen::shared::expand_with_outlined(&mir);
    let outlined = expanded
        .iter()
        .find(|f| f.name.contains("_outlined_"))
        .expect("no outlined lambda function");
    assert_eq!(outlined.return_type, TypeId::ANY);
}

/// A bool-result lambda is outlined as I64 (full-width body), so the outlined
/// metadata must still say the result is a BOOL: the boxed entry uses it to
/// answer a tagged bool. Without it `xs.map(\\x: x > 1)` printed `[0, 1, 1]`.
#[test]
fn outlined_bool_result_lambda_is_marked_for_bool_boxing() {
    let returns_bool = |source: &str| {
        let mir = compile_to_mir(source).expect("mir lowering failed");
        let expanded = crate::codegen::shared::expand_with_outlined(&mir);
        let outlined = expanded
            .iter()
            .find(|f| f.name.contains("_outlined_"))
            .expect("no outlined lambda function");
        assert_eq!(outlined.return_type, TypeId::I64, "body stays full-width");
        outlined
            .outlined_bodies
            .get(&outlined.entry_block)
            .expect("outlined lambda metadata")
            .lambda_returns_bool
    };
    assert!(returns_bool(
        "fn test() -> any:\n    val xs = [1, 2, 3]\n    return xs.map(\\x: x > 1)\n"
    ));
    assert!(!returns_bool(
        "fn test() -> any:\n    val xs = [1, 2, 3]\n    return xs.map(\\x: x + 1)\n"
    ));
}

/// An unannotated lambda passed to a METHOD's `fn(...)` parameter takes the
/// declared callback parameter type, as for a free function. It used to
/// default to I64, so `c.run_f(\\x: x * 2.0, 1.25)` decoded a boxed float as
/// an integer; a generic `fn(T) -> T` slot is the erased `ANY`.
#[test]
fn method_call_lambda_takes_declared_callback_param_types() {
    let lambda_param = |source: &str| {
        let mir = compile_to_mir(source).expect("mir lowering failed");
        mir.functions
            .iter()
            .flat_map(|f| f.blocks.iter())
            .flat_map(|b| b.instructions.iter())
            .find_map(|inst| match inst {
                MirInst::ClosureCreate { lambda_params, .. } => Some(lambda_params[0].ty),
                _ => None,
            })
            .expect("no ClosureCreate")
    };
    let class = "class Calc:\n    k: i64\n\n    fn run_f(f: fn(f64) -> f64, v: f64) -> f64:\n        f(v)\n\n    \
                 fn with<T>(f: fn(T) -> T, v: T) -> T:\n        f(v)\n\n";
    assert_eq!(
        lambda_param(&format!(
            "{class}fn test() -> f64:\n    val c = Calc(k: 1)\n    return c.run_f(\\x: x * 2.0, 1.25)\n"
        )),
        TypeId::F64
    );
    assert_eq!(
        lambda_param(&format!(
            "{class}fn test() -> any:\n    val c = Calc(k: 1)\n    return c.with(\\x: x, 1.25)\n"
        )),
        TypeId::ANY
    );
}

/// The LOCAL that holds a closure must be pointer-sized. HIR types a lambda as
/// its body type, so `val f = \\x: x > 1` declared `f` as `bool`: codegen gave
/// it an 8-bit slot and truncated the closure handle (`f(2)` crashed,
/// `xs.filter(f)` answered `[]`). The `Store`/`Load` were already retyped; the
/// slot itself was not.
#[test]
fn local_holding_a_bool_result_closure_is_pointer_sized() {
    let mir = compile_to_mir("fn test() -> bool:\n    val f = \\x: x > 1\n    return f(2)\n")
        .expect("mir lowering failed");
    let test = mir.functions.iter().find(|f| f.name == "test").expect("test fn");
    let closure_local = test
        .blocks
        .iter()
        .flat_map(|b| b.instructions.iter())
        .find_map(|inst| match inst {
            MirInst::LocalAddr { local_index, .. } => Some(*local_index),
            _ => None,
        })
        .expect("closure local");
    let slot = &test.locals[closure_local - test.params.len()];
    assert_eq!(slot.ty, TypeId::I64, "closure-holding local `{}` must be I64", slot.name);
}

/// Sub-register and untyped boundary types are not carryable by the unboxed
/// closure ABI. `BOOL` lowers to `i8` and crashed the process when a lambda
/// returned one; `ANY` has no correct encoding at all.
#[test]
fn abi_support_predicate_rejects_bool_and_any() {
    use crate::codegen::jit_closure_abi_supports;
    assert!(jit_closure_abi_supports(TypeId::I64));
    assert!(jit_closure_abi_supports(TypeId::F64));
    assert!(jit_closure_abi_supports(TypeId::STRING));
    assert!(!jit_closure_abi_supports(TypeId::BOOL));
    assert!(!jit_closure_abi_supports(TypeId::ANY));
    assert!(!jit_closure_abi_supports(TypeId::VOID));
}

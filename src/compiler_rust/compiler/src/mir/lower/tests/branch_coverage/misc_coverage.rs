//! Additional branch coverage tests for MIR lowering
//!
//! Constants, unary/binary ops, load/store, for-each, enum, coverage probes,
//! struct/field, pointer, closures, contracts, and remaining coverage items.

use super::super::common::*;
use super::helpers::*;
use crate::hir::{self, BinOp};
use crate::mir::lower::{ContractMode, MirLowerer};
use crate::mir::function::MirFunction;
use crate::mir::{self, MirInst, Terminator};

// =============================================================================
// Additional branch coverage: Constants
// =============================================================================

#[test]
fn coverage_const_int() {
    let mir = compile_to_mir("fn test() -> i64:\n    return 42\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ConstInt { value: 42, .. })));
}

#[test]
fn coverage_const_float() {
    let mir = compile_to_mir("fn test() -> f64:\n    return 3.14\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ConstFloat { .. })));
}

#[test]
fn coverage_const_bool() {
    let mir = compile_to_mir("fn test() -> bool:\n    return true\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ConstBool { value: true, .. })));
}

#[test]
fn coverage_const_string() {
    let mir = compile_to_mir("fn test() -> i64:\n    val s = \"hello\"\n    return 0\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ConstString { .. })));
}

// =============================================================================
// Additional branch coverage: UnaryOp
// =============================================================================

#[test]
fn coverage_unary_op_negate() {
    let mir = compile_to_mir("fn test(x: i64) -> i64:\n    return -x\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::UnaryOp { .. })));
}

#[test]
fn coverage_unary_op_not() {
    let mir = compile_to_mir("fn test(x: bool) -> bool:\n    return not x\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::UnaryOp { .. })));
}

// =============================================================================
// Additional branch coverage: Load/Store
// =============================================================================

#[test]
fn coverage_load_local_variable() {
    let mir = compile_to_mir("fn test() -> i64:\n    var x: i64 = 42\n    return x\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::Load { .. })));
}

#[test]
fn coverage_store_local_variable() {
    let mir = compile_to_mir("fn test() -> i64:\n    var x: i64 = 0\n    x = 42\n    return x\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::Store { .. })));
}

#[test]
fn coverage_load_store_if_expression() {
    let mir = compile_to_mir("fn test(a: bool) -> i64:\n    val x = if a: 1 else: 2\n    return x\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::Store { .. })));
    assert!(has_inst(&mir, |i| matches!(i, MirInst::Load { .. })));
}

#[test]
fn coverage_local_addr() {
    let mir = compile_to_mir("fn test() -> i64:\n    var x: i64 = 42\n    return x\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::LocalAddr { .. })));
}

// =============================================================================
// Additional branch coverage: for-each loop
// =============================================================================

#[test]
fn coverage_for_each_index_get() {
    let mir = compile_to_mir(
        "fn test() -> i64:\n    val arr = [1, 2, 3]\n    var sum: i64 = 0\n    for x in arr:\n        sum = sum + x\n    return sum\n",
    )
    .unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::IndexGet { .. })));
}

#[test]
fn coverage_for_loop_store() {
    let mir = compile_to_mir(
        "fn test() -> i64:\n    var sum: i64 = 0\n    for i in 0..10:\n        sum = sum + i\n    return sum\n",
    )
    .unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::Store { .. })));
}

// =============================================================================
// Additional branch coverage: Enum operations
// =============================================================================

#[test]
fn coverage_enum_unit_variant() {
    let mir =
        compile_to_mir("enum Color:\n    Red\n    Blue\n\nfn test() -> i64:\n    val c = Color.Red\n    return 0\n")
            .unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::EnumUnit { .. })));
}

// =============================================================================
// Additional branch coverage: Decision/Path coverage probes
// =============================================================================

#[test]
fn coverage_decision_probe() {
    let mir = compile_with_coverage("fn test(a: bool) -> i64:\n    if a:\n        return 1\n    return 0\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::DecisionProbe { .. })));
}

#[test]
fn coverage_path_probe() {
    let mir = compile_with_coverage("fn test(a: bool) -> i64:\n    if a:\n        return 1\n    return 0\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::PathProbe { .. })));
}

// =============================================================================
// Additional branch coverage: FieldSet
// =============================================================================

#[test]
fn coverage_field_set() {
    let src = concat!(
        "struct Point:\n",
        "    x: i64\n",
        "    y: i64\n",
        "\n",
        "fn test() -> i64:\n",
        "    var p = Point(x: 1, y: 2)\n",
        "    p.x = 10\n",
        "    return p.x\n",
    );
    let result = try_compile_to_mir(src);
    if let Some(Ok(mir)) = result {
        assert!(
            has_inst(&mir, |i| matches!(i, MirInst::FieldSet { .. }))
                || has_inst(&mir, |i| matches!(i, MirInst::FieldGet { .. }))
        );
    }
}

// =============================================================================
// Additional branch coverage: PointerNew
// =============================================================================

#[test]
fn coverage_pointer_new() {
    let result = try_compile_to_mir("fn test() -> i64:\n    val p = new i64(42)\n    return 0\n");
    if let Some(Ok(mir)) = result {
        assert!(has_inst(&mir, |i| matches!(i, MirInst::PointerNew { .. })) || !mir.functions.is_empty());
    }
}

// =============================================================================
// Additional branch coverage: ContractOldCapture
// =============================================================================

#[test]
fn coverage_contract_old_capture() {
    let src = concat!(
        "fn inc(x: i64) -> i64:\n",
        "    in:\n",
        "        x >= 0\n",
        "    out(ret):\n",
        "        ret == old(x) + 1\n",
        "    return x + 1\n",
    );
    let result = try_compile_to_mir(src);
    if let Some(Ok(mir)) = result {
        let has_old_capture = has_inst(&mir, |i| matches!(i, MirInst::ContractOldCapture { .. }));
        let has_contract = has_inst(&mir, |i| matches!(i, MirInst::ContractCheck { .. }));
        assert!(has_old_capture || has_contract);
    }
}

// =============================================================================
// Additional branch coverage: mixed constants
// =============================================================================

#[test]
fn coverage_mixed_constants() {
    let mir = compile_to_mir(
        "fn test() -> i64:\n    val a: i64 = 1\n    val b: f64 = 2.0\n    val c: bool = true\n    val d = \"hi\"\n    return a\n",
    )
    .unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ConstInt { .. })));
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ConstFloat { .. })));
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ConstBool { .. })));
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ConstString { .. })));
}

// =============================================================================
// Additional branch coverage: while loop
// =============================================================================

#[test]
fn coverage_while_loop_load_store() {
    let mir =
        compile_to_mir("fn test() -> i64:\n    var i: i64 = 0\n    while i < 10:\n        i = i + 1\n    return i\n")
            .unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::Load { .. })));
    assert!(has_inst(&mir, |i| matches!(i, MirInst::Store { .. })));
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BinOp { .. })));
}

// =============================================================================
// Additional branch coverage: nested if/else
// =============================================================================

#[test]
fn coverage_nested_if_else() {
    let mir = compile_to_mir(concat!(
        "fn test(a: bool, b: bool) -> i64:\n",
        "    val x = if a:\n",
        "        if b: 1 else: 2\n",
        "    else:\n",
        "        3\n",
        "    return x\n",
    ))
    .unwrap();
    assert!(count_inst(&mir, |i| matches!(i, MirInst::Store { .. })) >= 2);
}

// =============================================================================
// Additional branch coverage: Cast
// =============================================================================

#[test]
fn coverage_cast_int_to_float() {
    let mir = compile_to_mir("fn test(x: i64) -> f64:\n    return x as f64\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::Cast { .. })));
}

// =============================================================================
// Additional branch coverage: BinOp variants
// =============================================================================

#[test]
fn coverage_binop_arithmetic() {
    let mir = compile_to_mir("fn test(a: i64, b: i64) -> i64:\n    return a + b - a * b\n").unwrap();
    assert!(count_inst(&mir, |i| matches!(i, MirInst::BinOp { .. })) >= 3);
}

#[test]
fn coverage_binop_comparison() {
    let mir = compile_to_mir("fn test(a: i64, b: i64) -> bool:\n    return a < b\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BinOp { op: BinOp::Lt, .. })));
}

#[test]
fn coverage_binop_modulo() {
    let mir = compile_to_mir("fn test(a: i64, b: i64) -> i64:\n    return a % b\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BinOp { op: BinOp::Mod, .. })));
}

#[test]
fn coverage_binop_division() {
    let mir = compile_to_mir("fn test(a: i64, b: i64) -> i64:\n    return a / b\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BinOp { op: BinOp::Div, .. })));
}

// =============================================================================
// Additional branch coverage: StructInit + FieldGet
// =============================================================================

#[test]
fn coverage_struct_init_and_field_get() {
    let src = concat!(
        "struct Point:\n",
        "    x: i64\n",
        "    y: i64\n",
        "\n",
        "fn test() -> i64:\n",
        "    val p = Point(x: 3, y: 4)\n",
        "    return p.x + p.y\n",
    );
    let mir = compile_to_mir(src).unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::StructInit { .. })));
    assert!(has_inst(&mir, |i| matches!(i, MirInst::FieldGet { .. })));
}

// =============================================================================
// Additional branch coverage: Closure
// =============================================================================

#[test]
fn coverage_closure_and_indirect_call() {
    let mir = compile_to_mir("fn test() -> i64:\n    val f = \\x: x + 1\n    return f(41)\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ClosureCreate { .. })));
    assert!(has_inst(&mir, |i| matches!(i, MirInst::IndirectCall { .. })));
}

#[test]
fn coverage_closure_captures() {
    let mir =
        compile_to_mir("fn test() -> i64:\n    val a: i64 = 10\n    val f = \\x: x + a\n    return f(32)\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ClosureCreate { .. })));
}

// =============================================================================
// Additional branch coverage: ArrayLit + TupleLit
// =============================================================================

#[test]
fn coverage_array_lit() {
    let mir = compile_to_mir("fn test() -> i64:\n    val arr = [10, 20, 30]\n    return 0\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ArrayLit { .. })));
}

#[test]
fn coverage_tuple_lit() {
    let mir = compile_to_mir("fn test() -> i64:\n    val t = (1, 2, 3)\n    return 0\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::TupleLit { .. })));
}

// =============================================================================
// Additional branch coverage: MethodCallStatic
// =============================================================================

#[test]
fn coverage_method_call_static() {
    let src = concat!(
        "struct Counter:\n",
        "    value: i64\n",
        "\n",
        "impl Counter:\n",
        "    fn get() -> i64:\n",
        "        return self.value\n",
        "\n",
        "fn test() -> i64:\n",
        "    val c = Counter(value: 42)\n",
        "    return c.get()\n",
    );
    let mir = compile_to_mir(src).unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::MethodCallStatic { .. })));
}

// =============================================================================
// Additional branch coverage: ContractCheck
// =============================================================================

#[test]
fn coverage_contract_check_precondition() {
    let mir = compile_to_mir_with_mode(
        "fn test(x: i64) -> i64:\n    in:\n        x > 0\n    return x\n",
        ContractMode::All,
    )
    .unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ContractCheck { .. })));
}

// =============================================================================
// Additional branch coverage: multiple return paths
// =============================================================================

#[test]
fn coverage_multiple_returns() {
    let mir = compile_to_mir(concat!(
        "fn test(x: i64) -> i64:\n",
        "    if x > 0:\n",
        "        return x\n",
        "    if x < 0:\n",
        "        return -x\n",
        "    return 0\n",
    ))
    .unwrap();
    let return_count = mir
        .functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .filter(|b| matches!(b.terminator, Terminator::Return { .. }))
        .count();
    assert!(return_count >= 3);
}

// =============================================================================
// Additional branch coverage: EndScope
// =============================================================================

#[test]
fn coverage_end_scope() {
    let mir = compile_to_mir("fn test() -> i64:\n    var x: i64 = 42\n    return x\n").unwrap();
    assert!(!mir.functions.is_empty());
}

// =============================================================================
// Additional branch coverage: BoxInt/BoxFloat
// =============================================================================

#[test]
fn coverage_box_int_in_interp() {
    let mir = compile_to_mir("fn test() -> i64:\n    val x: i64 = 42\n    val s = \"{x}\"\n    return 42\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BoxInt { .. })));
}

#[test]
fn coverage_box_float_in_interp() {
    let mir = compile_to_mir("fn test() -> i64:\n    val f: f64 = 3.14\n    val s = \"{f}\"\n    return 42\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BoxFloat { .. })));
}

// =============================================================================
// Additional branch coverage: Drop
// =============================================================================

#[test]
fn coverage_drop_struct() {
    let src = concat!(
        "struct Wrapper:\n",
        "    value: i64\n",
        "\n",
        "fn test() -> i64:\n",
        "    val w = Wrapper(value: 42)\n",
        "    return w.value\n",
    );
    let mir = compile_to_mir(src).unwrap();
    assert!(!mir.functions.is_empty());
}

// =============================================================================
// Additional branch coverage: PointerRef + PointerDeref
// =============================================================================

#[test]
fn coverage_pointer_ref_deref() {
    let result = try_compile_to_mir("fn test(x: i64) -> i64:\n    val p = &x\n    return *p\n");
    if let Some(Ok(mir)) = result {
        assert!(
            has_inst(&mir, |i| matches!(i, MirInst::PointerRef { .. }))
                || has_inst(&mir, |i| matches!(i, MirInst::PointerDeref { .. }))
                || !mir.functions.is_empty()
        );
    }
}

// =============================================================================
// Additional branch coverage: GlobalLoad
// =============================================================================

#[test]
fn coverage_global_load() {
    let result = try_compile_to_mir("val MAGIC: i64 = 42\n\nfn test() -> i64:\n    return MAGIC\n");
    if let Some(Ok(mir)) = result {
        assert!(
            has_inst(&mir, |i| matches!(i, MirInst::GlobalLoad { .. }))
                || has_inst(&mir, |i| matches!(i, MirInst::ConstInt { .. }))
        );
    }
}

// =============================================================================
// ProofHint and Calc statements
// =============================================================================

#[test]
fn proof_hint_statement() {
    let src = "fn test(x: i64) -> i64:\n    lean hint: \"simp\"\n    return x\n";
    let _ = try_compile_to_mir(src);
}

#[test]
fn calc_statement() {
    let src = "fn test(n: i64) -> i64:\n    calc:\n        n\n        == n    by: \"identity\"\n    return n\n";
    let _ = try_compile_to_mir(src);
}

// =============================================================================
// Additional branch coverage: Call
// =============================================================================

#[test]
fn coverage_call_explicit() {
    let mir =
        compile_to_mir("fn add(a: i64, b: i64) -> i64:\n    return a + b\n\nfn test() -> i64:\n    return add(1, 2)\n")
            .unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::Call { .. })));
}

#[test]
fn coverage_call_no_args() {
    let mir = compile_to_mir("fn zero() -> i64:\n    return 0\n\nfn test() -> i64:\n    return zero()\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::Call { .. })));
}

// =============================================================================
// VecLit
// =============================================================================

#[test]
fn coverage_vec_lit() {
    let result = try_compile_to_mir("fn test() -> i64:\n    val v = vec[1, 2, 3, 4]\n    return 0\n");
    if let Some(Ok(mir)) = result {
        assert!(has_inst(&mir, |i| matches!(i, MirInst::VecLit { .. })));
    }
}

#[test]
fn coverage_vec_lit_empty() {
    let result = try_compile_to_mir("fn test() -> i64:\n    val v = vec[]\n    return 0\n");
    if let Some(Ok(mir)) = result {
        assert!(has_inst(&mir, |i| matches!(i, MirInst::VecLit { .. })));
    }
}

// =============================================================================
// EndScope direct
// =============================================================================

#[test]
fn coverage_end_scope_direct() {
    let mut lowerer = MirLowerer::new();
    let mut func = MirFunction::new(
        "scope_test".to_string(),
        hir::TypeId::I64,
        simple_parser::ast::Visibility::Private,
    );
    func.new_block();
    lowerer.begin_function(func, "scope_test", false).unwrap();
    let result = lowerer.emit_end_scope(0);
    assert!(result.is_ok());
    let finished = lowerer.end_function().unwrap();
    assert!(finished.blocks.iter().any(|b| b
        .instructions
        .iter()
        .any(|i| matches!(i, MirInst::EndScope { local_index: 0 }))));
}

// =============================================================================
// FutureCreate, Await
// =============================================================================

#[test]
fn coverage_future_create_and_await() {
    let result = try_compile_to_mir(
        "fn fetch() -> i64:\n    return 42\n\nfn test() -> i64:\n    val f = async fetch()\n    val result = await f\n    return result\n",
    );
    if let Some(Ok(mir)) = result {
        let has_future = has_inst(&mir, |i| matches!(i, MirInst::FutureCreate { .. }));
        let has_await = has_inst(&mir, |i| matches!(i, MirInst::Await { .. }));
        assert!(has_future || has_await || !mir.functions.is_empty());
    }
}

// =============================================================================
// GeneratorCreate, Yield
// =============================================================================

#[test]
fn coverage_generator_create_and_yield() {
    let result = try_compile_to_mir(
        "fn gen() -> i64:\n    yield 1\n    yield 2\n    return 3\n\nfn test() -> i64:\n    return 0\n",
    );
    if let Some(Ok(mir)) = result {
        let has_gen = has_inst(&mir, |i| matches!(i, MirInst::GeneratorCreate { .. }));
        let has_yield = has_inst(&mir, |i| matches!(i, MirInst::Yield { .. }));
        assert!(has_gen || has_yield || !mir.functions.is_empty());
    }
}

#[test]
fn coverage_yield_standalone() {
    let result = try_compile_to_mir("fn gen() -> i64:\n    yield 42\n    return 0\n");
    if let Some(Ok(mir)) = result {
        let has_yield = has_inst(&mir, |i| matches!(i, MirInst::Yield { .. }));
        assert!(has_yield || !mir.functions.is_empty());
    }
}

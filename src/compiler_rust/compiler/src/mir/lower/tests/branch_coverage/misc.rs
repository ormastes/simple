//! Miscellaneous branch coverage tests for MIR lowering
//!
//! Additional coverage tests, direct MIR construction, constants, unary/binary ops,
//! load/store, closures, attribute dedup, lowerer state, and remaining variants.

use super::super::common::*;
use super::helpers::*;
use crate::hir::{self, BinOp, HirExpr, HirExprKind};
use crate::mir::lower::{ContractMode, MirLowerer};
use crate::mir::function::MirFunction;
use crate::mir::{self, CallTarget, MirInst, Terminator};

// =============================================================================
// Additional coverage: bool boxing, if-expr, contracts, attrs
// =============================================================================

#[test]
fn index_set_bool_index_boxing() {
    let src = "fn test():\n    var arr = [1, 2, 3]\n    var b = true\n    arr[b] = 42\n";
    let _ = compile_to_mir(src);
}

#[test]
fn index_set_bool_value_in_array() {
    let src = "fn test():\n    var arr = [true, false]\n    arr[0] = true\n";
    let _ = compile_to_mir(src);
}

#[test]
fn print_bool_direct() {
    let src = "fn test():\n    var b = true\n    print(b)\n";
    let _ = compile_to_mir(src);
}

#[test]
fn tuple_with_bool_element() {
    let src = "fn test():\n    var t = (true, 1, 2.0)\n";
    let _ = compile_to_mir(src);
}

#[test]
fn array_bool_elements() {
    let src = "fn test():\n    var arr = [true, false, true]\n";
    let _ = compile_to_mir(src);
}

#[test]
fn if_stmt_without_else_as_expr() {
    let src = "fn test() -> i64:\n    var x = 0\n    if true:\n        x = 1\n    return x\n";
    let _ = compile_to_mir(src);
}

#[test]
fn contract_with_ensures_and_return() {
    let src = "fn add(a: i64, b: i64) -> i64:\n    in:\n        a >= 0\n    out(ret):\n        ret > 0\n    return a + b + 1\n";
    let _ = compile_to_mir(src);
}

#[test]
fn contract_with_old_value() {
    let src = "fn inc(x: i64) -> i64:\n    out(ret):\n        ret > 0\n    return x + 1\n";
    let _ = compile_to_mir(src);
}

#[test]
fn indirect_call_with_function_type() {
    let src = "fn apply(f: fn(i64) -> i64, x: i64) -> i64:\n    return f(x)\n";
    let _ = compile_to_mir(src);
}

#[test]
fn method_call_with_type_qualifier() {
    let src = "struct Vec2:\n    x: f64\n    y: f64\n\nimpl Vec2:\n    fn len() -> f64:\n        return self.x\n\nfn test() -> i64:\n    var v = Vec2(x: 3.0, y: 4.0)\n    var l = v.len()\n    return 0\n";
    let _ = compile_to_mir(src);
}

#[test]
fn enum_variant_via_lookup() {
    let src = "enum Dir:\n    Up\n    Down\n\nfn test() -> i64:\n    var d = Dir.Up\n    return 0\n";
    let _ = compile_to_mir(src);
}

// --- lowering_stmt.rs: field set assignment ---

#[test]
fn field_set_assignment() {
    let src = "struct Point:\n    x: i64\n    y: i64\n\nfn test() -> i64:\n    var p = Point(x: 1, y: 2)\n    p.x = 10\n    return p.x\n";
    let _ = compile_to_mir(src);
}

// --- lowering_stmt.rs: loop statement ---

#[test]
fn infinite_loop_with_break() {
    let src = "fn test() -> i64:\n    var x = 0\n    loop:\n        x = x + 1\n        if x > 5:\n            break\n    return x\n";
    let _ = compile_to_mir(src);
}

#[test]
fn loop_with_continue() {
    let src = "fn test() -> i64:\n    var x = 0\n    var sum = 0\n    loop:\n        x = x + 1\n        if x > 10:\n            break\n        if x % 2 == 0:\n            continue\n        sum = sum + x\n    return sum\n";
    let _ = compile_to_mir(src);
}

// --- lowering_stmt.rs: for-in statement ---

#[test]
fn for_in_range() {
    let src = "fn test() -> i64:\n    var sum = 0\n    for i in 0..5:\n        sum = sum + i\n    return sum\n";
    let _ = compile_to_mir(src);
}

// --- lowering_stmt.rs: assume statement ---

#[test]
fn assume_statement() {
    let src = "fn test(x: i64) -> i64:\n    assume x > 0\n    return x\n";
    let _ = compile_to_mir(src);
}

// --- lowering_stmt.rs: if-else with different value types (merge) ---

#[test]
fn if_else_different_values() {
    let src = "fn test(flag: bool) -> i64:\n    var x = if flag:\n        42\n    else:\n        99\n    return x\n";
    let _ = compile_to_mir(src);
}

// --- lowering_contracts.rs: postcondition with old() ---

#[test]
fn postcondition_with_in_and_out() {
    let src = "fn divide(a: i64, b: i64) -> i64:\n    in:\n        b != 0\n    out(ret):\n        ret >= 0\n    return a / b\n";
    let _ = compile_to_mir(src);
}

// --- lowering_expr.rs: vec literal ---

#[test]
fn vec_literal() {
    let src = "fn test() -> i64:\n    var v = vec[1, 2, 3]\n    return 0\n";
    let _ = try_compile_to_mir(src);
}

// --- lowering_expr.rs: pointer new ---

#[test]
fn pointer_new_expr() {
    let src = "fn test() -> i64:\n    var x = 42\n    var p = &x\n    return x\n";
    let _ = try_compile_to_mir(src);
}

// --- lowering_expr.rs: yield / generator ---

#[test]
fn generator_yield() {
    let src = "fn gen() -> i64:\n    yield 1\n    yield 2\n    return 0\n";
    let _ = try_compile_to_mir(src);
}

// --- lowering_expr.rs: await / future ---

#[test]
fn async_await_expr() {
    let src = "async fn fetch() -> i64:\n    return 42\n\nfn test() -> i64:\n    var result = await fetch()\n    return result\n";
    let _ = try_compile_to_mir(src);
}

// --- lowering_expr.rs: neighbor access ---

#[test]
fn neighbor_access() {
    let src = "fn test(arr: [i64]) -> i64:\n    var x = arr.north\n    return 0\n";
    let _ = try_compile_to_mir(src);
}

// --- lowering_stmt.rs: return with error contracts ---

#[test]
fn return_in_function_with_postcondition() {
    let src =
        "fn abs(x: i64) -> i64:\n    out(ret):\n        ret >= 0\n    if x < 0:\n        return 0 - x\n    return x\n";
    let _ = compile_to_mir(src);
}

// --- lowering_stmt.rs: admit statement ---

#[test]
fn admit_statement() {
    let src = "fn test(x: i64) -> i64:\n    admit x > 0\n    return x\n";
    let _ = try_compile_to_mir(src);
}

// --- lowering_expr.rs: box float ---

#[test]
fn box_float_to_any() {
    let src = "fn test() -> i64:\n    var x: f64 = 3.14\n    print(x)\n    return 0\n";
    let _ = compile_to_mir(src);
}

// --- lowering_stmt.rs: index set with array ---

#[test]
fn array_index_set() {
    let src = "fn test() -> i64:\n    var arr = [1, 2, 3]\n    arr[0] = 10\n    return arr[0]\n";
    let _ = compile_to_mir(src);
}

// --- lowering_expr.rs: string interpolation ---

#[test]
fn string_interpolation() {
    let src = "fn test() -> i64:\n    var name = \"world\"\n    var greeting = \"hello {name}\"\n    return 0\n";
    let _ = compile_to_mir(src);
}

// --- lowering_expr.rs: FFI call with int arg (box int for FFI) ---

#[test]
fn ffi_call_with_int_arg() {
    let src = "fn test() -> i64:\n    var x = 42\n    var s = str(x)\n    return 0\n";
    let _ = try_compile_to_mir(src);
}

// --- lowering_expr.rs: index with bool key ---

#[test]
fn dict_index_with_bool_key() {
    let src = "fn test() -> i64:\n    var d = {true: 1, false: 0}\n    var x = d[true]\n    return 0\n";
    let _ = try_compile_to_mir(src);
}

// --- lowering_stmt.rs: for-in with new local ---

#[test]
fn for_in_with_array_literal() {
    let src = "fn test() -> i64:\n    var sum = 0\n    for x in [1, 2, 3]:\n        sum = sum + x\n    return sum\n";
    let _ = compile_to_mir(src);
}

// --- lowering_stmt.rs: return error result ---

#[test]
fn return_err_value() {
    let src =
        "enum Result:\n    Ok(i64)\n    Err(i64)\n\nfn test() -> i64:\n    var r = Result.Err(42)\n    return 0\n";
    let _ = try_compile_to_mir(src);
}

// --- lowering_expr.rs: index set with float value ---

#[test]
fn array_index_set_with_float() {
    let src = "fn test() -> i64:\n    var arr = [1.0, 2.0, 3.0]\n    arr[0] = 10.0\n    return 0\n";
    let _ = try_compile_to_mir(src);
}

// --- lowering_expr.rs: struct init with inject ---

#[test]
fn struct_with_inject_annotation() {
    let src = "@inject\nfn get_value(x: i64) -> i64:\n    return x\n\nfn test() -> i64:\n    return get_value()\n";
    let _ = try_compile_to_mir(src);
}

// --- lowering_stmt.rs: match with enum patterns ---

#[test]
fn match_enum_patterns() {
    let src = "enum Color:\n    Red\n    Blue\n    Green\n\nfn test() -> i64:\n    var c = Color.Red\n    match c:\n        Color.Red:\n            return 1\n        Color.Blue:\n            return 2\n        Color.Green:\n            return 3\n    return 0\n";
    let _ = try_compile_to_mir(src);
}

// --- lowering_stmt.rs: variable binding in for-in (pattern) ---

#[test]
fn for_in_existing_var() {
    let src = "fn test() -> i64:\n    var total = 0\n    var i = 0\n    for i in [10, 20, 30]:\n        total = total + i\n    return total\n";
    let _ = try_compile_to_mir(src);
}

// --- lowering_core.rs: with_file ---

#[test]
fn lowerer_with_file() {
    let lowerer = MirLowerer::new().with_file("test.spl".to_string());
    assert!(lowerer.state().is_idle());
}

// --- lowering_core.rs: idle state methods ---

#[test]
fn lowerer_state_idle_methods() {
    use super::super::super::lowering_core::LowererState;
    let state = LowererState::Idle;
    assert!(state.is_idle());
    assert!(!state.is_lowering());
    assert!(state.try_current_block().is_err());
    assert_eq!(state.loop_depth(), 0);
}

#[test]
fn lowerer_state_try_loop_stack_idle() {
    use super::super::super::lowering_core::LowererState;
    let state = LowererState::Idle;
    assert!(state.try_loop_stack().is_err());
}

// --- lowering_core.rs: vtable/trait methods ---

#[test]
fn lowerer_get_vtable_slot_none() {
    let lowerer = MirLowerer::new();
    assert!(lowerer.get_vtable_slot("NonExistent", "method").is_none());
}

#[test]
fn lowerer_get_trait_method_sig_none() {
    let lowerer = MirLowerer::new();
    assert!(lowerer.get_trait_method_signature("NonExistent", "method").is_none());
}

#[test]
fn lowerer_contract_mode() {
    let lowerer = MirLowerer::new();
    assert_eq!(lowerer.contract_mode(), ContractMode::All);
}

// --- lowering_core.rs: begin_function when already lowering ---

#[test]
fn lowerer_begin_function_when_lowering() {
    let mut lowerer = MirLowerer::new();
    let func = MirFunction::new(
        "f1".to_string(),
        hir::TypeId::I64,
        simple_parser::ast::Visibility::Private,
    );
    lowerer.begin_function(func, "f1", false).unwrap();

    let func2 = MirFunction::new(
        "f2".to_string(),
        hir::TypeId::I64,
        simple_parser::ast::Visibility::Private,
    );
    assert!(lowerer.begin_function(func2, "f2", false).is_err());
}

// --- lowering_core.rs: end_function when idle ---

#[test]
fn lowerer_end_function_when_idle() {
    let mut lowerer = MirLowerer::new();
    assert!(lowerer.end_function().is_err());
}

// --- lowering_core.rs: with_func when idle ---

#[test]
fn lowerer_with_func_when_idle() {
    let mut lowerer = MirLowerer::new();
    let result = lowerer.with_func(|func, _| func.new_vreg());
    assert!(result.is_err());
}

// --- lowering_core.rs: set_current_block when idle ---

#[test]
fn lowerer_set_current_block_when_idle() {
    let mut lowerer = MirLowerer::new();
    assert!(lowerer.set_current_block(crate::mir::BlockId(0)).is_err());
}

// --- lowering_coverage.rs: emit_path_probe with coverage enabled ---

#[test]
fn coverage_emit_path_probe_enabled() {
    let mut lowerer = MirLowerer::new().with_coverage(true);
    let mut func = MirFunction::new(
        "cov_test".to_string(),
        hir::TypeId::I64,
        simple_parser::ast::Visibility::Private,
    );
    func.new_block();
    lowerer.begin_function(func, "cov_test", false).unwrap();
    let result = lowerer.emit_path_probe(1, 0);
    assert!(result.is_ok());
}

// --- lowering_gpu.rs: attrs deduplication branches ---

#[test]
fn extract_attrs_already_has_inject() {
    let lowerer = MirLowerer::new();
    let func = hir::HirFunction {
        name: "f".to_string(),
        span: None,
        params: vec![],
        locals: vec![],
        return_type: hir::TypeId::I64,
        body: vec![],
        visibility: simple_parser::ast::Visibility::Public,
        contract: None,
        is_pure: false,
        inject: true,
        concurrency_mode: hir::ConcurrencyMode::Actor,
        module_path: "".to_string(),
        attributes: vec!["inject".to_string()],
        effects: vec![],
        layout_hint: None,
        verification_mode: Default::default(),
        is_ghost: false,
        is_sync: false,
        has_suspension: false,
    };
    let attrs = lowerer.extract_function_attributes(&func);
    assert_eq!(attrs.iter().filter(|a| *a == "inject").count(), 1);
}

#[test]
fn extract_attrs_already_has_pure() {
    let lowerer = MirLowerer::new();
    let func = hir::HirFunction {
        name: "f".to_string(),
        span: None,
        params: vec![],
        locals: vec![],
        return_type: hir::TypeId::I64,
        body: vec![],
        visibility: simple_parser::ast::Visibility::Public,
        contract: None,
        is_pure: true,
        inject: false,
        concurrency_mode: hir::ConcurrencyMode::Actor,
        module_path: "".to_string(),
        attributes: vec!["pure".to_string()],
        effects: vec![],
        layout_hint: None,
        verification_mode: Default::default(),
        is_ghost: false,
        is_sync: false,
        has_suspension: false,
    };
    let attrs = lowerer.extract_function_attributes(&func);
    assert_eq!(attrs.iter().filter(|a| *a == "pure").count(), 1);
}

#[test]
fn extract_attrs_already_has_mode() {
    let lowerer = MirLowerer::new();
    let func = hir::HirFunction {
        name: "f".to_string(),
        span: None,
        params: vec![],
        locals: vec![],
        return_type: hir::TypeId::I64,
        body: vec![],
        visibility: simple_parser::ast::Visibility::Public,
        contract: None,
        is_pure: false,
        inject: false,
        concurrency_mode: hir::ConcurrencyMode::Actor,
        module_path: "".to_string(),
        attributes: vec!["actor".to_string()],
        effects: vec![],
        layout_hint: None,
        verification_mode: Default::default(),
        is_ghost: false,
        is_sync: false,
        has_suspension: false,
    };
    let attrs = lowerer.extract_function_attributes(&func);
    assert_eq!(attrs.iter().filter(|a| *a == "actor").count(), 1);
}

#[test]
fn extract_effects_already_has_async() {
    let lowerer = MirLowerer::new();
    let func = hir::HirFunction {
        name: "f".to_string(),
        span: None,
        params: vec![],
        locals: vec![],
        return_type: hir::TypeId::I64,
        body: vec![],
        visibility: simple_parser::ast::Visibility::Public,
        contract: None,
        is_pure: false,
        inject: false,
        concurrency_mode: hir::ConcurrencyMode::Actor,
        module_path: "".to_string(),
        attributes: vec![],
        effects: vec!["async".to_string()],
        layout_hint: None,
        verification_mode: Default::default(),
        is_ghost: false,
        is_sync: false,
        has_suspension: false,
    };
    let effects = lowerer.extract_function_effects(&func);
    assert_eq!(effects.iter().filter(|a| *a == "async").count(), 1);
}


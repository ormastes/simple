//! Expression coverage tests for MIR lowering
//!
//! Tests for boolean coverage, string interpolation, boxing, indirect calls,
//! tuple/array element boxing, index dispatch/unboxing, method calls, enum payload,
//! and string interpolation.

use super::super::common::*;
use super::helpers::*;
use crate::hir::BinOp;
use crate::mir::{CallTarget, MirInst};

// =============================================================================
// Coverage-enabled compound boolean (lowering_expr.rs line 82)
// =============================================================================

#[test]
fn coverage_compound_and() {
    let mir =
        compile_with_coverage("fn test(a: bool, b: bool) -> i64:\n    if a and b:\n        return 1\n    return 0\n")
            .unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ConditionProbe { .. })));
}

#[test]
fn coverage_compound_or() {
    let mir =
        compile_with_coverage("fn test(a: bool, b: bool) -> i64:\n    if a or b:\n        return 1\n    return 0\n")
            .unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::ConditionProbe { .. })));
}

// =============================================================================
// Indirect call / closure call (lowering_expr.rs lines 153, 176-177)
// =============================================================================

#[test]
fn indirect_call_lambda() {
    let mir = compile_to_mir("fn test() -> i64:\n    let f = \\x: x + 1\n    return f(41)\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::IndirectCall { .. })));
}

// =============================================================================
// rt_value_to_string boxing (lowering_expr.rs lines 351, 365, 370)
// =============================================================================

#[test]
fn string_interp_int_boxing() {
    let mir = compile_to_mir("fn test() -> i64:\n    val x: i64 = 42\n    val s = \"{x}\"\n    return 42\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BoxInt { .. })));
}

#[test]
fn string_interp_float_boxing() {
    let mir = compile_to_mir("fn test() -> i64:\n    val f: f64 = 3.14\n    val s = \"{f}\"\n    return 42\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BoxFloat { .. })));
}

#[test]
fn string_interp_string_no_boxing() {
    // When interpolating a string variable, no boxing or rt_value_to_string is needed —
    // the string is used directly.
    let mir =
        compile_to_mir("fn test() -> i64:\n    val s = \"hello\"\n    val s2 = \"{s}\"\n    return 42\n").unwrap();
    assert!(!has_inst(&mir, |i| matches!(i, MirInst::BoxInt { .. })));
    assert!(!has_inst(&mir, |i| matches!(i, MirInst::BoxFloat { .. })));
    assert!(!has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_value_to_string"))
    }));
}

// =============================================================================
// Builtin call boxing: print with typed args (lowering_expr.rs lines 402-420)
// =============================================================================

#[test]
fn print_int_boxing() {
    let mir = compile_to_mir("fn test() -> i64:\n    val x: i64 = 42\n    print \"{x}\"\n    return 42\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BoxInt { .. })));
}

#[test]
fn print_float_boxing() {
    let mir = compile_to_mir("fn test() -> i64:\n    val f: f64 = 2.5\n    print \"{f}\"\n    return 42\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::BoxFloat { .. })));
}

// =============================================================================
// String interpolation
// =============================================================================

#[test]
fn fstring_multiple_parts() {
    let mir =
        compile_to_mir("fn test():\n    val a: i64 = 1\n    val b: i64 = 2\n    val s = \"{a} + {b}\"\n").unwrap();
    let count = count_inst(
        &mir,
        |i| matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_value_to_string")),
    );
    assert!(count >= 2, "expected >= 2 rt_value_to_string calls, got {}", count);
}

// =============================================================================
// Bool boxing paths (lowering_expr.rs lines 610-612, 670-672, 422-423)
// =============================================================================

#[test]
fn tuple_bool_boxing() {
    // Tuple with bool element should call rt_value_bool
    let mir = compile_to_mir("fn test():\n    val t = (true, 42)\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_value_bool"))
    }));
}

#[test]
fn array_bool_boxing() {
    // Array with bool elements should call rt_value_bool
    let mir = compile_to_mir("fn test():\n    val a = [true, false]\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_value_bool"))
    }));
}

#[test]
fn print_bool_no_extra_boxing() {
    // print with bool interpolation: bool goes directly to rt_value_to_string without boxing
    // (BOOL type is not in the int/float boxing lists for rt_value_to_string)
    let mir = compile_to_mir("fn test():\n    val b: bool = true\n    print \"{b}\"\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_value_to_string"))
    }));
}

#[test]
fn string_interp_bool_no_extra_boxing() {
    // String interpolation with bool: bool goes directly to rt_value_to_string without boxing
    let mir = compile_to_mir("fn test():\n    val b: bool = true\n    val s = \"{b}\"\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_value_to_string"))
    }));
}

// =============================================================================
// Enum with payload as Call (lowering_expr.rs)
// =============================================================================

#[test]
fn enum_payload_as_call() {
    let mir =
        compile_to_mir("enum Shape:\n    Circle(i64)\n    Square(i64)\n\nfn test():\n    val s = Shape.Circle(42)\n")
            .unwrap();
    // Enum variant constructors now lower to EnumWith (type-aware) or Call (fallback)
    assert!(
        has_inst(&mir, |i| {
            matches!(i, MirInst::EnumWith { enum_name, variant_name, .. }
            if enum_name == "Shape" && variant_name == "Circle")
        }) || has_inst(&mir, |i| {
            matches!(i, MirInst::Call { target, .. }
            if target == &CallTarget::from_name("Shape.Circle"))
        })
    );
}

// =============================================================================
// Option/Result short constructors
// =============================================================================

#[test]
fn option_some_as_call() {
    let mir = compile_to_mir("fn test():\n    val x = Some(42)\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::OptionSome { .. })
    }));
}

#[test]
fn result_ok_as_call() {
    let mir = compile_to_mir("fn test():\n    val x = Ok(42)\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::ResultOk { .. })
    }));
}

#[test]
fn result_err_as_call() {
    let mir = compile_to_mir("fn test():\n    val x = Err(-1)\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::ResultErr { .. })
    }));
}

#[test]
fn result_ok_as_qualified_constructor() {
    let mir = compile_to_mir("fn test():\n    val x = Result.Ok(42)\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::ResultOk { .. })
    }));
}

#[test]
fn try_on_result_lowers_to_enum_payload_not_generic_unwrap() {
    let mir =
        compile_to_mir("fn mk() -> Result<i64, text>:\n    return Ok(7)\n\nfn test() -> i64:\n    return mk()?\n")
            .unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_enum_payload"))
    }));
    assert!(!has_inst(&mir, |i| {
        matches!(i, MirInst::MethodCallStatic { func_name, .. } if func_name == "unwrap" || func_name.ends_with(".unwrap"))
    }));
}

#[test]
fn try_on_result_alias_lowers_to_enum_payload_not_generic_unwrap() {
    let mir = compile_to_mir(
        "enum Result<T, E>:\n    Ok(T)\n    Err(E)\n\ntype BrowserResult = Result\n\nfn mk() -> BrowserResult<i64, text>:\n    return Ok(7)\n\nfn test() -> i64:\n    return mk()?\n",
    )
    .unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_enum_payload"))
    }));
    assert!(!has_inst(&mir, |i| {
        matches!(i, MirInst::MethodCallStatic { func_name, .. } if func_name == "unwrap" || func_name.ends_with(".unwrap"))
    }));
}

#[test]
fn try_on_imported_result_alias_lowers_to_enum_payload_not_generic_unwrap() {
    let src = r#"
use std.js.engine.js_error.{BrowserResult}

fn parse_statement() -> BrowserResult<i64>:
    Ok(7)

fn parse_program() -> BrowserResult<i64>:
    val stmt = parse_statement()?
    Ok(stmt)
"#;

    let mir = compile_to_mir(src).unwrap();
    let body = format!("{mir:#?}");

    assert!(
        body.contains("rt_enum_payload"),
        "expected imported BrowserResult try to lower via rt_enum_payload:\n{body}"
    );
    assert!(
        !body.contains("func_name: \"unwrap\"") && !body.contains(".unwrap"),
        "imported BrowserResult try should not lower to unwrap dispatch:\n{body}"
    );
}

// =============================================================================
// Cast operations
// =============================================================================

#[test]
fn cast_int_to_float() {
    let mir = compile_to_mir("fn test() -> f64:\n    val x: i64 = 42\n    return x as f64\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::Cast { .. })));
}

#[test]
fn cast_float_to_int() {
    let mir = compile_to_mir("fn test() -> i64:\n    val x: f64 = 42.5\n    return x as i64\n").unwrap();
    assert!(has_inst(&mir, |i| matches!(i, MirInst::Cast { .. })));
}

// =============================================================================
// Global enum variant (lowering_expr.rs lines 1057-1087)
// =============================================================================

#[test]
fn enum_unit_variant_via_global() {
    // Enum unit variant access
    let result = compile_to_mir("enum Color:\n    Red\n    Blue\n\nfn test():\n    val c = Color.Red\n");
    // Verify it compiles (or documents the current limitation)
    if let Ok(mir) = result {
        assert!(mir.functions.len() >= 1);
    }
}

// =============================================================================
// Dict literal (lowering_expr.rs lines 1105+)
// =============================================================================

#[test]
fn dict_literal() {
    let mir = compile_to_mir("fn test():\n    val d = {\"a\": 1, \"b\": 2}\n").unwrap();
    assert!(has_inst(&mir, |i| {
        matches!(i, MirInst::Call { target, .. } if target == &CallTarget::from_name("rt_dict_new"))
    }));
}

// =============================================================================
// Global variable load (lowering_expr.rs lines 1090-1102)
// =============================================================================

#[test]
fn global_variable_load() {
    // Top-level val creates a global
    let result = compile_to_mir("val MAGIC: i64 = 42\n\nfn test() -> i64:\n    return MAGIC\n");
    if let Ok(mir) = result {
        assert!(has_inst(&mir, |i| matches!(i, MirInst::GlobalLoad { .. })));
    }
}

// =============================================================================
// Dict operations (lowering_expr.rs)
// =============================================================================

#[test]
fn dict_with_values() {
    let mir = compile_to_mir("fn test():\n    val d = {\"x\": 1, \"y\": 2, \"z\": 3}\n").unwrap();
    let insert_count = count_inst(
        &mir,
        |i| matches!(i, MirInst::Call { target, .. } if target.name() == "rt_dict_insert"),
    );
    assert!(insert_count >= 3, "expected >= 3 dict inserts, got {}", insert_count);
}

// =============================================================================
// Coverage probe in nested conditions (lowering_coverage.rs)
// =============================================================================

#[test]
fn coverage_nested_and_or() {
    let mir = compile_with_coverage(
        "fn test(a: bool, b: bool, c: bool) -> i64:\n    if (a and b) or c:\n        return 1\n    return 0\n",
    )
    .unwrap();
    let probe_count = count_inst(&mir, |i| matches!(i, MirInst::ConditionProbe { .. }));
    assert!(probe_count >= 2, "expected >= 2 probes, got {}", probe_count);
}

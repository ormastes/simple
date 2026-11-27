//! Typed boolean array boundary representation tests.

use super::common::compile_to_mir;
use crate::mir::{CallTarget, MirInst};

const SOURCE: &str = r#"fn push_bool(values: [bool], item: bool):
    values.push(item)
fn find_bool(values: [bool], item: bool) -> i64:
    values.index_of(item)
fn push_integer(values: [i64], item: i64):
    values.push(item)
fn find_integer(values: [i64], item: i64) -> i64:
    values.index_of(item)
"#;

fn assert_method_argument_boxing(function_name: &str, method: &str, expected: &str) {
    let mir = compile_to_mir(SOURCE).expect("array argument boxing fixture lowers");
    let function = mir
        .functions
        .iter()
        .find(|function| function.name == function_name)
        .unwrap_or_else(|| panic!("missing MIR function {function_name}"));
    let item_param_index = function
        .params
        .iter()
        .position(|param| param.name == "item")
        .expect("item parameter exists");
    let instructions: Vec<_> = function
        .blocks
        .iter()
        .flat_map(|block| block.instructions.iter())
        .collect();

    let tagged_bool_defs: std::collections::HashSet<_> = instructions
        .iter()
        .filter_map(|instruction| match instruction {
            MirInst::Call { dest: Some(dest), target, .. }
                if target == &CallTarget::from_name("rt_value_bool") => Some(*dest),
            _ => None,
        })
        .collect();
    let int_box_defs: std::collections::HashSet<_> = instructions
        .iter()
        .filter_map(|instruction| match instruction {
            MirInst::BoxInt { dest, .. } => Some(*dest),
            _ => None,
        })
        .collect();
    let item_addresses: std::collections::HashSet<_> = instructions
        .iter()
        .filter_map(|instruction| match instruction {
            MirInst::LocalAddr { dest, local_index } if *local_index == item_param_index => Some(*dest),
            _ => None,
        })
        .collect();
    let item_loads: std::collections::HashSet<_> = instructions
        .iter()
        .filter_map(|instruction| match instruction {
            MirInst::Load { dest, addr, .. } if item_addresses.contains(addr) => Some(*dest),
            _ => None,
        })
        .collect();
    let (method_args, signed_i64_push) = instructions
        .iter()
        .find_map(|instruction| match (method, instruction) {
            ("push", MirInst::Call { target, args, .. })
                if target == &CallTarget::from_name("rt_array_push") => Some((args.as_slice(), false)),
            ("push", MirInst::Call { target, args, .. })
                if target == &CallTarget::from_name("rt_typed_words_i64_push") => Some((args.as_slice(), true)),
            ("index_of", MirInst::MethodCallStatic { func_name, args, .. })
                if func_name == "index_of" || func_name.ends_with(".index_of") => Some((args.as_slice(), false)),
            _ => None,
        })
        .unwrap_or_else(|| panic!("missing {method} MIR call in {function_name}"));
    let value_argument_index = if method == "push" { 1 } else { 0 };
    let argument = *method_args
        .get(value_argument_index)
        .expect("method has a value argument");

    match expected {
        "bool" => {
            assert!(!signed_i64_push, "typed bool push must not use the signed i64 specialized lane");
            assert!(
                tagged_bool_defs.contains(&argument),
                "typed bool {method} argument must be defined by rt_value_bool"
            );
            assert!(
                !int_box_defs.contains(&argument),
                "typed bool {method} argument must not be defined by BoxInt"
            );
            assert!(instructions.iter().any(|instruction| matches!(instruction,
                MirInst::Call { dest: Some(dest), target, args }
                    if *dest == argument
                        && target == &CallTarget::from_name("rt_value_bool")
                        && args.iter().any(|arg| item_loads.contains(arg))
            )), "the rt_value_bool input must be loaded from the item parameter");
        }
        "integer" if method == "push" => {
            assert!(signed_i64_push, "typed i64 statement push uses the signed-word array lane");
            assert!(item_loads.contains(&argument), "signed i64 push receives the loaded item parameter raw");
            assert!(!int_box_defs.contains(&argument), "signed i64 push keeps its raw integer representation");
        }
        "integer" => assert!(instructions.iter().any(|instruction| matches!(instruction,
            MirInst::BoxInt { dest, value }
                if *dest == argument && item_loads.contains(value)
        )), "typed integer {method} must BoxInt the loaded item parameter"),
        other => panic!("unsupported expected boxing {other}"),
    }
}

#[test]
fn array_push_typed_bool_uses_canonical_runtime_bool_tag() {
    assert_method_argument_boxing("push_bool", "push", "bool");
}

#[test]
fn array_index_of_typed_bool_uses_canonical_runtime_bool_tag() {
    assert_method_argument_boxing("find_bool", "index_of", "bool");
}

#[test]
fn array_push_typed_i64_uses_raw_signed_word_lane() {
    assert_method_argument_boxing("push_integer", "push", "integer");
}

#[test]
fn array_index_of_typed_integer_keeps_integer_boxing() {
    assert_method_argument_boxing("find_integer", "index_of", "integer");
}

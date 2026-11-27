//! Return-only collisions must fail before duplicate MIR bodies overwrite.

use simple_compiler::hir::{self, HirType, TypeId};
use simple_compiler::mir::lower_to_mir;
use simple_parser::Parser;

fn composed_module(second_return: &str, second_parameter: &str) -> hir::HirModule {
    let source = format!(
        "fn first(value: i64) -> i64:\n    return value\n\n\
         fn second(value: {second_parameter}) -> {second_return}:\n    return value\n"
    );
    let ast = Parser::new(&source).parse().expect("fixture parses");
    let mut module = hir::lower(&ast).expect("fixture lowers to HIR");
    assert_eq!(module.functions.len(), 2);
    // Model two module-private definitions after namespace flattening without
    // depending on the parser accepting duplicate declarations in one file.
    for function in &mut module.functions {
        function.name = "_private_pick".to_string();
    }
    module
}

#[test]
fn return_only_collision_is_rejected_before_last_write_wins() {
    let mut module = composed_module("i64", "i64");
    // Return bodies are immaterial: this collision must fail in signature
    // collection, before either body is lowered or selected by argument type.
    module.functions[1].return_type = hir::TypeId::STRING;
    let error = lower_to_mir(&module).expect_err("return-only collision must fail");
    let message = error.to_string();
    assert!(message.contains("identical parameter types"), "{message}");
    assert!(
        message.contains("different primitive return types"),
        "{message}"
    );
    assert!(
        message.contains("compiler_cross_module_private_symbol_collision"),
        "{message}"
    );
}

#[test]
fn identical_parameter_and_return_signatures_keep_existing_behavior() {
    lower_to_mir(&composed_module("i64", "i64")).expect("identical signatures remain accepted");
}

#[test]
fn distinct_parameter_types_still_receive_separate_mir_names() {
    let module = composed_module("bool", "bool");
    let mir = lower_to_mir(&module)
        .expect("parameter-distinct definitions are not return-only collisions");
    let names: Vec<_> = mir
        .functions
        .iter()
        .map(|function| function.name.as_str())
        .collect();
    assert!(names.contains(&"_private_pick$dup0"));
    assert!(names.contains(&"_private_pick$dup1"));
}

#[test]
fn independently_registered_equivalent_array_returns_are_not_rejected() {
    let source = "fn first(value: i64) -> [i64]:\n    return [value]\n\n\
                  fn second(value: i64) -> [i64]:\n    return [value]\n";
    let ast = Parser::new(source).parse().expect("array fixture parses");
    let mut module = hir::lower(&ast).expect("array fixture lowers to HIR");
    let first_type = module.types.register(HirType::Array {
        element: TypeId::I64,
        size: None,
    });
    let second_type = module.types.register(HirType::Array {
        element: TypeId::I64,
        size: None,
    });
    assert_ne!(
        first_type, second_type,
        "fixture must exercise fresh structural IDs"
    );
    for (index, function) in module.functions.iter_mut().enumerate() {
        function.name = "_private_pick".to_string();
        function.return_type = if index == 0 { first_type } else { second_type };
    }
    lower_to_mir(&module).expect("equivalent array returns are not proven incompatible");
}

#[test]
fn independently_registered_equivalent_tuple_returns_are_not_rejected() {
    let source = "fn first(value: i64) -> (i64, bool):\n    return (value, true)\n\n\
                  fn second(value: i64) -> (i64, bool):\n    return (value, true)\n";
    let ast = Parser::new(source).parse().expect("tuple fixture parses");
    let mut module = hir::lower(&ast).expect("tuple fixture lowers to HIR");
    let first_type = module
        .types
        .register(HirType::Tuple(vec![TypeId::I64, TypeId::BOOL]));
    let second_type = module
        .types
        .register(HirType::Tuple(vec![TypeId::I64, TypeId::BOOL]));
    assert_ne!(
        first_type, second_type,
        "fixture must exercise fresh structural IDs"
    );
    for (index, function) in module.functions.iter_mut().enumerate() {
        function.name = "_private_pick".to_string();
        function.return_type = if index == 0 { first_type } else { second_type };
    }
    lower_to_mir(&module).expect("equivalent tuple returns are not proven incompatible");
}

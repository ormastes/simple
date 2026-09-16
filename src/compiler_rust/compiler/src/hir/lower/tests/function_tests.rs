use super::super::super::types::*;
use super::super::*;
use super::parse_and_lower;
use std::collections::HashMap;
use std::sync::Arc;

#[test]
fn test_lower_simple_function() {
    let module = parse_and_lower("fn add(a: i64, b: i64) -> i64:\n    return a + b\n").unwrap();

    assert_eq!(module.functions.len(), 1);
    let func = &module.functions[0];
    assert_eq!(func.name, "add");
    assert_eq!(func.params.len(), 2);
    assert_eq!(func.return_type, TypeId::I64);
}

#[test]
fn test_basic_types() {
    // Test basic types: i64, str, bool, f64
    let module = parse_and_lower("fn greet(name: str) -> i64:\n    let x: i64 = 42\n    return x\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.params[0].ty, TypeId::STRING);
    assert_eq!(func.return_type, TypeId::I64);
    assert_eq!(func.locals[0].ty, TypeId::I64);
}

#[test]
fn declared_return_type_rejects_explicit_and_implicit_mismatches() {
    for source in [
        "fn wrong() -> bool:\n    return \"not-a-bool\"\n",
        "fn wrong() -> bool:\n    \"not-a-bool\"\n",
    ] {
        let error = parse_and_lower(source).expect_err("declared bool return must reject text");
        assert!(
            matches!(
                error,
                LowerError::TypeMismatch {
                    expected: TypeId::BOOL,
                    found: TypeId::STRING
                }
            ),
            "unexpected diagnostic: {error:?}"
        );
    }
}

#[test]
fn declared_return_type_accepts_same_name_struct_across_registration_paths() {
    // TypeIds are module-registry-local (every HirModule owns its own
    // TypeRegistry; `register` always allocates a fresh id, and imported
    // named types are re-registered per module), so a declared `-> Pair`
    // and a returned Pair value can carry DIFFERENT TypeIds for the same
    // nominal type -- the day the declared-return check landed, raw
    // TypeId equality rejected 542 previously valid app files. Named
    // aggregates must compare by name, not by registry-local id. This
    // fixture pins the accepted case; cross-module import re-registration
    // is exercised by the full bootstrap closure.
    let source = "fn make() -> Pair:\n    return Pair{a: 1, b: 2}\n";
    let mut parser = simple_parser::Parser::new(source);
    let module = parser.parse().expect("parse failed");

    let mut lowerer = Lowerer::new();
    lowerer.set_global_struct_defs(Arc::new(HashMap::from([(
        "Pair".to_string(),
        vec![
            ("a".to_string(), simple_parser::Type::Simple("i64".to_string())),
            ("b".to_string(), simple_parser::Type::Simple("i64".to_string())),
        ],
    )])));

    let lowered = lowerer
        .lower_module(&module)
        .expect("same-name struct return across registration paths must be accepted");
    assert_eq!(lowered.functions.len(), 1);
}

#[test]
fn test_lower_function_with_locals() {
    let module = parse_and_lower("fn compute(x: i64) -> i64:\n    let y: i64 = x * 2\n    return y\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.params.len(), 1);
    assert_eq!(func.locals.len(), 1);
    assert_eq!(func.locals[0].name, "y");
}

#[test]
fn test_multiple_functions() {
    let module = parse_and_lower(
        "fn foo() -> i64:\n    return 1\n\nfn bar() -> i64:\n    return 2\n\nfn baz() -> i64:\n    return 3\n",
    )
    .unwrap();

    assert_eq!(module.functions.len(), 3);
    assert_eq!(module.functions[0].name, "foo");
    assert_eq!(module.functions[1].name, "bar");
    assert_eq!(module.functions[2].name, "baz");
}

#[test]
fn test_function_with_multiple_params() {
    let module = parse_and_lower("fn multi(a: i64, b: f64, c: str, d: bool) -> i64:\n    return a\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.params.len(), 4);
    assert_eq!(func.params[0].ty, TypeId::I64);
    assert_eq!(func.params[1].ty, TypeId::F64);
    assert_eq!(func.params[2].ty, TypeId::STRING);
    assert_eq!(func.params[3].ty, TypeId::BOOL);
}

#[test]
fn extern_call_preserves_declared_optional_array_return_type() {
    let source = r#"
extern fn snapshot() -> [(text, text)]?

fn snapshot_len() -> i64:
    val entries = snapshot() ?? []
    var seen = 0
    for entry in entries:
        val (key, value) = entry
        if key.len() >= 0 and value.len() >= 0:
            seen = seen + 1
    entries.len() + seen
"#;
    parse_and_lower(source).expect("declared extern return type must survive calls, coalescing, len, and iteration");
}

#[test]
fn unannotated_value_function_uses_tagged_any_return_instead_of_void() {
    let module = parse_and_lower(
        "fn no_ret_type(data: [i64], index: i64):\n    data[index]\n\nfn caller() -> i64:\n    no_ret_type([7, 8, 9], 1)\n",
    )
    .expect("unannotated value function must lower");

    let callee = module
        .functions
        .iter()
        .find(|function| function.name == "no_ret_type")
        .unwrap();
    assert_eq!(callee.return_type, TypeId::ANY);
    assert!(matches!(callee.body.last(), Some(HirStmt::Expr(expr)) if expr.ty == TypeId::I64));
}

#[test]
fn unannotated_procedure_remains_void() {
    let module = parse_and_lower("fn procedure():\n    val value = 1\n").expect("procedure must lower");
    assert_eq!(module.functions[0].return_type, TypeId::VOID);
}

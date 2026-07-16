use super::super::super::types::*;
use super::super::*;
use super::parse_and_lower;
use simple_parser::{Parser, Type};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

#[test]
fn test_lower_literals() {
    let module = parse_and_lower(
        "fn test() -> i64:\n    let a: i64 = 42\n    let b: f64 = 3.15\n    let c: bool = true\n    return a\n",
    )
    .unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 3);
}

#[test]
fn text_rfind_uses_string_method_lowering() {
    let module = parse_and_lower(
        r#"struct text:
    data: i64

impl text:
    fn replace(old: text, new: text) -> text:
        return self

fn parent(path: text) -> i64:
    val normalized = path.replace("x", "/")
    return normalized.rfind("/")
"#,
    )
    .unwrap();
    let function = module.functions.iter().find(|f| f.name == "parent").expect("parent");
    let HirStmt::Return(Some(expr)) = &function.body[1] else {
        panic!("expected return expression");
    };
    assert!(
        matches!(&expr.kind, HirExprKind::MethodCall { dispatch: DispatchMode::Static, method, .. } if method == "rfind")
    );
}

#[test]
fn uppercase_string_is_empty_uses_string_method_lowering() {
    let module = parse_and_lower(
        r#"struct String:
    data: i64

impl String:
    fn trim() -> String:
        return self

fn empty(value: String) -> bool:
    val trimmed = value.trim()
    return trimmed.is_empty()
"#,
    )
    .unwrap();
    let function = module.functions.iter().find(|f| f.name == "empty").expect("empty");
    let HirStmt::Return(Some(expr)) = &function.body[1] else {
        panic!("expected return expression");
    };
    assert!(
        matches!(&expr.kind, HirExprKind::MethodCall { dispatch: DispatchMode::Static, method, .. } if method == "is_empty")
    );
}

#[test]
fn test_lower_danger_block_retains_boundary_and_tail_type() {
    let module = parse_and_lower("fn test() -> i64:\n    danger:\n        val x = 40\n        x + 2\n").unwrap();
    let func = &module.functions[0];
    let HirStmt::Expr(expr) = &func.body[0] else {
        panic!("Expected unsafe block expression");
    };
    assert_eq!(expr.ty, TypeId::I64);
    let HirExprKind::UnsafeBlock(statements) = &expr.kind else {
        panic!("Expected retained unsafe boundary, got {:?}", expr.kind);
    };
    assert_eq!(statements.len(), 2);
    assert!(!format!("{statements:?}").contains("danger"));
}

#[test]
fn test_lower_resolves_constant_receiver_and_acronym_static_type_semantically() {
    let constant_module = parse_and_lower(
        "val FRAME_HEADER_WORDS: i32 = 4\nfn words() -> u32:\n    return FRAME_HEADER_WORDS.to_u32()\n",
    )
    .unwrap();
    let words = constant_module
        .functions
        .iter()
        .find(|function| function.name == "words")
        .unwrap();
    let HirStmt::Return(Some(expr)) = &words.body[0] else {
        panic!("Expected constant conversion return");
    };
    let HirExprKind::MethodCall {
        receiver,
        method,
        dispatch,
        ..
    } = &expr.kind
    else {
        panic!("Expected numeric method call, got {:?}", expr.kind);
    };
    assert!(matches!(receiver.kind, HirExprKind::Global(ref name) if name == "FRAME_HEADER_WORDS"));
    assert_eq!(receiver.ty, TypeId::I32);
    assert_eq!(method, "to_u32");
    assert_eq!(*dispatch, DispatchMode::Static);
    assert_eq!(expr.ty, TypeId::U32);

    parse_and_lower(
        "class TCB:\n    id: i32\n    static fn empty(slot: i32) -> TCB:\n        return TCB(id: slot)\nfn make() -> TCB:\n    return TCB.empty(1)\n",
    )
    .expect("ALL_CAPS acronym types must retain static method resolution");
}

#[test]
fn test_lower_binary_ops() {
    let module = parse_and_lower("fn compare(a: i64, b: i64) -> bool:\n    return a < b\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::BOOL);

    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        assert_eq!(expr.ty, TypeId::BOOL);
    } else {
        panic!("Expected return statement");
    }
}

#[test]
fn test_lower_array_expression() {
    let module = parse_and_lower("fn test() -> i64:\n    let arr = [1, 2, 3]\n    return 0\n").unwrap();

    let func = &module.functions[0];
    assert!(!func.locals.is_empty());
}

// Regression coverage for Phase 0A global variable type resolution fix:
//
// The fix in module_pass.rs ensures `var x: u64 = ...` resolves the type
// from Pattern::Typed when LetStmt.ty is None (the parser's normal path).
//
// Unit tests below are currently blocked from running by pre-existing
// compilation errors in value_tests_basic.rs (E0308: Arc<HashMap> mismatch).
// Integration verification: pure_gui.spl renders via fb_addr global in QEMU.
//
// When value_tests_basic.rs is fixed, uncomment these tests:
//
// #[test]
// fn test_module_level_typed_var_resolves_type() {
//     let module = parse_and_lower(
//         "var addr: u64 = 100\nfn test() -> u64:\n    return addr + 1\n",
//     ).unwrap();
//     let addr_entry = module.globals.iter().find(|(name, _)| name == "addr");
//     assert!(addr_entry.is_some());
//     assert_eq!(addr_entry.unwrap().1, TypeId::I64);
// }
//
// #[test]
// fn test_module_level_typed_val_resolves_type() {
//     let module = parse_and_lower(
//         "val size: u32 = 42\nfn test() -> u32:\n    return size\n",
//     ).unwrap();
//     let size_entry = module.globals.iter().find(|(name, _)| name == "size");
//     assert!(size_entry.is_some());
//     assert_eq!(size_entry.unwrap().1, TypeId::I32);
// }

#[test]
fn test_lower_tuple_expression() {
    let module = parse_and_lower("fn test() -> i64:\n    let t = (1, 2, 3)\n    return 0\n").unwrap();

    let func = &module.functions[0];
    assert!(!func.locals.is_empty());
}

#[test]
fn test_lower_empty_array() {
    let module = parse_and_lower("fn test() -> i64:\n    let arr = []\n    return 0\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 1);
}

#[test]
fn test_empty_array_append_refines_indexed_element_type() {
    let module = parse_and_lower(
        "class Handle:\n    value: i64\n    fn join() -> i64:\n        self.value\n\nfn test() -> i64:\n    var handles = []\n    handles.append(Handle(value: 7))\n    val handle = handles[0]\n    return handle.join()\n",
    )
    .unwrap();

    let func = module.functions.iter().find(|f| f.name == "test").expect("test fn");
    let handles_ty = func.locals[0].ty;
    let Some(HirType::Array { element, size }) = module.types.get(handles_ty) else {
        panic!(
            "expected handles to keep an array type, got {:?}",
            module.types.get(handles_ty)
        );
    };
    assert_eq!(*size, Some(0));
    assert_eq!(module.types.get_type_name(*element).as_deref(), Some("Handle"));
    assert_eq!(module.types.get_type_name(func.locals[1].ty).as_deref(), Some("Handle"));
}

#[test]
fn test_lower_index_expression() {
    let module =
        parse_and_lower("fn test() -> i64:\n    let arr = [1, 2, 3]\n    let x = arr[0]\n    return x\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 2);
}

#[test]
fn test_lower_function_call() {
    let module = parse_and_lower(
        "fn add(a: i64, b: i64) -> i64:\n    return a + b\n\nfn test() -> i64:\n    return add(1, 2)\n",
    )
    .unwrap();

    assert_eq!(module.functions.len(), 2);
}

#[test]
fn test_lower_local_function_value_call_uses_function_return_type() {
    let module = parse_and_lower(
        "class Holder:\n    thunk: fn() -> i64\n\nfn forty_two() -> i64:\n    42\n\nfn test() -> i64:\n    val holder = Holder(thunk: forty_two)\n    val thunk = holder.thunk\n    val value = thunk()\n    return value\n",
    )
    .unwrap();

    let func = module.functions.iter().find(|f| f.name == "test").expect("test fn");
    assert_eq!(
        func.locals[1].ty,
        TypeId::I64,
        "call result local must be typed as the function return type"
    );
    let HirStmt::Return(Some(expr)) = &func.body[3] else {
        panic!("Expected return statement");
    };
    assert_eq!(expr.ty, TypeId::I64);
}

#[test]
fn test_lower_callable_field_method_call_uses_function_return_type() {
    let module = parse_and_lower(
        "class Holder:\n    thunk: fn() -> i64\n\nfn forty_two() -> i64:\n    42\n\nfn test() -> i64:\n    val holder = Holder(thunk: forty_two)\n    val value = holder.thunk()\n    return value\n",
    )
    .unwrap();

    let func = module.functions.iter().find(|f| f.name == "test").expect("test fn");
    assert_eq!(
        func.locals[1].ty,
        TypeId::I64,
        "method-syntax callable field result must use the function return type"
    );
    let HirStmt::Return(Some(expr)) = &func.body[2] else {
        panic!("Expected return statement");
    };
    assert_eq!(expr.ty, TypeId::I64);
}

#[test]
fn test_lower_function_identifier_in_array_keeps_function_value_type() {
    let module = parse_and_lower(
        "var FUNCS: [fn() -> i64] = []\n\nfn worker() -> i64:\n    7\n\nfn test() -> i64:\n    FUNCS = [worker]\n    val thunk = FUNCS[0]\n    val value = thunk()\n    return value\n",
    )
    .unwrap();

    let func = module.functions.iter().find(|f| f.name == "test").expect("test fn");
    let thunk_ty = func.locals[0].ty;
    let Some(HirType::Function { ret, .. }) = module.types.get(thunk_ty) else {
        panic!(
            "expected function-typed local for indexed function value, got {:?}",
            module.types.get(thunk_ty)
        );
    };
    assert_eq!(*ret, TypeId::I64);
    assert_eq!(
        func.locals[1].ty,
        TypeId::I64,
        "calling the indexed function value should produce its return type"
    );
}

#[test]
fn test_lower_function_param_array_keeps_function_value_type() {
    let module = parse_and_lower(
        "fn run_one(step_fn: fn() -> i64) -> i64:\n    val callbacks = [step_fn]\n    val thunk = callbacks[0]\n    val value = thunk()\n    return value\n",
    )
    .unwrap();

    let func = module
        .functions
        .iter()
        .find(|f| f.name == "run_one")
        .expect("run_one fn");
    let callbacks_ty = func.locals[0].ty;
    let Some(HirType::Array { element, .. }) = module.types.get(callbacks_ty) else {
        panic!(
            "expected array-typed local for callbacks, got {:?}",
            module.types.get(callbacks_ty)
        );
    };
    let Some(HirType::Function { ret, .. }) = module.types.get(*element) else {
        panic!(
            "expected function-valued array element for callbacks, got {:?}",
            module.types.get(*element)
        );
    };
    assert_eq!(*ret, TypeId::I64);

    let thunk_ty = func.locals[1].ty;
    let Some(HirType::Function { ret, .. }) = module.types.get(thunk_ty) else {
        panic!(
            "expected function-typed local for indexed param function, got {:?}",
            module.types.get(thunk_ty)
        );
    };
    assert_eq!(*ret, TypeId::I64);
    assert_eq!(
        func.locals[2].ty,
        TypeId::I64,
        "calling the indexed param function should produce its return type"
    );
}

#[test]
fn test_lower_inline_lambda_array_keeps_function_value_type() {
    let module = parse_and_lower(
        "fn run_one() -> i64:\n    val callbacks = [\\: 7]\n    val thunk = callbacks[0]\n    val value = thunk()\n    return value\n",
    )
    .unwrap();

    let func = module
        .functions
        .iter()
        .find(|f| f.name == "run_one")
        .expect("run_one fn");
    let callbacks_ty = func.locals[0].ty;
    let Some(HirType::Array { element, .. }) = module.types.get(callbacks_ty) else {
        panic!(
            "expected array-typed local for callbacks, got {:?}",
            module.types.get(callbacks_ty)
        );
    };
    let Some(HirType::Function { ret, .. }) = module.types.get(*element) else {
        panic!(
            "expected function-valued array element for inline lambda callbacks, got {:?}",
            module.types.get(*element)
        );
    };
    assert_eq!(*ret, TypeId::I64);

    let thunk_ty = func.locals[1].ty;
    let Some(HirType::Function { ret, .. }) = module.types.get(thunk_ty) else {
        panic!(
            "expected function-typed local for indexed inline lambda, got {:?}",
            module.types.get(thunk_ty)
        );
    };
    assert_eq!(*ret, TypeId::I64);
    assert_eq!(
        func.locals[2].ty,
        TypeId::I64,
        "calling the indexed inline lambda should produce its return type"
    );
}

#[test]
fn test_lower_if_expression() {
    let module = parse_and_lower("fn test(x: i64) -> i64:\n    let y = if x > 0: 1 else: 0\n    return y\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 1);
}

#[test]
fn test_lower_string_literal() {
    // Use single quotes for raw string (double quotes create FStrings)
    let module = parse_and_lower("fn test() -> str:\n    return 'hello'\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::STRING);
}

#[test]
fn test_lower_bool_literal() {
    let module = parse_and_lower("fn test() -> bool:\n    return false\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::BOOL);
}

#[test]
fn test_lower_float_literal() {
    let module = parse_and_lower("fn test() -> f64:\n    return 3.15\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.return_type, TypeId::F64);
}

#[test]
fn test_lower_nil_literal() {
    let module = parse_and_lower("fn test() -> i64:\n    let x = nil\n    return 0\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.locals.len(), 1);
}

#[test]
fn test_lower_unary_negation() {
    let module = parse_and_lower("fn test(x: i64) -> i64:\n    return -x\n").unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        assert!(matches!(expr.kind, HirExprKind::Unary { .. }));
    }
}

#[test]
fn test_lower_logical_not() {
    let module = parse_and_lower("fn test(x: bool) -> bool:\n    return not x\n").unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        assert!(matches!(expr.kind, HirExprKind::Unary { .. }));
    }
}

#[test]
fn test_lower_comparison_operators() {
    // Test all comparison operators return bool
    let ops = ["<", ">", "<=", ">=", "==", "!="];
    for op in ops {
        let source = format!("fn test(a: i64, b: i64) -> bool:\n    return a {} b\n", op);
        let module = parse_and_lower(&source).unwrap();
        let func = &module.functions[0];
        assert_eq!(func.return_type, TypeId::BOOL);
    }
}

#[test]
fn test_lower_logical_operators() {
    // Test and/or return bool
    let module = parse_and_lower("fn test(a: bool, b: bool) -> bool:\n    return a and b\n").unwrap();
    assert_eq!(module.functions[0].return_type, TypeId::BOOL);

    let module = parse_and_lower("fn test(a: bool, b: bool) -> bool:\n    return a or b\n").unwrap();
    assert_eq!(module.functions[0].return_type, TypeId::BOOL);
}

#[test]
fn test_lower_field_access() {
    let module =
        parse_and_lower("struct Point:\n    x: i64\n    y: i64\n\nfn test(p: Point) -> i64:\n    return p.x\n")
            .unwrap();

    let func = &module.functions[0];
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        assert!(matches!(expr.kind, HirExprKind::FieldAccess { .. }));
    }
}

#[test]
fn test_lenient_unresolved_uppercase_field_access_becomes_static_variant_global() {
    let source = "fn test():\n    return MissingEnum.NotFound\n";
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");

    let mut lowerer = Lowerer::new();
    lowerer.set_lenient_types(true);
    let lowered = lowerer.lower_module(&module).unwrap();

    let func = &lowered.functions[0];
    let HirStmt::Return(Some(expr)) = &func.body[0] else {
        panic!("Expected return statement");
    };
    assert_eq!(expr.kind, HirExprKind::Global("MissingEnum::NotFound".to_string()));
    assert_eq!(expr.ty, TypeId::ANY);
}

#[test]
fn test_lower_static_enum_variant_constructor_call() {
    let module = parse_and_lower(
        "enum FsError:\n    InvalidArg\n    Transient(code: i32)\n\nfn test() -> FsError:\n    return FsError.Transient(code: 110)\n",
    )
    .unwrap();

    let func = module.functions.iter().find(|f| f.name == "test").unwrap();
    let HirStmt::Return(Some(expr)) = &func.body[0] else {
        panic!("Expected return statement");
    };
    let HirExprKind::Call { func, args } = &expr.kind else {
        panic!("Expected enum variant constructor call");
    };
    assert_eq!(func.kind, HirExprKind::Global("FsError::Transient".to_string()));
    assert_eq!(args.len(), 1);
}

#[test]
fn test_lower_global_enum_variant_constructor_identifier_call() {
    let source = "fn test() -> Type:\n    return Type.Int(bits: 64, signed: true)\n";
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");

    let mut lowerer = Lowerer::new();
    lowerer.set_global_enum_defs(Arc::new(HashMap::from([(
        "Type".to_string(),
        vec![("Int".to_string(), Some(2))],
    )])));
    lowerer.register_global_enums();
    let lowered = lowerer.lower_module(&module).unwrap();

    let func = lowered.functions.iter().find(|f| f.name == "test").unwrap();
    let HirStmt::Return(Some(expr)) = &func.body[0] else {
        panic!("Expected return statement");
    };
    let HirExprKind::Call { func, args } = &expr.kind else {
        panic!("Expected enum variant constructor call");
    };
    assert_eq!(func.kind, HirExprKind::Global("Type::Int".to_string()));
    assert_eq!(args.len(), 2);
}

#[test]
fn test_lower_static_enum_unit_variant_value() {
    let module = parse_and_lower(
        "enum FsError:\n    InvalidArg\n    Transient(code: i32)\n\nfn test() -> FsError:\n    return FsError.InvalidArg\n",
    )
    .unwrap();

    let func = module.functions.iter().find(|f| f.name == "test").unwrap();
    let HirStmt::Return(Some(expr)) = &func.body[0] else {
        panic!("Expected return statement");
    };
    assert_eq!(expr.kind, HirExprKind::Global("FsError::InvalidArg".to_string()));
}

#[test]
fn test_trait_typed_method_result_enables_result_builtin() {
    let module = parse_and_lower(
        "trait Device:\n    fn write(data: [u8]) -> Result<bool, text>\n\nclass Store:\n    device: Device\n\nimpl Store:\n    fn failed(data: [u8]) -> bool:\n        val written = self.device.write(data)\n        written.is_err()\n",
    )
    .unwrap();

    let failed = module
        .functions
        .iter()
        .find(|function| function.name.ends_with("failed"))
        .unwrap();
    let body = format!("{:?}", failed.body);
    assert!(
        body.contains("rt_enum_check_discriminant") && !body.contains("method: \"is_err\""),
        "trait Result return must lower is_err as a builtin: {body}"
    );
}

#[test]
fn test_lower_ambiguous_global_field_chain_as_field_access() {
    let source = "fn bait(r: Replacement) -> text:\n    return r.new_text\n\nfn test(s: Holder) -> text:\n    return s.suggestion.new_text\n";
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");

    let mut lowerer = Lowerer::new();
    lowerer.set_global_struct_defs(Arc::new(HashMap::from([
        (
            "Holder".to_string(),
            vec![("suggestion".to_string(), Type::Simple("Suggestion".to_string()))],
        ),
        (
            "Replacement".to_string(),
            vec![
                ("new_text".to_string(), Type::Simple("text".to_string())),
                ("start".to_string(), Type::Simple("i64".to_string())),
                ("end".to_string(), Type::Simple("i64".to_string())),
                ("source".to_string(), Type::Simple("text".to_string())),
            ],
        ),
    ])));
    lowerer.set_duplicate_global_struct_defs(Arc::new(HashMap::from([(
        "Suggestion".to_string(),
        vec![
            vec![
                ("message".to_string(), Type::Simple("text".to_string())),
                ("confidence".to_string(), Type::Simple("FixConfidence".to_string())),
                ("new_text".to_string(), Type::Simple("text".to_string())),
            ],
            vec![("confidence".to_string(), Type::Simple("FixConfidence".to_string()))],
        ],
    )])));
    lowerer.set_lenient_types(true);
    lowerer.set_ambiguous_field_names(Arc::new(HashSet::from(["new_text".to_string()])));

    let lowered = lowerer.lower_module(&module).unwrap();
    let func = lowered.functions.iter().find(|func| func.name == "test").unwrap();
    if let HirStmt::Return(Some(expr)) = &func.body[0] {
        let HirExprKind::FieldAccess { field_index, .. } = &expr.kind else {
            panic!("Expected field access");
        };
        assert_eq!(*field_index, 2, "Suggestion.new_text must use the receiver layout");
        assert_eq!(expr.ty, TypeId::STRING);
    } else {
        panic!("Expected return statement");
    }
}

#[test]
fn test_lower_ambiguous_loop_element_field_access_with_global_array_type() {
    let source = "fn test(report: Report) -> text:\n    for s in report.suggestions:\n        return s.new_text\n    return ''\n";
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");

    let mut lowerer = Lowerer::new();
    lowerer.set_global_struct_defs(Arc::new(HashMap::from([
        (
            "Report".to_string(),
            vec![(
                "suggestions".to_string(),
                Type::Array {
                    element: Box::new(Type::Simple("Suggestion".to_string())),
                    size: None,
                },
            )],
        ),
        (
            "Suggestion".to_string(),
            vec![
                ("message".to_string(), Type::Simple("text".to_string())),
                ("location".to_string(), Type::Simple("SourceLocation".to_string())),
                ("new_text".to_string(), Type::Simple("text".to_string())),
                ("confidence".to_string(), Type::Simple("FixConfidence".to_string())),
            ],
        ),
        (
            "Replacement".to_string(),
            vec![("new_text".to_string(), Type::Simple("text".to_string()))],
        ),
    ])));
    lowerer.set_ambiguous_field_names(Arc::new(HashSet::from(["new_text".to_string()])));

    let lowered = lowerer.lower_module(&module).unwrap();
    let func = &lowered.functions[0];
    let HirStmt::For { body, .. } = &func.body[0] else {
        panic!("Expected for loop");
    };
    let HirStmt::Return(Some(expr)) = &body[0] else {
        panic!("Expected return inside loop");
    };
    assert!(matches!(expr.kind, HirExprKind::FieldAccess { .. }));
    assert_eq!(expr.ty, TypeId::STRING);
}

#[test]
fn test_lower_field_access_uses_unique_duplicate_struct_variant() {
    let source = "fn test(t: ObjTaker) -> i64:\n    return t.compiler_ctx.handle\n";
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");

    let mut lowerer = Lowerer::new();
    lowerer.set_global_struct_defs(Arc::new(HashMap::from([
        (
            "ObjTaker".to_string(),
            vec![("compiler_ctx".to_string(), Type::Simple("CompilerContext".to_string()))],
        ),
        (
            "CompilerContext".to_string(),
            vec![("alive".to_string(), Type::Simple("bool".to_string()))],
        ),
    ])));
    lowerer.set_duplicate_global_struct_defs(Arc::new(HashMap::from([(
        "CompilerContext".to_string(),
        vec![
            vec![("alive".to_string(), Type::Simple("bool".to_string()))],
            vec![("handle".to_string(), Type::Simple("i64".to_string()))],
        ],
    )])));
    lowerer.set_ambiguous_field_names(Arc::new(HashSet::new()));

    let lowered = lowerer.lower_module(&module).unwrap();
    let func = &lowered.functions[0];
    let HirStmt::Return(Some(expr)) = &func.body[0] else {
        panic!("Expected return statement");
    };
    assert!(matches!(expr.kind, HirExprKind::FieldAccess { .. }));
    assert_eq!(expr.ty, TypeId::I64);
}

#[test]
fn test_method_field_access_recovers_same_name_struct_layout_variant() {
    let source = "\
struct Span:
    start: i64
    end: i64

impl Span:
    fn end_value() -> i64:
        self.end

struct Span:
    start: i64
    end_pos: i64
";
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");

    let mut lowerer = Lowerer::new();
    lowerer.set_lenient_types(true);
    let lowered = lowerer.lower_module(&module).unwrap();
    let func = lowered
        .functions
        .iter()
        .find(|f| f.name == "Span.end_value")
        .expect("expected Span.end_value");
    let HirStmt::Expr(expr) = &func.body[0] else {
        panic!("Expected expression statement");
    };
    assert!(matches!(expr.kind, HirExprKind::FieldAccess { .. }));
    assert_eq!(expr.ty, TypeId::I64);
}

#[test]
fn test_lower_assignment() {
    let module = parse_and_lower("fn test() -> i64:\n    let mut x: i64 = 0\n    x = 42\n    return x\n").unwrap();

    let func = &module.functions[0];
    assert!(matches!(func.body[1], HirStmt::Assign { .. }));
}

#[test]
fn test_lower_expression_statement() {
    let module = parse_and_lower("fn test() -> i64:\n    1 + 2\n    return 0\n").unwrap();

    let func = &module.functions[0];
    assert!(matches!(func.body[0], HirStmt::Expr(_)));
}

#[test]
fn test_lower_erases_standalone_string_statement() {
    let module = parse_and_lower("fn test() -> i64:\n    \"\"\"doc only\"\"\"\n    return 0\n").unwrap();

    let func = &module.functions[0];
    assert_eq!(func.body.len(), 1);
    assert!(matches!(func.body[0], HirStmt::Return(_)));
}

#[test]
fn test_infer_type_from_binary_arithmetic() {
    let module = parse_and_lower("fn test() -> i64:\n    let x = 1 + 2\n    return x\n").unwrap();

    let func = &module.functions[0];
    // The type should be inferred from the left operand (i64)
    assert_eq!(func.locals[0].ty, TypeId::I64);
}

#[test]
fn test_lower_return_without_value() {
    let module = parse_and_lower("fn test() -> i64:\n    return\n").unwrap();

    let func = &module.functions[0];
    assert!(matches!(func.body[0], HirStmt::Return(None)));
}

/// B6 regression: HIR await must propagate the operand type, not hardcode I64.
/// Simple async is EAGER — await on a non-Future is the identity, so the
/// await expression type equals the operand type.
#[test]
fn test_await_expr_type_propagates_operand_type() {
    // `await 3.14` — operand is f64; HIR result must be F64, not I64.
    let module = parse_and_lower("fn test() -> i64:\n    let x = await 3.14\n    return 0\n").unwrap();

    let func = &module.functions[0];
    // The Let binding stores the await expression; check its inferred type.
    if let HirStmt::Let {
        ty,
        value: Some(ref expr),
        ..
    } = func.body[0]
    {
        assert_eq!(
            expr.ty,
            TypeId::F64,
            "await on f64 operand must produce F64 type, not I64 (B6 regression)"
        );
        // Also verify the let local got the right type
        assert_eq!(ty, TypeId::F64, "let binding type must match await result type");
        // Confirm the HIR kind is Await wrapping an f64 literal
        assert!(
            matches!(&expr.kind, HirExprKind::Await(inner) if inner.ty == TypeId::F64),
            "HirExprKind::Await inner must be F64"
        );
    } else {
        panic!("Expected Let statement with await expression");
    }
}

/// B6 regression: await on a string operand must yield STRING type (not I64).
#[test]
fn test_await_expr_string_type_propagates() {
    let module = parse_and_lower("fn test() -> i64:\n    let s = await \"hello\"\n    return 0\n").unwrap();

    let func = &module.functions[0];
    if let HirStmt::Let {
        value: Some(ref expr), ..
    } = func.body[0]
    {
        assert_eq!(
            expr.ty,
            TypeId::STRING,
            "await on string operand must produce STRING type (B6 regression)"
        );
    } else {
        panic!("Expected Let statement with await expression");
    }
}

/// Task #80 f-path repro (dap dap_handlers.spl / lsp verification.spl): a
/// module-qualified enum-variant reference `protocol.StopReason.DataBreakpoint`
/// must resolve via `global_enum_defs` (declared type evidence) even when a
/// global struct also declares a field named `DataBreakpoint` — the
/// most-fields-wins struct heuristic must not be consulted first.
#[test]
fn test_qualified_enum_variant_beats_struct_field_bait() {
    let source = "fn pick() -> i64:\n    val r = protocol.StopReason.DataBreakpoint\n    return 0\n";
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");

    let mut lowerer = Lowerer::new();
    lowerer.set_global_enum_defs(Arc::new(HashMap::from([(
        "StopReason".to_string(),
        vec![
            ("Step".to_string(), None),
            ("Breakpoint".to_string(), None),
            ("DataBreakpoint".to_string(), None),
        ],
    )])));
    // Bait: a struct with a same-named field and many fields (most-fields-wins winner).
    lowerer.set_global_struct_defs(Arc::new(HashMap::from([(
        "Decoy".to_string(),
        vec![
            ("DataBreakpoint".to_string(), Type::Simple("i64".to_string())),
            ("a".to_string(), Type::Simple("i64".to_string())),
            ("b".to_string(), Type::Simple("i64".to_string())),
            ("c".to_string(), Type::Simple("i64".to_string())),
        ],
    )])));
    let lowered = lowerer.lower_module(&module).expect("lowering must succeed");
    let func = lowered.functions.iter().find(|f| f.name == "pick").unwrap();
    let HirStmt::Let {
        value: Some(ref expr), ..
    } = func.body[0]
    else {
        panic!("Expected val binding");
    };
    assert_eq!(
        expr.kind,
        HirExprKind::Global("StopReason::DataBreakpoint".to_string()),
        "qualified enum variant must win over struct field-name bait"
    );
}

/// Task #80 f-path repro (gpu_helpers.spl cuda_available): a fn-scope
/// `use std.io.cuda_sffi` followed by `cuda_sffi.cuda_available()` must not
/// degrade into a field-access-on-ANY chain where `std.io` is resolved via the
/// most-fields-wins struct heuristic (bait: a global struct with field `io`).
#[test]
fn test_fn_scope_module_use_does_not_bait_field_guess() {
    let source = "fn cuda_available() -> bool:\n    use std.io.cuda_sffi\n    cuda_sffi.cuda_available()\n";
    let mut parser = Parser::new(source);
    let module = parser.parse().expect("parse failed");

    let mut lowerer = Lowerer::new();
    lowerer.set_global_struct_defs(Arc::new(HashMap::from([(
        "NvmeFreestandingControllerResources".to_string(),
        vec![
            ("io".to_string(), Type::Simple("i64".to_string())),
            ("admin".to_string(), Type::Simple("i64".to_string())),
            ("bar0".to_string(), Type::Simple("i64".to_string())),
        ],
    )])));
    match lowerer.lower_module(&module) {
        Ok(lowered) => {
            let func = lowered.functions.iter().find(|f| f.name == "cuda_available").unwrap();
            // The body must not contain a struct FieldAccess for the `std.io`
            // module path (index baked from the bait struct).
            fn expr_has(e: &HirExpr) -> bool {
                match &e.kind {
                    HirExprKind::FieldAccess { receiver, .. } => {
                        matches!(receiver.kind, HirExprKind::Global(ref g) if g == "std") || expr_has(receiver)
                    }
                    HirExprKind::MethodCall { receiver, args, .. } => expr_has(receiver) || args.iter().any(expr_has),
                    HirExprKind::Call { func, args } => expr_has(func) || args.iter().any(expr_has),
                    _ => false,
                }
            }
            let baited = func.body.iter().any(|s| match s {
                HirStmt::Expr(e) | HirStmt::Return(Some(e)) => expr_has(e),
                _ => false,
            });
            assert!(!baited, "module path `std.io` must not lower to a struct field access");
        }
        Err(e) => {
            let msg = format!("{e:?}");
            assert!(
                !(msg.contains("field") && msg.contains("'io'")),
                "lowering failed by mis-treating module path `std.io` as field access: {msg}"
            );
        }
    }
}

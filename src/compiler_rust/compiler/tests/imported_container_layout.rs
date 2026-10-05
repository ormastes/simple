use simple_compiler::hir::{Lowerer, LowerError, HirType, TypeId};
use simple_compiler::hir::{HirExprKind, HirStmt, HirModule};
use simple_compiler::module_resolver::ModuleResolver;
use tempfile::tempdir as create_test_project;
use simple_parser::{Parser, Type};
use std::{collections::HashMap, fs, sync::Arc};

fn lower_selective(model: &str, expression: &str) -> Result<HirModule, LowerError> {
    lower_selective_with_body(model, expression, true)
}

fn lower_selective_with_body(model: &str, expression: &str, expect_field: bool) -> Result<HirModule, LowerError> {
    let dir = create_test_project().unwrap();
    let src = dir.path().join("src");
    fs::create_dir_all(&src).unwrap();
    let declaration = src.join("model.spl");
    fs::write(&declaration, model).unwrap();
    let caller = src.join("main.spl");
    let source = format!("use model.{{Object}}\nfn read_name(value: Object) -> text:\n    {expression}\n");
    fs::write(&caller, &source).unwrap();
    let ast = Parser::new(&source).parse().unwrap();
    let mut lowerer = Lowerer::with_module_resolver(
        ModuleResolver::new(dir.path().to_path_buf(), src), caller);
    // The real closure has three ElfSymbol owners whose `name` offsets differ.
    // No consensus/global spelling can stand in for the selected declaration.
    let wrong = vec![("name".into(), Type::Simple("text".into()))];
    let right = vec![("tag".into(), Type::Simple("i64".into())),
                     ("name".into(), Type::Simple("text".into()))];
    lowerer.set_global_struct_defs(Arc::new(HashMap::from([
        ("other__Entry".into(), wrong.clone()), ("model__Entry".into(), right.clone())])));
    lowerer.set_duplicate_global_struct_defs(Arc::new(HashMap::from([
        ("Entry".into(), vec![wrong, right])])));
    lowerer.set_unique_global_struct_owners(Arc::new(HashMap::new()));
    lowerer.set_struct_module_owners(Arc::new(HashMap::from([(declaration.clone(), "model".into())])));
    let lowered = lowerer.lower_module(&ast)?;
    let function = lowered.functions.iter().find(|f| f.name == "read_name").unwrap();
    let Some(HirStmt::Expr(value)) = function.body.last() else { panic!("expected real field-access body") };
    assert_eq!(value.ty, TypeId::STRING);
    if expect_field {
        assert!(matches!(value.kind, HirExprKind::FieldAccess { field_index: 1, .. }), "must use declaration slot 1: {value:?}");
    }
    assert!(lowered.types.lookup("model__Entry").is_some(), "declaring-module identity must be retained");
    Ok(lowered)
}

const ENTRY: &str = "struct Entry:\n    tag: i64\n    name: text\n";

#[test]
fn imported_container_array_preserves_declaration_layout() {
    lower_selective(&format!("{ENTRY}struct Object:\n    items: [Entry]\n"), "value.items[0].name").unwrap();
}

#[test]
fn imported_container_nested_array_preserves_declaration_layout() {
    lower_selective(&format!("{ENTRY}struct Object:\n    items: [[Entry]]\n"), "value.items[0][0].name").unwrap();
}

#[test]
fn imported_container_dictionary_preserves_declaration_layout() {
    lower_selective(&format!("{ENTRY}struct Object:\n    items: Dict<text, Entry>\n"), "value.items[\"first\"].name").unwrap();
}

#[test]
fn imported_container_optional_payload_completes_nested_array() {
    let model = format!("{ENTRY}struct Object:\n    selected: [Entry]?\n");
    let lowered = lower_selective_with_body(&model, "\"unused optional payload\"", false).unwrap();
    let object = lowered.types.lookup("Object").unwrap();
    let HirType::Struct { fields, .. } = lowered.types.get(object).unwrap() else { panic!("Object") };
    let HirType::Enum { variants, .. } = lowered.types.get(fields[0].1).unwrap() else { panic!("Option") };
    let array = variants.iter().find(|(name, _)| name == "Some").unwrap().1.as_ref().unwrap()[0];
    let HirType::Array { element, .. } = lowered.types.get(array).unwrap() else { panic!("array") };
    let HirType::Struct { fields, .. } = lowered.types.get(*element).unwrap() else { panic!("Entry") };
    assert_eq!(fields[1], ("name".into(), TypeId::STRING));
}

#[test]
fn imported_container_recursive_graph_terminates_with_complete_layout() {
    let model = "struct Entry:\n    children: [Entry]\n    name: text\nstruct Object:\n    items: [Entry]\n";
    lower_selective(model, "value.items[0].children[0].name").unwrap();
}

#[test]
fn imported_container_unknown_field_still_rejected() {
    let err = lower_selective(&format!("{ENTRY}struct Object:\n    items: [Entry]\n"), "value.items[0].misspelled").err().expect("unknown field must fail");
    assert!(matches!(err, LowerError::CannotInferFieldType { field, .. } if field == "misspelled"));
}

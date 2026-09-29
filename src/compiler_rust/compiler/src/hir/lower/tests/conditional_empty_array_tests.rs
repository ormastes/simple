use super::parse_and_lower;
use crate::hir::types::{HirExprKind, HirStmt, HirType, TypeId};

#[test]
fn conditional_empty_array_preserves_symbol_keys_in_both_orders() {
    for expression in ["if empty: [] else: symbols.keys()", "if empty: symbols.keys() else: []"] {
        let source = format!("struct SymbolId:\n    id: i64\nfn probe(symbols: Dict<SymbolId, i64>, empty: bool) -> i64:\n    val keys = {expression}\n    for key in keys:\n        val observed = key.id\n    0\n");
        let module = parse_and_lower(&source).unwrap();
        let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
        let keys = function.locals.iter().find(|l| l.name == "keys").unwrap();
        let Some(HirType::Array { element, size }) = module.types.get(keys.ty) else { panic!("keys is not an array") };
        assert!(matches!(module.types.get(*element), Some(HirType::Struct { name, .. }) if name == "SymbolId"), "{expression}: {:?}", module.types.get(*element));
        assert_eq!(*size, None);
        let key = function.locals.iter().find(|l| l.name == "key").unwrap();
        assert_eq!(key.ty, *element);
        let HirStmt::Let { value: Some(value), .. } = &function.body[0] else { panic!("expected keys initializer") };
        let HirExprKind::If { then_branch, else_branch: Some(other), .. } = &value.kind else { panic!("expected conditional") };
        for branch in [then_branch, other] {
            let Some(HirType::Array { element: branch_element, .. }) = module.types.get(branch.ty) else { panic!("expected array branch") };
            assert_eq!(branch_element, element);
        }
    }
}

#[test]
fn conditional_empty_array_does_not_retype_populated_or_unrelated_aggregates() {
    for (expression, expected) in [
        ("if flag: [1] else: words", TypeId::I64),
        ("if flag: [] else: (1, 2)", TypeId::I32),
        ("if flag: [] else: []", TypeId::I32),
        ("if flag: [\"typed\"; 0] else: [1]", TypeId::STRING),
        ("if flag: [] else: [\"typed\"; 0]", TypeId::STRING),
    ] {
        let source = format!("fn probe(flag: bool, words: [text]) -> i64:\n    val items = {expression}\n    0\n");
        let module = parse_and_lower(&source).unwrap();
        let items = module.functions[0].locals.iter().find(|l| l.name == "items").unwrap();
        assert!(matches!(module.types.get(items.ty), Some(HirType::Array { element, .. }) if *element == expected), "{expression}");
    }
}

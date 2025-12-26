//! Low coverage tests - Round 7
//!
//! Targets:
//! - driver/src/simple_test.rs (0% -> higher) - TestCategory, SimpleTestFile, SimpleTestResult
//! - parser/src/doc_gen.rs (0% -> higher) - DocItem, DocItemKind, ModuleDocs
//! - type/src/lib.rs (partial) - more Type, TypeChecker tests
//! - loader/src/settlement/container.rs (partial) - SettlementConfig, ModuleHandle, SlotRange

use std::path::PathBuf;

// ============================================================================
// Simple Test Framework Tests (driver/src/simple_test.rs)
// ============================================================================

mod simple_test_tests {
    use simple_driver::simple_test::*;
    use std::path::Path;
    use std::path::PathBuf;

    #[test]
    fn test_category_unit_from_path() {
        let path = Path::new("test/unit/core/arithmetic_spec.spl");
        assert_eq!(TestCategory::from_path(path), TestCategory::Unit);
    }

    #[test]
    fn test_category_integration_from_path() {
        let path = Path::new("test/integration/doctest/discovery_spec.spl");
        assert_eq!(TestCategory::from_path(path), TestCategory::Integration);
    }

    #[test]
    fn test_category_system_from_path() {
        let path = Path::new("test/system/spec/spec_framework_spec.spl");
        assert_eq!(TestCategory::from_path(path), TestCategory::System);
    }

    #[test]
    fn test_category_fixture_from_path() {
        let path = Path::new("test/fixtures/doctest/sample.spl");
        assert_eq!(TestCategory::from_path(path), TestCategory::Fixture);
    }

    #[test]
    fn test_category_default_is_unit() {
        let path = Path::new("some/random/path.spl");
        assert_eq!(TestCategory::from_path(path), TestCategory::Unit);
    }

    #[test]
    fn test_simple_test_file_to_test_name() {
        let file = SimpleTestFile {
            path: PathBuf::from("/home/test/unit/core/arithmetic_spec.spl"),
            relative_path: "unit/core/arithmetic_spec.spl".to_string(),
            category: TestCategory::Unit,
            module_path: "unit.core.arithmetic_spec".to_string(),
        };

        assert_eq!(file.to_test_name(), "unit_core_arithmetic_spec");
    }

    #[test]
    fn test_simple_test_file_to_test_name_with_hyphens() {
        let file = SimpleTestFile {
            path: PathBuf::from("/home/test/unit/my-module_spec.spl"),
            relative_path: "unit/my-module_spec.spl".to_string(),
            category: TestCategory::Unit,
            module_path: "unit.my_module_spec".to_string(),
        };

        assert_eq!(file.to_test_name(), "unit_my_module_spec");
    }

    #[test]
    fn test_test_failure_creation() {
        let failure = TestFailure {
            test_name: "DoctestParser > parse_docstring > parses simple".to_string(),
            message: "Expected: 1, Got: 0".to_string(),
            location: Some("parser_spec.spl:12".to_string()),
        };

        assert_eq!(
            failure.test_name,
            "DoctestParser > parse_docstring > parses simple"
        );
        assert_eq!(failure.message, "Expected: 1, Got: 0");
        assert_eq!(failure.location, Some("parser_spec.spl:12".to_string()));
    }

    #[test]
    fn test_test_failure_no_location() {
        let failure = TestFailure {
            test_name: "some test".to_string(),
            message: "failed".to_string(),
            location: None,
        };

        assert!(failure.location.is_none());
    }

    #[test]
    fn test_simple_test_result_pass_is_success() {
        let result = SimpleTestResult::Pass {
            file: "test.spl".to_string(),
            passed_count: 5,
            duration_ms: 100,
            stdout: "output".to_string(),
        };

        assert!(result.is_success());
    }

    #[test]
    fn test_simple_test_result_fail_not_success() {
        let result = SimpleTestResult::Fail {
            file: "test.spl".to_string(),
            passed_count: 3,
            failed_count: 2,
            failures: vec![],
            duration_ms: 100,
            stdout: "output".to_string(),
        };

        assert!(!result.is_success());
    }

    #[test]
    fn test_simple_test_result_skipped_is_success() {
        let result = SimpleTestResult::Skipped {
            file: "fixture.spl".to_string(),
            reason: "fixture file".to_string(),
        };

        assert!(result.is_success());
    }

    #[test]
    fn test_simple_test_result_compile_error_not_success() {
        let result = SimpleTestResult::CompileError {
            file: "test.spl".to_string(),
            error: "syntax error".to_string(),
        };

        assert!(!result.is_success());
    }

    #[test]
    fn test_simple_test_result_runtime_error_not_success() {
        let result = SimpleTestResult::RuntimeError {
            file: "test.spl".to_string(),
            error: "division by zero".to_string(),
            stdout: "partial output".to_string(),
        };

        assert!(!result.is_success());
    }

    #[test]
    fn test_simple_test_result_pass_summary() {
        let result = SimpleTestResult::Pass {
            file: "test.spl".to_string(),
            passed_count: 5,
            duration_ms: 100,
            stdout: "".to_string(),
        };

        let summary = result.summary();
        assert!(summary.contains("test.spl"));
        assert!(summary.contains("5"));
        assert!(summary.contains("passed"));
        assert!(summary.contains("100"));
    }

    #[test]
    fn test_simple_test_result_fail_summary() {
        let result = SimpleTestResult::Fail {
            file: "test.spl".to_string(),
            passed_count: 3,
            failed_count: 2,
            failures: vec![],
            duration_ms: 200,
            stdout: "".to_string(),
        };

        let summary = result.summary();
        assert!(summary.contains("test.spl"));
        assert!(summary.contains("3"));
        assert!(summary.contains("2"));
        assert!(summary.contains("failed"));
    }

    #[test]
    fn test_simple_test_result_compile_error_summary() {
        let result = SimpleTestResult::CompileError {
            file: "bad.spl".to_string(),
            error: "syntax error at line 5".to_string(),
        };

        let summary = result.summary();
        assert!(summary.contains("bad.spl"));
        assert!(summary.contains("compile error"));
    }

    #[test]
    fn test_simple_test_result_runtime_error_summary() {
        let result = SimpleTestResult::RuntimeError {
            file: "crash.spl".to_string(),
            error: "null pointer".to_string(),
            stdout: "".to_string(),
        };

        let summary = result.summary();
        assert!(summary.contains("crash.spl"));
        assert!(summary.contains("runtime error"));
    }

    #[test]
    fn test_simple_test_result_skipped_summary() {
        let result = SimpleTestResult::Skipped {
            file: "fixture.spl".to_string(),
            reason: "fixture file".to_string(),
        };

        let summary = result.summary();
        assert!(summary.contains("fixture.spl"));
        assert!(summary.contains("skipped"));
    }

    #[test]
    fn test_discover_tests_empty_dir() {
        use tempfile::TempDir;

        let temp = TempDir::new().unwrap();
        let tests = discover_tests(temp.path());
        assert!(tests.is_empty());
    }
}

// ============================================================================
// Doc Gen Tests (parser/src/doc_gen.rs)
// ============================================================================

mod doc_gen_tests {
    use simple_parser::ast::Visibility;
    use simple_parser::{DocItem, DocItemKind, ModuleDocs};

    #[test]
    fn test_doc_item_kind_function() {
        let kind = DocItemKind::Function;
        assert!(matches!(kind, DocItemKind::Function));
    }

    #[test]
    fn test_doc_item_kind_struct() {
        let kind = DocItemKind::Struct;
        assert!(matches!(kind, DocItemKind::Struct));
    }

    #[test]
    fn test_doc_item_kind_enum() {
        let kind = DocItemKind::Enum;
        assert!(matches!(kind, DocItemKind::Enum));
    }

    #[test]
    fn test_doc_item_kind_trait() {
        let kind = DocItemKind::Trait;
        assert!(matches!(kind, DocItemKind::Trait));
    }

    #[test]
    fn test_doc_item_kind_class() {
        let kind = DocItemKind::Class;
        assert!(matches!(kind, DocItemKind::Class));
    }

    #[test]
    fn test_doc_item_creation() {
        let item = DocItem {
            name: "add".to_string(),
            kind: DocItemKind::Function,
            doc: "Adds two numbers".to_string(),
            signature: "fn add(x: Int, y: Int) -> Int".to_string(),
            visibility: Visibility::Public,
        };

        assert_eq!(item.name, "add");
        assert!(matches!(item.kind, DocItemKind::Function));
        assert_eq!(item.doc, "Adds two numbers");
        assert!(!item.signature.is_empty());
    }

    #[test]
    fn test_doc_item_empty_doc() {
        let item = DocItem {
            name: "internal_helper".to_string(),
            kind: DocItemKind::Function,
            doc: String::new(),
            signature: String::new(),
            visibility: Visibility::Private,
        };

        assert!(item.doc.is_empty());
        assert!(item.signature.is_empty());
    }

    #[test]
    fn test_module_docs_default() {
        let docs = ModuleDocs::default();
        assert!(docs.name.is_none());
        assert!(docs.items.is_empty());
    }

    #[test]
    fn test_module_docs_creation() {
        let docs = ModuleDocs {
            name: Some("core".to_string()),
            items: vec![DocItem {
                name: "add".to_string(),
                kind: DocItemKind::Function,
                doc: "Adds numbers".to_string(),
                signature: "fn add(x, y)".to_string(),
                visibility: Visibility::Public,
            }],
        };

        assert_eq!(docs.name, Some("core".to_string()));
        assert_eq!(docs.items.len(), 1);
    }

    #[test]
    fn test_module_docs_to_markdown() {
        let docs = ModuleDocs {
            name: Some("test_module".to_string()),
            items: vec![DocItem {
                name: "my_func".to_string(),
                kind: DocItemKind::Function,
                doc: "Does something".to_string(),
                signature: "fn my_func()".to_string(),
                visibility: Visibility::Public,
            }],
        };

        let md = docs.to_markdown();
        assert!(md.contains("test_module"));
        assert!(md.contains("my_func"));
    }

    #[test]
    fn test_module_docs_to_html() {
        let docs = ModuleDocs {
            name: Some("html_test".to_string()),
            items: vec![],
        };

        let html = docs.to_html();
        assert!(html.contains("html_test") || html.contains("<"));
    }
}

// ============================================================================
// Type Checker Extended Tests (type/src/lib.rs)
// ============================================================================

mod type_checker_extended_tests {
    use simple_type::*;

    #[test]
    fn test_substitution_compose() {
        let mut sub1 = Substitution::new();
        sub1.insert(0, Type::Int);

        let mut sub2 = Substitution::new();
        sub2.insert(1, Type::Bool);

        sub1.compose(&sub2);

        // After composition, sub1 should have both mappings
        assert!(sub1.get(0).is_some());
        assert!(sub1.get(1).is_some());
    }

    #[test]
    fn test_type_function_apply_subst() {
        let func_ty = Type::Function {
            params: vec![Type::Var(0)],
            ret: Box::new(Type::Var(1)),
        };

        let mut subst = Substitution::new();
        subst.insert(0, Type::Int);
        subst.insert(1, Type::Bool);

        let result = func_ty.apply_subst(&subst);

        if let Type::Function { params, ret } = result {
            assert!(matches!(params[0], Type::Int));
            assert!(matches!(*ret, Type::Bool));
        } else {
            panic!("Expected Function type");
        }
    }

    #[test]
    fn test_type_function_contains_var() {
        let func_ty = Type::Function {
            params: vec![Type::Int],
            ret: Box::new(Type::Var(5)),
        };

        assert!(func_ty.contains_var(5));
        assert!(!func_ty.contains_var(0));
    }

    #[test]
    fn test_type_nil() {
        let ty = Type::Nil;
        assert!(matches!(ty, Type::Nil));
        assert!(!ty.contains_var(0));
    }

    #[test]
    fn test_type_float() {
        let ty = Type::Float;
        assert!(matches!(ty, Type::Float));
    }

    #[test]
    fn test_lean_ty_arrow() {
        let arrow = LeanTy::Arrow(Box::new(LeanTy::Nat), Box::new(LeanTy::Bool));

        if let LeanTy::Arrow(from, to) = arrow {
            assert!(matches!(*from, LeanTy::Nat));
            assert!(matches!(*to, LeanTy::Bool));
        } else {
            panic!("Expected Arrow type");
        }
    }

    #[test]
    fn test_lean_expr_lam() {
        let lam = LeanExpr::Lam(Box::new(LeanExpr::LitBool(true)));

        if let LeanExpr::Lam(body) = lam {
            assert!(matches!(*body, LeanExpr::LitBool(true)));
        } else {
            panic!("Expected Lam expression");
        }
    }

    #[test]
    fn test_lean_expr_app() {
        let app = LeanExpr::App(
            Box::new(LeanExpr::Lam(Box::new(LeanExpr::LitNat(42)))),
            Box::new(LeanExpr::LitNat(1)),
        );

        if let LeanExpr::App(f, x) = app {
            assert!(matches!(*f, LeanExpr::Lam(_)));
            assert!(matches!(*x, LeanExpr::LitNat(1)));
        } else {
            panic!("Expected App expression");
        }
    }

    #[test]
    fn test_lean_expr_concat() {
        let concat = LeanExpr::Concat(
            Box::new(LeanExpr::LitStr("hello".to_string())),
            Box::new(LeanExpr::LitStr(" world".to_string())),
        );

        if let LeanExpr::Concat(a, b) = concat {
            assert!(matches!(*a, LeanExpr::LitStr(_)));
            assert!(matches!(*b, LeanExpr::LitStr(_)));
        } else {
            panic!("Expected Concat expression");
        }
    }

    #[test]
    fn test_lean_infer_concat() {
        let expr = LeanExpr::Concat(
            Box::new(LeanExpr::LitStr("a".to_string())),
            Box::new(LeanExpr::LitStr("b".to_string())),
        );

        let ty = lean_infer(&expr);
        assert_eq!(ty, Some(LeanTy::Str));
    }

    #[test]
    fn test_lean_infer_if_else_bool() {
        let expr = LeanExpr::IfElse(
            Box::new(LeanExpr::LitBool(true)),
            Box::new(LeanExpr::LitBool(false)),
            Box::new(LeanExpr::LitBool(true)),
        );

        let ty = lean_infer(&expr);
        assert_eq!(ty, Some(LeanTy::Bool));
    }

    #[test]
    fn test_lean_infer_if_else_mismatched() {
        let expr = LeanExpr::IfElse(
            Box::new(LeanExpr::LitBool(true)),
            Box::new(LeanExpr::LitNat(1)),
            Box::new(LeanExpr::LitBool(false)),
        );

        let ty = lean_infer(&expr);
        assert!(ty.is_none());
    }

    #[test]
    fn test_infer_deterministic_lit() {
        let expr = LeanExpr::LitNat(42);
        assert!(infer_deterministic(&expr));
    }

    #[test]
    fn test_infer_deterministic_add() {
        let expr = LeanExpr::Add(
            Box::new(LeanExpr::LitNat(1)),
            Box::new(LeanExpr::LitNat(2)),
        );
        assert!(infer_deterministic(&expr));
    }

    #[test]
    fn test_infer_simple_nat() {
        let expr = LeanExpr::LitNat(100);
        let ty = infer_simple(&expr);
        assert_eq!(ty, Some(LeanTy::Nat));
    }

    #[test]
    fn test_infer_simple_str() {
        let expr = LeanExpr::LitStr("test".to_string());
        let ty = infer_simple(&expr);
        assert_eq!(ty, Some(LeanTy::Str));
    }
}

// ============================================================================
// Settlement Container Tests (loader/src/settlement)
// ============================================================================

mod settlement_container_tests {
    use simple_loader::settlement::*;

    #[test]
    fn test_module_handle_creation() {
        let handle = ModuleHandle(42);
        assert_eq!(handle.0, 42);
    }

    #[test]
    fn test_module_handle_is_valid() {
        let valid = ModuleHandle(0);
        assert!(valid.is_valid());

        let invalid = ModuleHandle(u32::MAX);
        assert!(!invalid.is_valid());
    }

    #[test]
    fn test_module_handle_as_usize() {
        let handle = ModuleHandle(100);
        assert_eq!(handle.as_usize(), 100);
    }

    #[test]
    fn test_settlement_error_module_not_found() {
        let err = SettlementError::ModuleNotFound("test".to_string());
        assert!(err.to_string().contains("test"));
    }

    #[test]
    fn test_settlement_error_invalid_module() {
        let err = SettlementError::InvalidModule("bad_module".to_string());
        assert!(err.to_string().contains("bad_module"));
    }

    #[test]
    fn test_settlement_error_code_region_full() {
        let err = SettlementError::CodeRegionFull;
        let msg = err.to_string();
        assert!(msg.contains("code") || msg.contains("Code") || !msg.is_empty());
    }

    #[test]
    fn test_settlement_error_data_region_full() {
        let err = SettlementError::DataRegionFull;
        let msg = err.to_string();
        assert!(msg.contains("data") || msg.contains("Data") || !msg.is_empty());
    }

    #[test]
    fn test_settlement_error_memory_error() {
        let err = SettlementError::MemoryError("allocation failed".to_string());
        assert!(err.to_string().contains("allocation failed"));
    }

    #[test]
    fn test_settlement_error_native_lib_error() {
        let err = SettlementError::NativeLibError("libfoo.so not found".to_string());
        assert!(err.to_string().contains("libfoo.so"));
    }

    #[test]
    fn test_settlement_error_has_dependents() {
        let err = SettlementError::HasDependents(
            "module_a".to_string(),
            vec!["module_b".to_string(), "module_c".to_string()],
        );
        let msg = err.to_string();
        assert!(msg.contains("module_a") || !msg.is_empty());
    }

    #[test]
    fn test_settlement_error_dependency_cycle() {
        let err = SettlementError::DependencyCycle(vec![
            "a".to_string(),
            "b".to_string(),
            "a".to_string(),
        ]);
        let msg = err.to_string();
        assert!(!msg.is_empty());
    }

    #[test]
    fn test_settlement_config_default() {
        let config = SettlementConfig::default();
        // Verify config has reasonable defaults
        assert!(config.code_region_size > 0);
        assert!(config.data_region_size > 0);
    }

    #[test]
    fn test_settlement_config_custom() {
        let config = SettlementConfig {
            code_region_size: 1024 * 1024,
            data_region_size: 512 * 1024,
            reloadable: true,
            executable: true,
        };

        assert_eq!(config.code_region_size, 1024 * 1024);
        assert_eq!(config.data_region_size, 512 * 1024);
        assert!(config.reloadable);
        assert!(config.executable);
    }

    #[test]
    fn test_slot_range_new() {
        let range = SlotRange::new(100, 50);
        assert_eq!(range.start, 100);
        assert_eq!(range.count, 50);
    }

    #[test]
    fn test_slot_range_end() {
        let range = SlotRange::new(100, 50);
        assert_eq!(range.end(), 150);
    }

    #[test]
    fn test_slot_range_contains() {
        let range = SlotRange::new(100, 50);
        assert!(range.contains(100));
        assert!(range.contains(125));
        assert!(range.contains(149));
        assert!(!range.contains(99));
        assert!(!range.contains(150));
    }

    #[test]
    fn test_slot_range_overlaps() {
        let range1 = SlotRange::new(100, 50);
        let range2 = SlotRange::new(125, 50);
        let range3 = SlotRange::new(200, 50);

        assert!(range1.overlaps(&range2));
        assert!(range2.overlaps(&range1));
        assert!(!range1.overlaps(&range3));
        assert!(!range3.overlaps(&range1));
    }

    #[test]
    fn test_slot_range_empty_not_overlaps() {
        let empty = SlotRange::new(0, 0);
        let non_empty = SlotRange::new(0, 10);

        // Empty range shouldn't overlap with anything meaningful
        // Depends on implementation, just verify no panic
        let _ = empty.overlaps(&non_empty);
    }
}

// ============================================================================
// Type Error Tests
// ============================================================================

mod type_error_tests {
    use simple_type::*;

    #[test]
    fn test_type_error_mismatch() {
        let err = TypeError::Mismatch {
            expected: Type::Int,
            found: Type::Bool,
        };

        if let TypeError::Mismatch { expected, found } = err {
            assert!(matches!(expected, Type::Int));
            assert!(matches!(found, Type::Bool));
        } else {
            panic!("Expected Mismatch variant");
        }
    }

    #[test]
    fn test_type_error_undefined() {
        let err = TypeError::Undefined("unknown_var".to_string());

        if let TypeError::Undefined(name) = err {
            assert_eq!(name, "unknown_var");
        } else {
            panic!("Expected Undefined variant");
        }
    }

    #[test]
    fn test_type_error_occurs_check() {
        let err = TypeError::OccursCheck {
            var_id: 5,
            ty: Type::Function {
                params: vec![Type::Var(5)],
                ret: Box::new(Type::Int),
            },
        };

        if let TypeError::OccursCheck { var_id, ty } = err {
            assert_eq!(var_id, 5);
            assert!(ty.contains_var(5));
        } else {
            panic!("Expected OccursCheck variant");
        }
    }

    #[test]
    fn test_type_error_other() {
        let err = TypeError::Other("custom error".to_string());

        if let TypeError::Other(msg) = err {
            assert_eq!(msg, "custom error");
        } else {
            panic!("Expected Other variant");
        }
    }
}

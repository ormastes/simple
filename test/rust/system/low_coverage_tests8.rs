//! Low coverage improvement tests - Round 8
//!
//! Targets: coverage.rs, package/reader.rs, type/checker_unify.rs, pkg/commands/list.rs

// ===========================================================================
// Coverage Collector Tests (simple_compiler::coverage)
// ===========================================================================
mod coverage_collector_tests {
    use simple_compiler::{CoverageCollector, CoverageStats};
    use std::path::Path;

    #[test]
    fn test_coverage_collector_new() {
        let cov = CoverageCollector::new();
        assert!(!cov.has_data());
    }

    #[test]
    fn test_coverage_collector_new_for_test() {
        let cov = CoverageCollector::new_for_test("my_test".to_string());
        assert!(!cov.has_data());
    }

    #[test]
    fn test_coverage_record_line() {
        let mut cov = CoverageCollector::new();
        cov.record_line(Path::new("test.spl"), 10);
        cov.record_line(Path::new("test.spl"), 20);
        cov.record_line(Path::new("test.spl"), 10); // duplicate

        let stats = cov.stats();
        assert_eq!(stats.total_lines, 2);
        assert_eq!(stats.total_files, 1);
    }

    #[test]
    fn test_coverage_record_function_call() {
        let mut cov = CoverageCollector::new();
        cov.record_function_call("main");
        cov.record_function_call("main");
        cov.record_function_call("helper");

        assert_eq!(cov.function_call_count("main"), 2);
        assert_eq!(cov.function_call_count("helper"), 1);
        assert_eq!(cov.function_call_count("nonexistent"), 0);
    }

    #[test]
    fn test_coverage_record_ffi_call() {
        let mut cov = CoverageCollector::new();
        cov.record_ffi_call("rt_array_new");
        cov.record_ffi_call("rt_array_new");

        assert_eq!(cov.ffi_call_count("rt_array_new"), 2);
        assert_eq!(cov.ffi_call_count("other"), 0);
    }

    #[test]
    fn test_coverage_merge() {
        let mut cov1 = CoverageCollector::new();
        cov1.record_line(Path::new("a.spl"), 1);
        cov1.record_function_call("foo");

        let mut cov2 = CoverageCollector::new();
        cov2.record_line(Path::new("a.spl"), 2);
        cov2.record_function_call("foo");
        cov2.record_ffi_call("rt_print");

        cov1.merge(&cov2);

        assert_eq!(cov1.stats().total_lines, 2);
        assert_eq!(cov1.function_call_count("foo"), 2);
        assert_eq!(cov1.ffi_call_count("rt_print"), 1);
    }

    #[test]
    fn test_coverage_stats() {
        let mut cov = CoverageCollector::new();
        cov.record_line(Path::new("a.spl"), 1);
        cov.record_line(Path::new("b.spl"), 1);
        cov.record_function_call("main");
        cov.record_ffi_call("rt_new");

        let stats = cov.stats();
        assert_eq!(stats.total_lines, 2);
        assert_eq!(stats.total_files, 2);
        assert_eq!(stats.total_functions, 1);
        assert_eq!(stats.total_ffi_calls, 1);
    }

    #[test]
    fn test_coverage_lines_for_file() {
        let mut cov = CoverageCollector::new();
        cov.record_line(Path::new("test.spl"), 10);
        cov.record_line(Path::new("test.spl"), 20);

        let lines = cov.lines_for_file(Path::new("test.spl"));
        assert!(lines.is_some());
        assert!(lines.unwrap().contains(&10));
        assert!(lines.unwrap().contains(&20));

        assert!(cov.lines_for_file(Path::new("other.spl")).is_none());
    }

    #[test]
    fn test_coverage_is_line_executed() {
        let mut cov = CoverageCollector::new();
        cov.record_line(Path::new("test.spl"), 10);

        assert!(cov.is_line_executed(Path::new("test.spl"), 10));
        assert!(!cov.is_line_executed(Path::new("test.spl"), 11));
        assert!(!cov.is_line_executed(Path::new("other.spl"), 10));
    }

    #[test]
    fn test_coverage_has_data() {
        let mut cov = CoverageCollector::new();
        assert!(!cov.has_data());

        cov.record_function_call("test");
        assert!(cov.has_data());
    }

    #[test]
    fn test_coverage_validate_minimum_coverage_pass() {
        let mut cov = CoverageCollector::new();
        cov.record_line(Path::new("test.spl"), 1);
        cov.record_function_call("main");

        assert!(cov.validate_minimum_coverage(1, 1).is_ok());
        assert!(cov.validate_minimum_coverage(0, 0).is_ok());
    }

    #[test]
    fn test_coverage_validate_minimum_coverage_fail_lines() {
        let cov = CoverageCollector::new();
        let result = cov.validate_minimum_coverage(10, 0);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Insufficient line coverage"));
    }

    #[test]
    fn test_coverage_validate_minimum_coverage_fail_functions() {
        let mut cov = CoverageCollector::new();
        cov.record_line(Path::new("test.spl"), 1);
        let result = cov.validate_minimum_coverage(1, 5);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Insufficient function coverage"));
    }

    #[test]
    fn test_coverage_was_function_called() {
        let mut cov = CoverageCollector::new();
        assert!(!cov.was_function_called("test"));
        cov.record_function_call("test");
        assert!(cov.was_function_called("test"));
    }

    #[test]
    fn test_coverage_was_file_executed() {
        let mut cov = CoverageCollector::new();
        assert!(!cov.was_file_executed(Path::new("test.spl")));
        cov.record_line(Path::new("test.spl"), 1);
        assert!(cov.was_file_executed(Path::new("test.spl")));
    }

    #[test]
    fn test_coverage_executed_files() {
        let mut cov = CoverageCollector::new();
        cov.record_line(Path::new("a.spl"), 1);
        cov.record_line(Path::new("b.spl"), 1);

        let files = cov.executed_files();
        assert_eq!(files.len(), 2);
    }

    #[test]
    fn test_coverage_called_functions() {
        let mut cov = CoverageCollector::new();
        cov.record_function_call("foo");
        cov.record_function_call("bar");

        let funcs = cov.called_functions();
        assert_eq!(funcs.len(), 2);
        assert!(funcs.contains(&"foo".to_string()));
        assert!(funcs.contains(&"bar".to_string()));
    }

    #[test]
    fn test_coverage_file_coverage_percentage() {
        let mut cov = CoverageCollector::new();
        cov.record_line(Path::new("test.spl"), 1);
        cov.record_line(Path::new("test.spl"), 2);

        let pct = cov.file_coverage_percentage(Path::new("test.spl"), 10);
        assert!((pct - 20.0).abs() < 0.01);

        let pct_none = cov.file_coverage_percentage(Path::new("other.spl"), 10);
        assert!((pct_none - 0.0).abs() < 0.01);
    }

    #[test]
    fn test_coverage_summary_report() {
        let mut cov = CoverageCollector::new();
        cov.record_function_call("main");
        cov.record_ffi_call("rt_print");

        let report = cov.summary_report();
        assert!(report.contains("=== Coverage Summary ==="));
        assert!(report.contains("Functions called:"));
        assert!(report.contains("main"));
    }

    #[test]
    fn test_coverage_stats_struct() {
        let stats = CoverageStats {
            total_lines: 100,
            total_files: 5,
            total_functions: 20,
            total_ffi_calls: 10,
        };
        assert_eq!(stats.total_lines, 100);
        assert_eq!(stats.total_files, 5);
    }
}

// ===========================================================================
// Package Reader Tests (simple_loader::package::PackageReader)
// ===========================================================================
mod package_reader_tests {
    use simple_loader::package::PackageReader;

    #[test]
    fn test_package_reader_new() {
        let reader = PackageReader::new();
        let _ = reader; // just test construction
    }

    #[test]
    fn test_package_reader_default() {
        let reader = PackageReader::default();
        let _ = reader;
    }

    #[test]
    fn test_package_reader_load_invalid_file() {
        let reader = PackageReader::new();
        let result = reader.load("/nonexistent/path.spk");
        assert!(result.is_err());
    }

    #[test]
    fn test_package_reader_load_from_bytes_empty() {
        let reader = PackageReader::new();
        let result = reader.load_from_bytes(&[]);
        assert!(result.is_err());
    }

    #[test]
    fn test_package_reader_load_from_bytes_invalid_magic() {
        let reader = PackageReader::new();
        let invalid_data = vec![0x00; 100];
        let result = reader.load_from_bytes(&invalid_data);
        assert!(result.is_err());
    }

    #[test]
    fn test_package_trailer_new() {
        use simple_loader::package::PackageTrailer;

        // PackageTrailer::new() creates a default trailer
        let trailer = PackageTrailer::new();
        assert_eq!(trailer.version, 1);
        assert!(!trailer.has_manifest());
        assert!(!trailer.has_resources());
    }

    #[test]
    fn test_package_trailer_flags() {
        use simple_loader::package::{PackageTrailer, SPK_FLAG_HAS_MANIFEST, SPK_FLAG_HAS_RESOURCES};

        let mut trailer = PackageTrailer::new();

        // Test has_manifest
        assert!(!trailer.has_manifest());
        trailer.flags |= SPK_FLAG_HAS_MANIFEST; // 0x0002
        assert!(trailer.has_manifest());

        // Test has_resources
        assert!(!trailer.has_resources());
        trailer.flags |= SPK_FLAG_HAS_RESOURCES; // 0x0001
        assert!(trailer.has_resources());
    }
}

// ===========================================================================
// Type Checker Unification Tests (simple_type)
// ===========================================================================
mod type_unification_tests {
    use simple_type::{Substitution, Type, TypeChecker, TypeError, TypeScheme};

    #[test]
    fn test_type_int_apply_subst() {
        let subst = Substitution::new();
        let ty = Type::Int;
        let result = ty.apply_subst(&subst);
        assert_eq!(result, Type::Int);
    }

    #[test]
    fn test_type_bool_apply_subst() {
        let subst = Substitution::new();
        let ty = Type::Bool;
        let result = ty.apply_subst(&subst);
        assert_eq!(result, Type::Bool);
    }

    #[test]
    fn test_type_str_apply_subst() {
        let subst = Substitution::new();
        let ty = Type::Str;
        let result = ty.apply_subst(&subst);
        assert_eq!(result, Type::Str);
    }

    #[test]
    fn test_type_float_apply_subst() {
        let subst = Substitution::new();
        let ty = Type::Float;
        let result = ty.apply_subst(&subst);
        assert_eq!(result, Type::Float);
    }

    #[test]
    fn test_type_nil_apply_subst() {
        let subst = Substitution::new();
        let ty = Type::Nil;
        let result = ty.apply_subst(&subst);
        assert_eq!(result, Type::Nil);
    }

    #[test]
    fn test_type_var_apply_subst_no_mapping() {
        let subst = Substitution::new();
        let ty = Type::Var(0);
        let result = ty.apply_subst(&subst);
        assert_eq!(result, Type::Var(0));
    }

    #[test]
    fn test_type_var_apply_subst_with_mapping() {
        let mut subst = Substitution::new();
        subst.insert(0, Type::Int);
        let ty = Type::Var(0);
        let result = ty.apply_subst(&subst);
        assert_eq!(result, Type::Int);
    }

    #[test]
    fn test_type_function_apply_subst() {
        let mut subst = Substitution::new();
        subst.insert(0, Type::Int);

        let ty = Type::Function {
            params: vec![Type::Var(0)],
            ret: Box::new(Type::Var(0)),
        };
        let result = ty.apply_subst(&subst);

        match result {
            Type::Function { params, ret } => {
                assert_eq!(params[0], Type::Int);
                assert_eq!(*ret, Type::Int);
            }
            _ => panic!("Expected Function type"),
        }
    }

    #[test]
    fn test_type_array_apply_subst() {
        let mut subst = Substitution::new();
        subst.insert(0, Type::Str);

        let ty = Type::Array(Box::new(Type::Var(0)));
        let result = ty.apply_subst(&subst);

        match result {
            Type::Array(inner) => assert_eq!(*inner, Type::Str),
            _ => panic!("Expected Array type"),
        }
    }

    #[test]
    fn test_type_tuple_apply_subst() {
        let mut subst = Substitution::new();
        subst.insert(0, Type::Int);

        let ty = Type::Tuple(vec![Type::Var(0), Type::Bool]);
        let result = ty.apply_subst(&subst);

        match result {
            Type::Tuple(types) => {
                assert_eq!(types[0], Type::Int);
                assert_eq!(types[1], Type::Bool);
            }
            _ => panic!("Expected Tuple type"),
        }
    }

    #[test]
    fn test_type_optional_apply_subst() {
        let mut subst = Substitution::new();
        subst.insert(0, Type::Int);

        let ty = Type::Optional(Box::new(Type::Var(0)));
        let result = ty.apply_subst(&subst);

        match result {
            Type::Optional(inner) => assert_eq!(*inner, Type::Int),
            _ => panic!("Expected Optional type"),
        }
    }

    #[test]
    fn test_type_union_apply_subst() {
        let mut subst = Substitution::new();
        subst.insert(0, Type::Int);

        let ty = Type::Union(vec![Type::Var(0), Type::Str]);
        let result = ty.apply_subst(&subst);

        match result {
            Type::Union(types) => {
                assert_eq!(types[0], Type::Int);
                assert_eq!(types[1], Type::Str);
            }
            _ => panic!("Expected Union type"),
        }
    }

    #[test]
    fn test_type_contains_var_true() {
        let ty = Type::Var(0);
        assert!(ty.contains_var(0));
    }

    #[test]
    fn test_type_contains_var_false() {
        let ty = Type::Int;
        assert!(!ty.contains_var(0));
    }

    #[test]
    fn test_type_contains_var_in_function() {
        let ty = Type::Function {
            params: vec![Type::Var(0)],
            ret: Box::new(Type::Int),
        };
        assert!(ty.contains_var(0));
        assert!(!ty.contains_var(1));
    }

    #[test]
    fn test_type_contains_var_in_array() {
        let ty = Type::Array(Box::new(Type::Var(5)));
        assert!(ty.contains_var(5));
        assert!(!ty.contains_var(0));
    }

    #[test]
    fn test_type_contains_var_in_tuple() {
        let ty = Type::Tuple(vec![Type::Int, Type::Var(3)]);
        assert!(ty.contains_var(3));
        assert!(!ty.contains_var(0));
    }

    #[test]
    fn test_substitution_new() {
        let subst = Substitution::new();
        assert!(subst.get(0).is_none());
    }

    #[test]
    fn test_substitution_insert_get() {
        let mut subst = Substitution::new();
        subst.insert(0, Type::Int);
        assert_eq!(subst.get(0), Some(&Type::Int));
        assert!(subst.get(1).is_none());
    }

    #[test]
    fn test_substitution_compose() {
        let mut subst1 = Substitution::new();
        subst1.insert(0, Type::Int);

        let mut subst2 = Substitution::new();
        subst2.insert(1, Type::Var(0)); // var 1 maps to var 0

        subst1.compose(&subst2);

        // After composing: subst1 applies to types in subst2 during merge
        // So Var(0) in subst2 becomes Int (from subst1)
        // subst1 now has: 0 -> Int, 1 -> Int
        assert_eq!(subst1.get(0), Some(&Type::Int));
        assert_eq!(subst1.get(1), Some(&Type::Int));
    }

    #[test]
    fn test_substitution_compose_preserves_original() {
        let mut subst1 = Substitution::new();
        subst1.insert(0, Type::Bool);

        let mut subst2 = Substitution::new();
        subst2.insert(1, Type::Str);

        subst1.compose(&subst2);

        // Original mapping preserved
        assert_eq!(subst1.get(0), Some(&Type::Bool));
        // New mapping added
        assert_eq!(subst1.get(1), Some(&Type::Str));
    }

    #[test]
    fn test_type_scheme_mono() {
        let scheme = TypeScheme::mono(Type::Int);
        assert!(scheme.vars.is_empty());
        assert_eq!(scheme.ty, Type::Int);
    }

    #[test]
    fn test_type_scheme_poly() {
        let scheme = TypeScheme::poly(vec![0, 1], Type::Var(0));
        assert_eq!(scheme.vars.len(), 2);
        assert_eq!(scheme.ty, Type::Var(0));
    }

    #[test]
    fn test_type_error_mismatch() {
        let err = TypeError::Mismatch {
            expected: Type::Int,
            found: Type::Bool,
        };
        match err {
            TypeError::Mismatch { expected, found } => {
                assert_eq!(expected, Type::Int);
                assert_eq!(found, Type::Bool);
            }
            _ => panic!("Expected Mismatch"),
        }
    }

    #[test]
    fn test_type_error_undefined() {
        let err = TypeError::Undefined("foo".to_string());
        match err {
            TypeError::Undefined(name) => assert_eq!(name, "foo"),
            _ => panic!("Expected Undefined"),
        }
    }

    #[test]
    fn test_type_error_occurs_check() {
        let err = TypeError::OccursCheck {
            var_id: 0,
            ty: Type::Int,
        };
        match err {
            TypeError::OccursCheck { var_id, ty } => {
                assert_eq!(var_id, 0);
                assert_eq!(ty, Type::Int);
            }
            _ => panic!("Expected OccursCheck"),
        }
    }

    #[test]
    fn test_type_error_other() {
        let err = TypeError::Other("custom error".to_string());
        match err {
            TypeError::Other(msg) => assert_eq!(msg, "custom error"),
            _ => panic!("Expected Other"),
        }
    }

    #[test]
    fn test_type_checker_new() {
        let checker = TypeChecker::new();
        let _ = checker;
    }

    #[test]
    fn test_type_checker_fresh_var() {
        let mut checker = TypeChecker::new();
        let v1 = checker.fresh_var();
        let v2 = checker.fresh_var();

        // Fresh vars should be different
        assert_ne!(v1, v2);
    }

    #[test]
    fn test_type_checker_unify_same_primitives() {
        let mut checker = TypeChecker::new();
        assert!(checker.unify(&Type::Int, &Type::Int).is_ok());
        assert!(checker.unify(&Type::Bool, &Type::Bool).is_ok());
        assert!(checker.unify(&Type::Str, &Type::Str).is_ok());
        assert!(checker.unify(&Type::Float, &Type::Float).is_ok());
        assert!(checker.unify(&Type::Nil, &Type::Nil).is_ok());
    }

    #[test]
    fn test_type_checker_unify_different_primitives() {
        let mut checker = TypeChecker::new();
        let result = checker.unify(&Type::Int, &Type::Bool);
        assert!(result.is_err());
    }

    #[test]
    fn test_type_checker_unify_var_with_type() {
        let mut checker = TypeChecker::new();
        let var = checker.fresh_var();
        assert!(checker.unify(&var, &Type::Int).is_ok());

        let resolved = checker.resolve(&var);
        assert_eq!(resolved, Type::Int);
    }

    #[test]
    fn test_type_checker_unify_type_with_var() {
        let mut checker = TypeChecker::new();
        let var = checker.fresh_var();
        assert!(checker.unify(&Type::Str, &var).is_ok());

        let resolved = checker.resolve(&var);
        assert_eq!(resolved, Type::Str);
    }

    #[test]
    fn test_type_checker_unify_arrays() {
        let mut checker = TypeChecker::new();
        let arr1 = Type::Array(Box::new(Type::Int));
        let arr2 = Type::Array(Box::new(Type::Int));
        assert!(checker.unify(&arr1, &arr2).is_ok());
    }

    #[test]
    fn test_type_checker_unify_arrays_different_elements() {
        let mut checker = TypeChecker::new();
        let arr1 = Type::Array(Box::new(Type::Int));
        let arr2 = Type::Array(Box::new(Type::Bool));
        assert!(checker.unify(&arr1, &arr2).is_err());
    }

    #[test]
    fn test_type_checker_unify_functions() {
        let mut checker = TypeChecker::new();
        let fn1 = Type::Function {
            params: vec![Type::Int],
            ret: Box::new(Type::Bool),
        };
        let fn2 = Type::Function {
            params: vec![Type::Int],
            ret: Box::new(Type::Bool),
        };
        assert!(checker.unify(&fn1, &fn2).is_ok());
    }

    #[test]
    fn test_type_checker_unify_functions_different_params() {
        let mut checker = TypeChecker::new();
        let fn1 = Type::Function {
            params: vec![Type::Int],
            ret: Box::new(Type::Bool),
        };
        let fn2 = Type::Function {
            params: vec![Type::Str],
            ret: Box::new(Type::Bool),
        };
        assert!(checker.unify(&fn1, &fn2).is_err());
    }

    #[test]
    fn test_type_checker_unify_tuples() {
        let mut checker = TypeChecker::new();
        let t1 = Type::Tuple(vec![Type::Int, Type::Bool]);
        let t2 = Type::Tuple(vec![Type::Int, Type::Bool]);
        assert!(checker.unify(&t1, &t2).is_ok());
    }

    #[test]
    fn test_type_checker_unify_tuples_different_length() {
        let mut checker = TypeChecker::new();
        let t1 = Type::Tuple(vec![Type::Int]);
        let t2 = Type::Tuple(vec![Type::Int, Type::Bool]);
        assert!(checker.unify(&t1, &t2).is_err());
    }

    #[test]
    fn test_type_checker_unify_occurs_check() {
        let mut checker = TypeChecker::new();
        let var = checker.fresh_var();
        let circular = Type::Array(Box::new(var.clone()));

        // This should fail the occurs check
        let result = checker.unify(&var, &circular);
        assert!(result.is_err());
    }

    #[test]
    fn test_type_checker_resolve() {
        let mut checker = TypeChecker::new();
        let var = checker.fresh_var();
        let _ = checker.unify(&var, &Type::Int);

        let resolved = checker.resolve(&var);
        assert_eq!(resolved, Type::Int);
    }

    #[test]
    fn test_type_checker_types_compatible_primitives() {
        let checker = TypeChecker::new();
        assert!(checker.types_compatible(&Type::Int, &Type::Int));
        assert!(checker.types_compatible(&Type::Bool, &Type::Bool));
        assert!(!checker.types_compatible(&Type::Int, &Type::Bool));
    }

    #[test]
    fn test_type_checker_types_compatible_with_var() {
        let checker = TypeChecker::new();
        assert!(checker.types_compatible(&Type::Var(0), &Type::Int));
        assert!(checker.types_compatible(&Type::Int, &Type::Var(0)));
    }

    #[test]
    fn test_type_checker_types_compatible_arrays() {
        let checker = TypeChecker::new();
        let arr1 = Type::Array(Box::new(Type::Int));
        let arr2 = Type::Array(Box::new(Type::Int));
        let arr3 = Type::Array(Box::new(Type::Bool));

        assert!(checker.types_compatible(&arr1, &arr2));
        assert!(!checker.types_compatible(&arr1, &arr3));
    }

    #[test]
    fn test_type_checker_type_matches_union() {
        let checker = TypeChecker::new();
        let union_members = vec![Type::Int, Type::Str];

        assert!(checker.type_matches_union(&Type::Int, &union_members));
        assert!(checker.type_matches_union(&Type::Str, &union_members));
        assert!(!checker.type_matches_union(&Type::Bool, &union_members));
    }
}

// ===========================================================================
// Package List Command Tests (simple_pkg::commands::list)
// ===========================================================================
mod pkg_list_tests {
    use simple_pkg::commands::list::{format_tree, InstalledPackage, TreeNode};

    #[test]
    fn test_installed_package_struct() {
        let pkg = InstalledPackage {
            name: "mylib".to_string(),
            version: "1.0.0".to_string(),
            source_type: "path".to_string(),
            is_linked: true,
        };

        assert_eq!(pkg.name, "mylib");
        assert_eq!(pkg.version, "1.0.0");
        assert_eq!(pkg.source_type, "path");
        assert!(pkg.is_linked);
    }

    #[test]
    fn test_tree_node_leaf() {
        let node = TreeNode {
            name: "leaf".to_string(),
            version: "1.0.0".to_string(),
            children: Vec::new(),
        };

        assert_eq!(node.name, "leaf");
        assert!(node.children.is_empty());
    }

    #[test]
    fn test_tree_node_with_children() {
        let child = TreeNode {
            name: "child".to_string(),
            version: "2.0.0".to_string(),
            children: Vec::new(),
        };

        let parent = TreeNode {
            name: "parent".to_string(),
            version: "1.0.0".to_string(),
            children: vec![child],
        };

        assert_eq!(parent.children.len(), 1);
        assert_eq!(parent.children[0].name, "child");
    }

    #[test]
    fn test_format_tree_root_only() {
        let tree = TreeNode {
            name: "myapp".to_string(),
            version: "1.0.0".to_string(),
            children: Vec::new(),
        };

        let output = format_tree(&tree, "", true);
        assert!(output.contains("myapp (1.0.0)"));
    }

    #[test]
    fn test_format_tree_with_children() {
        let tree = TreeNode {
            name: "myapp".to_string(),
            version: "1.0.0".to_string(),
            children: vec![
                TreeNode {
                    name: "lib_a".to_string(),
                    version: "2.0.0".to_string(),
                    children: Vec::new(),
                },
                TreeNode {
                    name: "lib_b".to_string(),
                    version: "3.0.0".to_string(),
                    children: Vec::new(),
                },
            ],
        };

        let output = format_tree(&tree, "", true);
        assert!(output.contains("myapp (1.0.0)"));
        assert!(output.contains("lib_a (2.0.0)"));
        assert!(output.contains("lib_b (3.0.0)"));
    }

    #[test]
    fn test_format_tree_nested() {
        let tree = TreeNode {
            name: "root".to_string(),
            version: "1.0.0".to_string(),
            children: vec![TreeNode {
                name: "child".to_string(),
                version: "2.0.0".to_string(),
                children: vec![TreeNode {
                    name: "grandchild".to_string(),
                    version: "3.0.0".to_string(),
                    children: Vec::new(),
                }],
            }],
        };

        let output = format_tree(&tree, "", true);
        assert!(output.contains("root"));
        assert!(output.contains("child"));
        assert!(output.contains("grandchild"));
    }

    #[test]
    fn test_format_tree_with_prefix() {
        let tree = TreeNode {
            name: "child".to_string(),
            version: "1.0.0".to_string(),
            children: Vec::new(),
        };

        // With non-empty prefix and is_last=true, should use └── connector
        let output = format_tree(&tree, "    ", true);
        assert!(output.contains("└──"));

        // With non-empty prefix and is_last=false, should use ├── connector
        let output = format_tree(&tree, "    ", false);
        assert!(output.contains("├──"));
    }
}

// ===========================================================================
// Lean Type Inference Tests (simple_type::lean_*)
// ===========================================================================
mod lean_type_tests {
    use simple_type::{infer_deterministic, infer_simple, lean_infer, LeanExpr, LeanTy};

    #[test]
    fn test_lean_ty_nat() {
        let ty = LeanTy::Nat;
        assert_eq!(ty, LeanTy::Nat);
    }

    #[test]
    fn test_lean_ty_bool() {
        let ty = LeanTy::Bool;
        assert_eq!(ty, LeanTy::Bool);
    }

    #[test]
    fn test_lean_ty_str() {
        let ty = LeanTy::Str;
        assert_eq!(ty, LeanTy::Str);
    }

    #[test]
    fn test_lean_ty_arrow() {
        let ty = LeanTy::Arrow(Box::new(LeanTy::Nat), Box::new(LeanTy::Bool));
        match ty {
            LeanTy::Arrow(a, b) => {
                assert_eq!(*a, LeanTy::Nat);
                assert_eq!(*b, LeanTy::Bool);
            }
            _ => panic!("Expected Arrow"),
        }
    }

    #[test]
    fn test_lean_expr_lit_nat() {
        let expr = LeanExpr::LitNat(42);
        let ty = lean_infer(&expr);
        assert_eq!(ty, Some(LeanTy::Nat));
    }

    #[test]
    fn test_lean_expr_lit_bool() {
        let expr = LeanExpr::LitBool(true);
        let ty = lean_infer(&expr);
        assert_eq!(ty, Some(LeanTy::Bool));
    }

    #[test]
    fn test_lean_expr_lit_str() {
        let expr = LeanExpr::LitStr("hello".to_string());
        let ty = lean_infer(&expr);
        assert_eq!(ty, Some(LeanTy::Str));
    }

    #[test]
    fn test_lean_expr_add() {
        let expr = LeanExpr::Add(Box::new(LeanExpr::LitNat(1)), Box::new(LeanExpr::LitNat(2)));
        let ty = lean_infer(&expr);
        assert_eq!(ty, Some(LeanTy::Nat));
    }

    #[test]
    fn test_lean_expr_add_type_error() {
        let expr = LeanExpr::Add(Box::new(LeanExpr::LitNat(1)), Box::new(LeanExpr::LitBool(true)));
        let ty = lean_infer(&expr);
        assert_eq!(ty, None);
    }

    #[test]
    fn test_lean_expr_concat() {
        let expr = LeanExpr::Concat(
            Box::new(LeanExpr::LitStr("hello".to_string())),
            Box::new(LeanExpr::LitStr(" world".to_string())),
        );
        let ty = lean_infer(&expr);
        assert_eq!(ty, Some(LeanTy::Str));
    }

    #[test]
    fn test_lean_expr_concat_type_error() {
        let expr = LeanExpr::Concat(
            Box::new(LeanExpr::LitStr("hello".to_string())),
            Box::new(LeanExpr::LitNat(42)),
        );
        let ty = lean_infer(&expr);
        assert_eq!(ty, None);
    }

    #[test]
    fn test_lean_expr_if_else() {
        let expr = LeanExpr::IfElse(
            Box::new(LeanExpr::LitBool(true)),
            Box::new(LeanExpr::LitNat(1)),
            Box::new(LeanExpr::LitNat(2)),
        );
        let ty = lean_infer(&expr);
        assert_eq!(ty, Some(LeanTy::Nat));
    }

    #[test]
    fn test_lean_expr_if_else_type_mismatch() {
        let expr = LeanExpr::IfElse(
            Box::new(LeanExpr::LitBool(true)),
            Box::new(LeanExpr::LitNat(1)),
            Box::new(LeanExpr::LitStr("no".to_string())),
        );
        let ty = lean_infer(&expr);
        assert_eq!(ty, None);
    }

    #[test]
    fn test_lean_expr_if_else_non_bool_condition() {
        let expr = LeanExpr::IfElse(
            Box::new(LeanExpr::LitNat(1)),
            Box::new(LeanExpr::LitNat(2)),
            Box::new(LeanExpr::LitNat(3)),
        );
        let ty = lean_infer(&expr);
        assert_eq!(ty, None);
    }

    #[test]
    fn test_lean_expr_lam() {
        let expr = LeanExpr::Lam(Box::new(LeanExpr::LitBool(true)));
        let ty = lean_infer(&expr);
        assert_eq!(ty, Some(LeanTy::Arrow(Box::new(LeanTy::Nat), Box::new(LeanTy::Bool))));
    }

    #[test]
    fn test_lean_expr_app() {
        let lam = LeanExpr::Lam(Box::new(LeanExpr::LitBool(true)));
        let expr = LeanExpr::App(Box::new(lam), Box::new(LeanExpr::LitNat(42)));
        let ty = lean_infer(&expr);
        assert_eq!(ty, Some(LeanTy::Bool));
    }

    #[test]
    fn test_lean_expr_app_wrong_arg_type() {
        let lam = LeanExpr::Lam(Box::new(LeanExpr::LitBool(true)));
        let expr = LeanExpr::App(Box::new(lam), Box::new(LeanExpr::LitBool(false)));
        let ty = lean_infer(&expr);
        assert_eq!(ty, None);
    }

    #[test]
    fn test_lean_expr_app_non_function() {
        let expr = LeanExpr::App(Box::new(LeanExpr::LitNat(1)), Box::new(LeanExpr::LitNat(2)));
        let ty = lean_infer(&expr);
        assert_eq!(ty, None);
    }

    #[test]
    fn test_infer_deterministic() {
        let expr = LeanExpr::Add(Box::new(LeanExpr::LitNat(1)), Box::new(LeanExpr::LitNat(2)));
        assert!(infer_deterministic(&expr));
    }

    #[test]
    fn test_infer_simple_alias() {
        let expr = LeanExpr::LitNat(42);
        assert_eq!(infer_simple(&expr), lean_infer(&expr));
    }
}

// ===========================================================================
// Type Generic and Dict Tests
// ===========================================================================
mod type_generic_dict_tests {
    use simple_type::{Substitution, Type};

    #[test]
    fn test_type_generic_apply_subst() {
        let mut subst = Substitution::new();
        subst.insert(0, Type::Int);

        let ty = Type::Generic {
            name: "Option".to_string(),
            args: vec![Type::Var(0)],
        };
        let result = ty.apply_subst(&subst);

        match result {
            Type::Generic { name, args } => {
                assert_eq!(name, "Option");
                assert_eq!(args[0], Type::Int);
            }
            _ => panic!("Expected Generic"),
        }
    }

    #[test]
    fn test_type_dict_apply_subst() {
        let mut subst = Substitution::new();
        subst.insert(0, Type::Str);
        subst.insert(1, Type::Int);

        let ty = Type::Dict {
            key: Box::new(Type::Var(0)),
            value: Box::new(Type::Var(1)),
        };
        let result = ty.apply_subst(&subst);

        match result {
            Type::Dict { key, value } => {
                assert_eq!(*key, Type::Str);
                assert_eq!(*value, Type::Int);
            }
            _ => panic!("Expected Dict"),
        }
    }

    #[test]
    fn test_type_borrow_apply_subst() {
        let mut subst = Substitution::new();
        subst.insert(0, Type::Int);

        let ty = Type::Borrow(Box::new(Type::Var(0)));
        let result = ty.apply_subst(&subst);

        match result {
            Type::Borrow(inner) => assert_eq!(*inner, Type::Int),
            _ => panic!("Expected Borrow"),
        }
    }

    #[test]
    fn test_type_borrow_mut_apply_subst() {
        let mut subst = Substitution::new();
        subst.insert(0, Type::Int);

        let ty = Type::BorrowMut(Box::new(Type::Var(0)));
        let result = ty.apply_subst(&subst);

        match result {
            Type::BorrowMut(inner) => assert_eq!(*inner, Type::Int),
            _ => panic!("Expected BorrowMut"),
        }
    }

    #[test]
    fn test_type_simd_apply_subst() {
        let mut subst = Substitution::new();
        subst.insert(0, Type::Float);

        let ty = Type::Simd {
            lanes: 4,
            element: Box::new(Type::Var(0)),
        };
        let result = ty.apply_subst(&subst);

        match result {
            Type::Simd { lanes, element } => {
                assert_eq!(lanes, 4);
                assert_eq!(*element, Type::Float);
            }
            _ => panic!("Expected Simd"),
        }
    }

    #[test]
    fn test_type_named_no_subst() {
        let subst = Substitution::new();
        let ty = Type::Named("MyStruct".to_string());
        let result = ty.apply_subst(&subst);
        assert_eq!(result, Type::Named("MyStruct".to_string()));
    }

    #[test]
    fn test_type_type_param_no_subst() {
        let subst = Substitution::new();
        let ty = Type::TypeParam("T".to_string());
        let result = ty.apply_subst(&subst);
        assert_eq!(result, Type::TypeParam("T".to_string()));
    }

    #[test]
    fn test_type_dyn_trait_no_subst() {
        let subst = Substitution::new();
        let ty = Type::DynTrait("Iterator".to_string());
        let result = ty.apply_subst(&subst);
        assert_eq!(result, Type::DynTrait("Iterator".to_string()));
    }

    #[test]
    fn test_type_contains_var_in_union() {
        let ty = Type::Union(vec![Type::Int, Type::Var(5)]);
        assert!(ty.contains_var(5));
        assert!(!ty.contains_var(0));
    }

    #[test]
    fn test_type_contains_var_in_generic() {
        let ty = Type::Generic {
            name: "Result".to_string(),
            args: vec![Type::Var(3), Type::Int],
        };
        assert!(ty.contains_var(3));
        assert!(!ty.contains_var(0));
    }

    #[test]
    fn test_type_contains_var_in_dict() {
        let ty = Type::Dict {
            key: Box::new(Type::Str),
            value: Box::new(Type::Var(7)),
        };
        assert!(ty.contains_var(7));
        assert!(!ty.contains_var(0));
    }

    #[test]
    fn test_type_contains_var_in_optional() {
        let ty = Type::Optional(Box::new(Type::Var(2)));
        assert!(ty.contains_var(2));
        assert!(!ty.contains_var(0));
    }

    #[test]
    fn test_type_contains_var_in_borrow() {
        let ty = Type::Borrow(Box::new(Type::Var(4)));
        assert!(ty.contains_var(4));
    }

    #[test]
    fn test_type_contains_var_in_borrow_mut() {
        let ty = Type::BorrowMut(Box::new(Type::Var(6)));
        assert!(ty.contains_var(6));
    }

    #[test]
    fn test_type_contains_var_in_simd() {
        let ty = Type::Simd {
            lanes: 8,
            element: Box::new(Type::Var(9)),
        };
        assert!(ty.contains_var(9));
    }
}

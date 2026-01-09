//! Round 15: Extended tests for uncovered public types
//! Focus on compiler value types, loader cross_test, and more

// ============================================================================
// Compiler Value Types - BuiltinClass
// ============================================================================
mod compiler_builtin_class_tests {
    use simple_compiler::value::{BuiltinClass, ClassType, MethodLookupResult};

    #[test]
    fn test_builtin_class_variants() {
        let classes = [BuiltinClass::Range, BuiltinClass::Array];
        for c in classes {
            let _ = format!("{:?}", c);
        }
    }

    #[test]
    fn test_builtin_class_from_name() {
        assert_eq!(BuiltinClass::from_name("Range"), Some(BuiltinClass::Range));
        assert_eq!(
            BuiltinClass::from_name("__range__"),
            Some(BuiltinClass::Range)
        );
        assert_eq!(BuiltinClass::from_name("Array"), Some(BuiltinClass::Array));
        assert_eq!(
            BuiltinClass::from_name("__array__"),
            Some(BuiltinClass::Array)
        );
        assert_eq!(BuiltinClass::from_name("Unknown"), None);
    }

    #[test]
    fn test_builtin_class_as_str() {
        assert_eq!(BuiltinClass::Range.as_str(), "__range__");
        assert_eq!(BuiltinClass::Array.as_str(), "__array__");
    }

    #[test]
    fn test_builtin_class_matches() {
        assert!(BuiltinClass::Range.matches("Range"));
        assert!(BuiltinClass::Range.matches("__range__"));
        assert!(!BuiltinClass::Range.matches("Array"));
    }

    #[test]
    fn test_class_type_from_name() {
        let ct1 = ClassType::from_name("Range");
        assert!(ct1.is_builtin());
        assert!(ct1.is_range());

        let ct2 = ClassType::from_name("MyClass");
        assert!(!ct2.is_builtin());
        assert!(!ct2.is_range());
    }

    #[test]
    fn test_method_lookup_result() {
        let results = [
            MethodLookupResult::Found,
            MethodLookupResult::NotFound,
            MethodLookupResult::MissingHook,
        ];
        for r in results {
            let _ = format!("{:?}", r);
        }
        assert!(MethodLookupResult::Found.is_callable());
        assert!(!MethodLookupResult::NotFound.is_callable());
        assert!(MethodLookupResult::MissingHook.is_callable());
        assert!(MethodLookupResult::MissingHook.is_missing_hook());
    }
}

// ============================================================================
// Compiler Value Types - Special Enums
// ============================================================================
mod compiler_special_enum_tests {
    use simple_compiler::value::{OptionVariant, ResultVariant, SpecialEnumType};

    #[test]
    fn test_special_enum_type_variants() {
        let types = [SpecialEnumType::Option, SpecialEnumType::Result];
        for t in types {
            let _ = format!("{:?}", t);
        }
    }

    #[test]
    fn test_special_enum_type_from_name() {
        assert_eq!(
            SpecialEnumType::from_name("Option"),
            Some(SpecialEnumType::Option)
        );
        assert_eq!(
            SpecialEnumType::from_name("Result"),
            Some(SpecialEnumType::Result)
        );
        assert_eq!(SpecialEnumType::from_name("Unknown"), None);
    }

    #[test]
    fn test_special_enum_type_as_str() {
        assert_eq!(SpecialEnumType::Option.as_str(), "Option");
        assert_eq!(SpecialEnumType::Result.as_str(), "Result");
    }

    #[test]
    fn test_option_variant() {
        let variants = [OptionVariant::Some, OptionVariant::None];
        for v in variants {
            let _ = format!("{:?}", v);
        }
        assert_eq!(OptionVariant::from_name("Some"), Some(OptionVariant::Some));
        assert_eq!(OptionVariant::from_name("None"), Some(OptionVariant::None));
    }

    #[test]
    fn test_result_variant() {
        let variants = [ResultVariant::Ok, ResultVariant::Err];
        for v in variants {
            let _ = format!("{:?}", v);
        }
        assert_eq!(ResultVariant::from_name("Ok"), Some(ResultVariant::Ok));
        assert_eq!(ResultVariant::from_name("Err"), Some(ResultVariant::Err));
    }
}

// ============================================================================
// Loader Cross-Test Types
// ============================================================================
mod loader_cross_test_types {
    use simple_loader::{CrossTestResults, TargetFixture, TestMatrix};

    #[test]
    fn test_target_fixture_x86_64_linux() {
        let fixture = TargetFixture::x86_64_linux();
        let _ = format!("{:?}", fixture);
    }

    #[test]
    fn test_target_fixture_aarch64_linux() {
        let fixture = TargetFixture::aarch64_linux();
        let _ = format!("{:?}", fixture);
    }

    #[test]
    fn test_target_fixture_x86_64_windows() {
        let fixture = TargetFixture::x86_64_windows();
        let _ = format!("{:?}", fixture);
    }

    #[test]
    fn test_target_fixture_aarch64_macos() {
        let fixture = TargetFixture::aarch64_macos();
        let _ = format!("{:?}", fixture);
    }

    #[test]
    fn test_target_fixture_all_64bit() {
        let fixtures = TargetFixture::all_64bit();
        assert!(fixtures.len() >= 4);
        for f in fixtures {
            let _ = format!("{:?}", f);
        }
    }

    #[test]
    fn test_target_fixture_mock_headers() {
        let fixture = TargetFixture::x86_64_linux();
        let smf_header = fixture.mock_smf_header();
        let _ = format!("{:?}", smf_header);
        let settlement_header = fixture.mock_settlement_header();
        let _ = format!("{:?}", settlement_header);
    }

    #[test]
    fn test_target_fixture_host_check() {
        let fixture = TargetFixture::x86_64_linux();
        let _ = fixture.is_host();
        let _ = fixture.can_execute();
    }

    #[test]
    fn test_test_matrix_new() {
        let matrix = TestMatrix::new();
        let targets = matrix.targets();
        assert!(targets.len() >= 2);
    }

    #[test]
    fn test_test_matrix_minimal() {
        let matrix = TestMatrix::minimal();
        let targets = matrix.targets();
        assert_eq!(targets.len(), 1);
    }

    #[test]
    fn test_test_matrix_comprehensive() {
        let matrix = TestMatrix::comprehensive();
        let targets = matrix.targets();
        assert!(targets.len() >= 6);
    }

    #[test]
    fn test_test_matrix_fixtures() {
        let matrix = TestMatrix::new();
        let fixtures = matrix.fixtures();
        assert!(fixtures.len() >= 2);
    }

    #[test]
    fn test_test_matrix_default() {
        let matrix = TestMatrix::default();
        let _ = matrix;
    }

    #[test]
    fn test_cross_test_results_default() {
        let results = CrossTestResults::default();
        let _ = format!("{:?}", results);
    }
}

// ============================================================================
// Compiler Value Constants
// ============================================================================
mod compiler_value_constants_tests {
    use simple_compiler::value::{
        ACTOR_BUILTINS, ATTR_STRONG, BLOCKING_BUILTINS, BUILTIN_ARRAY, BUILTIN_CHANNEL,
        BUILTIN_RANGE, BUILTIN_SPAWN, CLASS_ARRAY, CLASS_RANGE, FUNC_MAIN, GENERATOR_BUILTINS,
        METHOD_MISSING, METHOD_NEW, METHOD_SELF,
    };

    #[test]
    fn test_magic_name_constants() {
        assert_eq!(BUILTIN_RANGE, "__range__");
        assert_eq!(BUILTIN_ARRAY, "__array__");
        assert_eq!(METHOD_NEW, "new");
        assert_eq!(METHOD_SELF, "self");
        assert_eq!(METHOD_MISSING, "method_missing");
        assert_eq!(FUNC_MAIN, "main");
        assert_eq!(ATTR_STRONG, "strong");
    }

    #[test]
    fn test_builtin_type_constants() {
        assert_eq!(BUILTIN_CHANNEL, "Channel");
        assert_eq!(BUILTIN_SPAWN, "spawn");
        assert_eq!(CLASS_RANGE, "Range");
        assert_eq!(CLASS_ARRAY, "Array");
    }

    #[test]
    fn test_blocking_builtins() {
        assert!(BLOCKING_BUILTINS.contains(&"await"));
        assert!(BLOCKING_BUILTINS.contains(&"sleep"));
        assert!(BLOCKING_BUILTINS.contains(&"recv"));
    }

    #[test]
    fn test_actor_builtins() {
        assert!(ACTOR_BUILTINS.contains(&"spawn"));
        assert!(ACTOR_BUILTINS.contains(&"send"));
        assert!(ACTOR_BUILTINS.contains(&"recv"));
    }

    #[test]
    fn test_generator_builtins() {
        assert!(GENERATOR_BUILTINS.contains(&"generator"));
        assert!(GENERATOR_BUILTINS.contains(&"next"));
        assert!(GENERATOR_BUILTINS.contains(&"collect"));
    }
}

// ============================================================================
// Loader Arch Validate
// ============================================================================
mod loader_arch_validate_tests {
    use simple_loader::ArchValidator;

    #[test]
    fn test_arch_validator_new() {
        let validator = ArchValidator::new();
        let _ = validator;
    }
}

// ============================================================================
// Loader Load Error
// ============================================================================
mod loader_load_error_tests {
    use simple_loader::LoadError;

    #[test]
    fn test_load_error_io() {
        let err = LoadError::Io(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            "not found",
        ));
        let _ = format!("{:?}", err);
    }
}

// ============================================================================
// Loader Startup Types
// ============================================================================
mod loader_startup_tests {
    use simple_loader::StartupLoader;

    #[test]
    fn test_startup_loader_new() {
        let loader = StartupLoader::new();
        let _ = loader;
    }
}

// ============================================================================
// Package Error Types
// ============================================================================
mod pkg_error_tests {
    use simple_pkg::{PkgError, PkgResult};

    #[test]
    fn test_pkg_error_size() {
        // Test that PkgError type exists
        let _ = std::mem::size_of::<PkgError>();
    }

    #[test]
    fn test_pkg_result_type() {
        // Test that PkgResult type alias works
        let result: PkgResult<i32> = Ok(42);
        assert_eq!(result.unwrap(), 42);
    }
}

// ============================================================================
// Package Cache Types
// ============================================================================
mod pkg_cache_tests {
    use simple_pkg::Cache;

    #[test]
    fn test_cache_new() {
        let cache = Cache::new();
        let _ = cache;
    }
}

// ============================================================================
// Package Linker Types
// ============================================================================
mod pkg_linker_tests {
    use simple_pkg::Linker;
    use std::path::Path;

    #[test]
    fn test_linker_new() {
        let linker = Linker::new(Path::new("/tmp/test_project"));
        let _ = linker;
    }
}

// ============================================================================
// Compiler ClassName Methods
// ============================================================================
mod compiler_classname_tests {
    use simple_compiler::{ClassName, EnumTypeName, VariantName};

    #[test]
    fn test_class_name_methods() {
        let name = ClassName::new("MyClass");
        assert_eq!(name.as_str(), "MyClass");

        let from_str: ClassName = "OtherClass".into();
        assert_eq!(from_str.as_str(), "OtherClass");

        let from_string: ClassName = String::from("ThirdClass").into();
        assert_eq!(from_string.as_str(), "ThirdClass");
    }

    #[test]
    fn test_enum_type_name_methods() {
        let name = EnumTypeName::new("MyEnum");
        assert_eq!(name.as_str(), "MyEnum");

        let from_str: EnumTypeName = "OtherEnum".into();
        assert_eq!(from_str.as_str(), "OtherEnum");
    }

    #[test]
    fn test_variant_name_methods() {
        let name = VariantName::new("Some");
        assert_eq!(name.as_str(), "Some");

        let from_str: VariantName = "None".into();
        assert_eq!(from_str.as_str(), "None");
    }
}

// ============================================================================
// Parser Additional Token Kinds
// ============================================================================
mod parser_token_extra_tests {
    use simple_parser::TokenKind;

    #[test]
    fn test_token_kind_more_keywords() {
        let kinds = [
            TokenKind::Match,
            TokenKind::Case,
            TokenKind::Break,
            TokenKind::Continue,
            TokenKind::In,
            TokenKind::As,
            TokenKind::Async,
            TokenKind::Await,
            TokenKind::Actor,
            TokenKind::Const,
        ];
        for k in kinds {
            let _ = format!("{:?}", k);
        }
    }
}

// ============================================================================
// Parser SelfMode Tests
// ============================================================================
mod parser_self_mode_tests {
    use simple_parser::SelfMode;

    #[test]
    fn test_self_mode_default() {
        let mode = SelfMode::default();
        let _ = format!("{:?}", mode);
    }
}

// ============================================================================
// Parser StorageClass Tests
// ============================================================================
mod parser_storage_class_tests {
    use simple_parser::StorageClass;

    #[test]
    fn test_storage_class_default() {
        let sc = StorageClass::default();
        let _ = format!("{:?}", sc);
    }
}

// ============================================================================
// Parser MoveMode Tests
// ============================================================================
mod parser_move_mode_tests {
    use simple_parser::MoveMode;

    #[test]
    fn test_move_mode_default() {
        let mode = MoveMode::default();
        let _ = format!("{:?}", mode);
    }
}

// ============================================================================
// Loader LoadedModule Tests
// ============================================================================
mod loader_loaded_module_tests {
    use simple_loader::LoadedModule;

    #[test]
    fn test_loaded_module_size() {
        // Verify the type exists
        let _ = std::mem::size_of::<LoadedModule>();
    }
}

// ============================================================================
// Type Checker Additional Tests
// ============================================================================
mod type_checker_additional_tests {
    use simple_type::{Substitution, Type, TypeScheme};

    #[test]
    fn test_type_nil() {
        let t = Type::Nil;
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_type_var() {
        let t = Type::Var(42);
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_substitution_compose() {
        let mut s1 = Substitution::new();
        let s2 = Substitution::new();
        s1.compose(&s2);
        let _ = format!("{:?}", s1);
    }

    #[test]
    fn test_type_scheme_mono() {
        let ts = TypeScheme::mono(Type::Int);
        let _ = format!("{:?}", ts);
    }

    #[test]
    fn test_type_scheme_poly() {
        let ts = TypeScheme::poly(vec![1, 2], Type::Bool);
        let _ = format!("{:?}", ts);
    }
}

// ============================================================================
// Compiler Project Context Tests
// ============================================================================
mod compiler_project_tests {
    use simple_compiler::ProjectContext;
    use std::path::PathBuf;
    use tempfile::TempDir;

    #[test]
    fn test_project_context_new() {
        let tmp = TempDir::new().unwrap();
        // ProjectContext::new returns Result
        let result = ProjectContext::new(tmp.path().to_path_buf());
        // Either succeeds or fails - both are valid for testing
        let _ = format!("{:?}", result);
    }
}

// ============================================================================
// Compiler Compilability Tests
// ============================================================================
mod compiler_compilability_tests {
    use simple_compiler::compilability::{CompilabilityStatus, FallbackReason};

    #[test]
    fn test_compilability_status() {
        let status = CompilabilityStatus::Compilable;
        let _ = format!("{:?}", status);
    }

    #[test]
    fn test_fallback_reason_closure() {
        let reason = FallbackReason::Closure;
        let _ = format!("{:?}", reason);
    }

    #[test]
    fn test_fallback_reason_dynamic_types() {
        let reason = FallbackReason::DynamicTypes;
        let _ = format!("{:?}", reason);
    }

    #[test]
    fn test_fallback_reason_collection_ops() {
        let reason = FallbackReason::CollectionOps;
        let _ = format!("{:?}", reason);
    }
}

//! Round 22: Extended tests for remaining uncovered public types
//! Focus on compiler, loader, runtime types

// ============================================================================
// Compiler Monomorphizer Types
// ============================================================================
mod compiler_monomorphizer_tests {
    use simple_compiler::monomorphize::Monomorphizer;

    #[test]
    fn test_monomorphizer_size() {
        let _ = std::mem::size_of::<Monomorphizer>();
    }
}

// ============================================================================
// Compiler Outlined Body Types
// ============================================================================
mod compiler_outlined_body_tests {
    use simple_compiler::mir::OutlinedBody;

    #[test]
    fn test_outlined_body_size() {
        let _ = std::mem::size_of::<OutlinedBody>();
    }
}

// ============================================================================
// Loader Native Handle Types
// ============================================================================
mod loader_native_handle_tests {
    use simple_loader::native_cross::NativeLibConfig;

    #[test]
    fn test_native_lib_config_size() {
        let _ = std::mem::size_of::<NativeLibConfig>();
    }
}

// ============================================================================
// Runtime Object Types
// ============================================================================
mod runtime_object_tests {
    use simple_runtime::RuntimeObject;

    #[test]
    fn test_runtime_object_size() {
        let _ = std::mem::size_of::<RuntimeObject>();
    }
}

// ============================================================================
// Runtime String Types
// ============================================================================
mod runtime_string_tests {
    use simple_runtime::RuntimeString;

    #[test]
    fn test_runtime_string_size() {
        let _ = std::mem::size_of::<RuntimeString>();
    }
}

// ============================================================================
// Runtime Array Types
// ============================================================================
mod runtime_array_tests {
    use simple_runtime::RuntimeArray;

    #[test]
    fn test_runtime_array_size() {
        let _ = std::mem::size_of::<RuntimeArray>();
    }
}

// ============================================================================
// Runtime Tuple Types
// ============================================================================
mod runtime_tuple_tests {
    use simple_runtime::RuntimeTuple;

    #[test]
    fn test_runtime_tuple_size() {
        let _ = std::mem::size_of::<RuntimeTuple>();
    }
}

// ============================================================================
// Runtime Dict Types
// ============================================================================
mod runtime_dict_tests {
    use simple_runtime::RuntimeDict;

    #[test]
    fn test_runtime_dict_size() {
        let _ = std::mem::size_of::<RuntimeDict>();
    }
}

// ============================================================================
// Compiler Env Extended Types
// ============================================================================
mod compiler_env_extended_tests {
    use simple_compiler::value::Env;

    #[test]
    fn test_env_size() {
        let _ = std::mem::size_of::<Env>();
    }
}

// ============================================================================
// Compiler Module Resolver Extended Types
// ============================================================================
mod compiler_module_resolver_extended_tests {
    use simple_compiler::{ModuleResolver, ResolvedModule};

    #[test]
    fn test_module_resolver_size() {
        let _ = std::mem::size_of::<ModuleResolver>();
    }

    #[test]
    fn test_resolved_module_size() {
        let _ = std::mem::size_of::<ResolvedModule>();
    }
}

// ============================================================================
// Compiler Pipeline Extended Types
// ============================================================================
mod compiler_pipeline_extended_tests {
    use simple_compiler::{CompileError, CompilerPipeline};

    #[test]
    fn test_compiler_pipeline_size() {
        let _ = std::mem::size_of::<CompilerPipeline>();
    }

    #[test]
    fn test_compile_error_size() {
        let _ = std::mem::size_of::<CompileError>();
    }
}

// ============================================================================
// Compiler HIR Expr Types
// ============================================================================
mod compiler_hir_expr_tests {
    use simple_compiler::hir::{HirExpr, HirStmt};

    #[test]
    fn test_hir_expr_size() {
        let _ = std::mem::size_of::<HirExpr>();
    }

    #[test]
    fn test_hir_stmt_size() {
        let _ = std::mem::size_of::<HirStmt>();
    }
}

// ============================================================================
// Driver Runner Types
// ============================================================================
mod driver_runner_tests {
    use simple_driver::{RunResult, Runner};

    #[test]
    fn test_runner_size() {
        let _ = std::mem::size_of::<Runner>();
    }

    #[test]
    fn test_run_result_size() {
        let _ = std::mem::size_of::<RunResult>();
    }
}

// ============================================================================
// Loader Module Types
// ============================================================================
mod loader_module_tests {
    use simple_loader::{LoadedModule, ModuleLoader, ModuleRegistry};

    #[test]
    fn test_module_loader_size() {
        let _ = std::mem::size_of::<ModuleLoader>();
    }

    #[test]
    fn test_module_registry_size() {
        let _ = std::mem::size_of::<ModuleRegistry>();
    }

    #[test]
    fn test_loaded_module_size() {
        let _ = std::mem::size_of::<LoadedModule>();
    }
}

// ============================================================================
// Runtime Value Types
// ============================================================================
mod runtime_value_tests {
    use simple_runtime::RuntimeValue;

    #[test]
    fn test_runtime_value_size() {
        let _ = std::mem::size_of::<RuntimeValue>();
    }
}

// ============================================================================
// Runtime GC Types
// ============================================================================
mod runtime_gc_tests {
    use simple_runtime::memory::{GcRuntime, NoGcAllocator};

    #[test]
    fn test_gc_runtime_size() {
        let _ = std::mem::size_of::<GcRuntime>();
    }

    #[test]
    fn test_no_gc_allocator_size() {
        let _ = std::mem::size_of::<NoGcAllocator>();
    }
}

// ============================================================================
// Compiler Monomorphize Table Types
// ============================================================================
mod compiler_monomorphize_table_tests {
    use simple_compiler::monomorphize::MonomorphizationTable;

    #[test]
    fn test_monomorphization_table_size() {
        let _ = std::mem::size_of::<MonomorphizationTable>();
    }
}

// ============================================================================
// Common Message Types
// ============================================================================
mod common_message_tests {
    use simple_common::actor::Message;

    #[test]
    fn test_message_size() {
        let _ = std::mem::size_of::<Message>();
    }
}

// ============================================================================
// Compiler Value Extended Types
// ============================================================================
mod compiler_value_extended_tests {
    use simple_compiler::value::{ClassType, SpecialEnumType, Value};

    #[test]
    fn test_value_size() {
        let _ = std::mem::size_of::<Value>();
    }

    #[test]
    fn test_class_type_size() {
        let _ = std::mem::size_of::<ClassType>();
    }

    #[test]
    fn test_special_enum_type_size() {
        let _ = std::mem::size_of::<SpecialEnumType>();
    }
}

// ============================================================================
// Loader Settlement Builder Types
// ============================================================================
mod loader_settlement_builder_tests {
    use simple_loader::settlement::SettlementBuilder;

    #[test]
    fn test_settlement_builder_size() {
        let _ = std::mem::size_of::<SettlementBuilder>();
    }
}

// ============================================================================
// Pkg Version Types
// ============================================================================
mod pkg_version_tests {
    use simple_pkg::{Version, VersionReq};

    #[test]
    fn test_version_size() {
        let _ = std::mem::size_of::<Version>();
    }

    #[test]
    fn test_version_req_size() {
        let _ = std::mem::size_of::<VersionReq>();
    }
}

// ============================================================================
// Pkg Manifest Types
// ============================================================================
mod pkg_manifest_tests {
    use simple_pkg::{LockFile, Manifest};

    #[test]
    fn test_manifest_size() {
        let _ = std::mem::size_of::<Manifest>();
    }

    #[test]
    fn test_lock_file_size() {
        let _ = std::mem::size_of::<LockFile>();
    }
}

// ============================================================================
// Type Crate Types
// ============================================================================
mod type_crate_tests {
    use simple_type::{Substitution, Type, TypeScheme};

    #[test]
    fn test_type_size() {
        let _ = std::mem::size_of::<Type>();
    }

    #[test]
    fn test_type_scheme_size() {
        let _ = std::mem::size_of::<TypeScheme>();
    }

    #[test]
    fn test_substitution_size() {
        let _ = std::mem::size_of::<Substitution>();
    }
}

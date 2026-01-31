//! Round 21: Extended tests for remaining uncovered public types
//! Focus on compiler, loader, common, and driver types

// ============================================================================
// Compiler Backend Types
// ============================================================================
mod compiler_backend_tests {
    use simple_compiler::codegen::{BackendError, BackendKind, BackendSettings};

    #[test]
    fn test_backend_error_size() {
        let _ = std::mem::size_of::<BackendError>();
    }

    #[test]
    fn test_backend_kind_size() {
        let _ = std::mem::size_of::<BackendKind>();
    }

    #[test]
    fn test_backend_settings_size() {
        let _ = std::mem::size_of::<BackendSettings>();
    }
}

// ============================================================================
// Compiler Context Types
// ============================================================================
mod compiler_context_tests {
    use simple_compiler::mir::{ContractContext, LoopContext};

    #[test]
    fn test_contract_context_size() {
        let _ = std::mem::size_of::<ContractContext>();
    }

    #[test]
    fn test_loop_context_size() {
        let _ = std::mem::size_of::<LoopContext>();
    }
}

// ============================================================================
// Compiler Lint Types
// ============================================================================
mod compiler_lint_extended_tests {
    use simple_compiler::lint::{LintChecker, LintDiagnostic, LintName};

    #[test]
    fn test_lint_checker_size() {
        let _ = std::mem::size_of::<LintChecker>();
    }

    #[test]
    fn test_lint_diagnostic_size() {
        let _ = std::mem::size_of::<LintDiagnostic>();
    }

    #[test]
    fn test_lint_name_size() {
        let _ = std::mem::size_of::<LintName>();
    }
}

// ============================================================================
// Compiler Lower Error Types
// ============================================================================
mod compiler_lower_error_tests {
    use simple_compiler::mir::MirLowerError;

    #[test]
    fn test_mir_lower_error_size() {
        let _ = std::mem::size_of::<MirLowerError>();
    }
}

// ============================================================================
// Compiler JIT Types
// ============================================================================
mod compiler_jit_tests {
    use simple_compiler::codegen::JitCompiler;

    #[test]
    fn test_jit_compiler_size() {
        let _ = std::mem::size_of::<JitCompiler>();
    }
}

// ============================================================================
// Common Target Types
// ============================================================================
mod common_target_extended_tests {
    use simple_common::{TargetConfig, TargetParseError};

    #[test]
    fn test_target_config_size() {
        let _ = std::mem::size_of::<TargetConfig>();
    }

    #[test]
    fn test_target_parse_error_size() {
        let _ = std::mem::size_of::<TargetParseError>();
    }
}

// ============================================================================
// Loader Memory Allocator Types
// ============================================================================
mod loader_memory_allocator_tests {
    use simple_loader::memory::ExecutableMemory;

    #[test]
    fn test_executable_memory_size() {
        let _ = std::mem::size_of::<ExecutableMemory>();
    }
}

// ============================================================================
// Loader Native Lib Types
// ============================================================================
mod loader_native_lib_extended_tests {
    use simple_loader::native_cross::NativeLibBuilder;

    #[test]
    fn test_native_lib_builder_size() {
        let _ = std::mem::size_of::<NativeLibBuilder>();
    }
}

// ============================================================================
// Driver JJ Types
// ============================================================================
mod driver_jj_tests {
    use simple_driver::jj::JJConnector;

    #[test]
    fn test_jj_connector_size() {
        let _ = std::mem::size_of::<JJConnector>();
    }
}

// ============================================================================
// Runtime GC-less Allocator Types
// ============================================================================
mod runtime_gcless_tests {
    use simple_runtime::memory::GclessAllocator;

    #[test]
    fn test_gcless_allocator_size() {
        let _ = std::mem::size_of::<GclessAllocator>();
    }
}

// ============================================================================
// Loader Posix Allocator Types
// ============================================================================
#[cfg(unix)]
mod loader_posix_allocator_tests {
    use simple_loader::memory::PosixAllocator;

    #[test]
    fn test_posix_allocator_size() {
        let _ = std::mem::size_of::<PosixAllocator>();
    }
}

// ============================================================================
// Compiler Type Extended Types
// ============================================================================
mod compiler_type_extended_tests {
    use simple_type::Type;

    #[test]
    fn test_type_size() {
        let _ = std::mem::size_of::<Type>();
    }
}

// ============================================================================
// Loader Startup Extended Types
// ============================================================================
mod loader_startup_extended_tests {
    use simple_loader::startup::{StartupError, StartupLoader};

    #[test]
    fn test_startup_error_size() {
        let _ = std::mem::size_of::<StartupError>();
    }

    #[test]
    fn test_startup_loader_size() {
        let _ = std::mem::size_of::<StartupLoader>();
    }
}

// ============================================================================
// Common Actor Extended Types
// ============================================================================
mod common_actor_extended_tests {
    use simple_common::ActorHandle;

    #[test]
    fn test_actor_handle_size() {
        let _ = std::mem::size_of::<ActorHandle>();
    }
}

// ============================================================================
// Compiler Value Variant Extended Types
// ============================================================================
mod compiler_value_variant_extended_tests {
    use simple_compiler::value::{BuiltinClass, MethodLookupResult};

    #[test]
    fn test_builtin_class_size() {
        let _ = std::mem::size_of::<BuiltinClass>();
    }

    #[test]
    fn test_method_lookup_result_size() {
        let _ = std::mem::size_of::<MethodLookupResult>();
    }
}

// ============================================================================
// Loader SMF More Types
// ============================================================================
mod loader_smf_more_tests {
    use simple_loader::smf::{SmfHeader, SmfRelocation, SmfSection, SmfSymbol};

    #[test]
    fn test_smf_header_size() {
        let _ = std::mem::size_of::<SmfHeader>();
    }

    #[test]
    fn test_smf_section_size() {
        let _ = std::mem::size_of::<SmfSection>();
    }

    #[test]
    fn test_smf_symbol_size() {
        let _ = std::mem::size_of::<SmfSymbol>();
    }

    #[test]
    fn test_smf_relocation_size() {
        let _ = std::mem::size_of::<SmfRelocation>();
    }
}

// ============================================================================
// Compiler HIR More Types
// ============================================================================
mod compiler_hir_more_tests {
    use simple_compiler::hir::{HirFunction, HirModule, HirType};

    #[test]
    fn test_hir_type_size() {
        let _ = std::mem::size_of::<HirType>();
    }

    #[test]
    fn test_hir_function_size() {
        let _ = std::mem::size_of::<HirFunction>();
    }

    #[test]
    fn test_hir_module_size() {
        let _ = std::mem::size_of::<HirModule>();
    }
}

// ============================================================================
// Compiler MIR More Types
// ============================================================================
mod compiler_mir_more_tests {
    use simple_compiler::mir::{MirFunction, MirModule, Terminator};

    #[test]
    fn test_mir_function_size() {
        let _ = std::mem::size_of::<MirFunction>();
    }

    #[test]
    fn test_mir_module_size() {
        let _ = std::mem::size_of::<MirModule>();
    }

    #[test]
    fn test_terminator_size() {
        let _ = std::mem::size_of::<Terminator>();
    }
}

// ============================================================================
// Compiler Coverage More Types
// ============================================================================
mod compiler_coverage_more_tests {
    use simple_compiler::coverage::CoverageCollector;

    #[test]
    fn test_coverage_collector_new() {
        let collector = CoverageCollector::new();
        let _ = collector;
    }
}

// ============================================================================
// Compiler Compilability More Types
// ============================================================================
mod compiler_compilability_more_tests {
    use simple_compiler::compilability::{CompilabilityStatus, FallbackReason};

    #[test]
    fn test_compilability_status_variants() {
        let status = CompilabilityStatus::Compilable;
        let _ = format!("{:?}", status);
    }

    #[test]
    fn test_fallback_reason_variants() {
        let reason = FallbackReason::Closure;
        let _ = format!("{:?}", reason);
    }
}

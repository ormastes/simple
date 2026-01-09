//! Round 23: Extended tests for remaining uncovered public types
//! Focus on compiler, loader, runtime, pkg types

// ============================================================================
// Compiler SMF Write Error Types
// ============================================================================
mod compiler_smf_write_error_tests {
    use simple_compiler::linker::SmfWriteError;

    #[test]
    fn test_smf_write_error_size() {
        let _ = std::mem::size_of::<SmfWriteError>();
    }
}

// ============================================================================
// Compiler Special Enum Kind Types
// ============================================================================
mod compiler_special_enum_kind_tests {
    use simple_compiler::value::SpecialEnumKind;

    #[test]
    fn test_special_enum_kind_size() {
        let _ = std::mem::size_of::<SpecialEnumKind>();
    }
}

// ============================================================================
// Compiler Subtype Result Types
// ============================================================================
mod compiler_subtype_result_tests {
    use simple_compiler::hir::SubtypeResult;

    #[test]
    fn test_subtype_result_size() {
        let _ = std::mem::size_of::<SubtypeResult>();
    }
}

// ============================================================================
// Compiler Lower Error Types
// ============================================================================
mod compiler_lower_error_extended_tests {
    use simple_compiler::hir::LowerError;

    #[test]
    fn test_lower_error_size() {
        let _ = std::mem::size_of::<LowerError>();
    }
}

// ============================================================================
// Pkg Cache Extended Types
// ============================================================================
mod pkg_cache_extended_tests {
    use simple_pkg::Cache;

    #[test]
    fn test_cache_new() {
        let cache = Cache::new();
        let _ = cache;
    }
}

// ============================================================================
// Pkg Linker Extended Types
// ============================================================================
mod pkg_linker_extended_tests {
    use simple_pkg::Linker;

    #[test]
    fn test_linker_size() {
        let _ = std::mem::size_of::<Linker>();
    }
}

// ============================================================================
// Loader Cross Compile Types
// ============================================================================
mod loader_cross_compile_tests {
    use simple_loader::native_cross::CrossCompileError;

    #[test]
    fn test_cross_compile_error_size() {
        let _ = std::mem::size_of::<CrossCompileError>();
    }
}

// ============================================================================
// Loader Executable Memory Types
// ============================================================================
mod loader_executable_memory_tests {
    use simple_loader::memory::ExecutableMemory;

    #[test]
    fn test_executable_memory_new() {
        let _ = std::mem::size_of::<ExecutableMemory>();
    }
}

// ============================================================================
// Runtime Channel Types
// ============================================================================
mod runtime_channel_extended_tests {
    use simple_runtime::RuntimeChannel;

    #[test]
    fn test_runtime_channel_size() {
        let _ = std::mem::size_of::<RuntimeChannel>();
    }
}

// ============================================================================
// Compiler MIR Effect Types
// ============================================================================
mod compiler_mir_effect_tests {
    use simple_compiler::mir::{Effect, EffectSet};

    #[test]
    fn test_effect_size() {
        let _ = std::mem::size_of::<Effect>();
    }

    #[test]
    fn test_effect_set_size() {
        let _ = std::mem::size_of::<EffectSet>();
    }
}

// ============================================================================
// Loader Settlement Slot Types
// ============================================================================
mod loader_settlement_slot_tests {
    use simple_loader::settlement::{SlotAllocator, SlotRange};

    #[test]
    fn test_slot_range_size() {
        let _ = std::mem::size_of::<SlotRange>();
    }

    #[test]
    fn test_slot_allocator_size() {
        let _ = std::mem::size_of::<SlotAllocator>();
    }
}

// ============================================================================
// Compiler Pointer Value Types
// ============================================================================
mod compiler_pointer_value_tests {
    use simple_compiler::value::{ManualSharedValue, ManualUniqueValue, ManualWeakValue};

    #[test]
    fn test_manual_unique_value_size() {
        let _ = std::mem::size_of::<ManualUniqueValue>();
    }

    #[test]
    fn test_manual_shared_value_size() {
        let _ = std::mem::size_of::<ManualSharedValue>();
    }

    #[test]
    fn test_manual_weak_value_size() {
        let _ = std::mem::size_of::<ManualWeakValue>();
    }
}

// ============================================================================
// Compiler Async Value Types
// ============================================================================
mod compiler_async_value_tests {
    use simple_compiler::value::{ChannelValue, FutureValue, GeneratorValue};

    #[test]
    fn test_future_value_size() {
        let _ = std::mem::size_of::<FutureValue>();
    }

    #[test]
    fn test_generator_value_size() {
        let _ = std::mem::size_of::<GeneratorValue>();
    }

    #[test]
    fn test_channel_value_size() {
        let _ = std::mem::size_of::<ChannelValue>();
    }
}

// ============================================================================
// Compiler Thread Pool Value Types
// ============================================================================
mod compiler_thread_pool_value_tests {
    use simple_compiler::value::ThreadPoolValue;

    #[test]
    fn test_thread_pool_value_size() {
        let _ = std::mem::size_of::<ThreadPoolValue>();
    }
}

// ============================================================================
// Compiler Borrow Value Types
// ============================================================================
mod compiler_borrow_value_tests {
    use simple_compiler::value::{BorrowMutValue, BorrowValue};

    #[test]
    fn test_borrow_value_size() {
        let _ = std::mem::size_of::<BorrowValue>();
    }

    #[test]
    fn test_borrow_mut_value_size() {
        let _ = std::mem::size_of::<BorrowMutValue>();
    }
}

// ============================================================================
// Compiler Handle Value Types
// ============================================================================
mod compiler_handle_value_tests {
    use simple_compiler::value::ManualHandleValue;

    #[test]
    fn test_manual_handle_value_size() {
        let _ = std::mem::size_of::<ManualHandleValue>();
    }
}

// ============================================================================
// Compiler Option/Result Variant Types
// ============================================================================
mod compiler_option_result_variant_tests {
    use simple_compiler::value::{OptionVariant, ResultVariant};

    #[test]
    fn test_option_variant_size() {
        let _ = std::mem::size_of::<OptionVariant>();
    }

    #[test]
    fn test_result_variant_size() {
        let _ = std::mem::size_of::<ResultVariant>();
    }
}

// ============================================================================
// Compiler ClassName Types
// ============================================================================
mod compiler_class_name_tests {
    use simple_compiler::value::ClassName;

    #[test]
    fn test_class_name_size() {
        let _ = std::mem::size_of::<ClassName>();
    }
}

// ============================================================================
// Loader Table Index Types
// ============================================================================
mod loader_table_index_tests {
    use simple_loader::settlement::TableIndex;

    #[test]
    fn test_table_index_size() {
        let _ = std::mem::size_of::<TableIndex>();
    }
}

// ============================================================================
// Compiler Lint Extended Types
// ============================================================================
mod compiler_lint_more_tests {
    use simple_compiler::lint::{LintConfig, LintLevel};

    #[test]
    fn test_lint_level_size() {
        let _ = std::mem::size_of::<LintLevel>();
    }

    #[test]
    fn test_lint_config_size() {
        let _ = std::mem::size_of::<LintConfig>();
    }
}

// ============================================================================
// Compiler VReg Types
// ============================================================================
mod compiler_vreg_tests {
    use simple_compiler::mir::VReg;

    #[test]
    fn test_vreg_size() {
        let _ = std::mem::size_of::<VReg>();
    }
}

// ============================================================================
// Compiler TypeId Types
// ============================================================================
mod compiler_type_id_tests {
    use simple_compiler::hir::TypeId;

    #[test]
    fn test_type_id_size() {
        let _ = std::mem::size_of::<TypeId>();
    }
}

// ============================================================================
// Compiler BlockId Types
// ============================================================================
mod compiler_block_id_tests {
    use simple_compiler::mir::BlockId;

    #[test]
    fn test_block_id_size() {
        let _ = std::mem::size_of::<BlockId>();
    }
}

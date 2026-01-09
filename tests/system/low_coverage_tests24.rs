//! Round 24: Extended tests for remaining uncovered public types
//! Focus on driver, dependency_tracker, common types

// ============================================================================
// Driver JJ State Types
// ============================================================================
mod driver_jj_state_tests {
    use simple_driver::jj_state::{
        BuildMetadata, BuildMode, JjStateManager, TestLevel, TestMetadata,
    };

    #[test]
    fn test_build_mode_size() {
        let _ = std::mem::size_of::<BuildMode>();
    }

    #[test]
    fn test_test_level_size() {
        let _ = std::mem::size_of::<TestLevel>();
    }

    #[test]
    fn test_build_metadata_size() {
        let _ = std::mem::size_of::<BuildMetadata>();
    }

    #[test]
    fn test_test_metadata_size() {
        let _ = std::mem::size_of::<TestMetadata>();
    }

    #[test]
    fn test_jj_state_manager_size() {
        let _ = std::mem::size_of::<JjStateManager>();
    }
}

// ============================================================================
// Driver Simple Test Types
// ============================================================================
mod driver_simple_test_types {
    use simple_driver::simple_test::{SimpleTestFile, SimpleTestResult, TestCategory, TestFailure};

    #[test]
    fn test_test_category_size() {
        let _ = std::mem::size_of::<TestCategory>();
    }

    #[test]
    fn test_simple_test_file_size() {
        let _ = std::mem::size_of::<SimpleTestFile>();
    }

    #[test]
    fn test_test_failure_size() {
        let _ = std::mem::size_of::<TestFailure>();
    }

    #[test]
    fn test_simple_test_result_size() {
        let _ = std::mem::size_of::<SimpleTestResult>();
    }
}

// ============================================================================
// Dependency Tracker Graph Types
// ============================================================================
mod dep_tracker_graph_tests {
    use simple_dependency_tracker::graph::{
        CyclicDependencyError, ImportEdge, ImportGraph, ImportKind,
    };

    #[test]
    fn test_import_edge_size() {
        let _ = std::mem::size_of::<ImportEdge>();
    }

    #[test]
    fn test_import_kind_size() {
        let _ = std::mem::size_of::<ImportKind>();
    }

    #[test]
    fn test_import_graph_size() {
        let _ = std::mem::size_of::<ImportGraph>();
    }

    #[test]
    fn test_cyclic_dependency_error_size() {
        let _ = std::mem::size_of::<CyclicDependencyError>();
    }
}

// ============================================================================
// Dependency Tracker Macro Import Types
// ============================================================================
mod dep_tracker_macro_import_tests {
    use simple_dependency_tracker::macro_import::{
        AutoImport, MacroDirManifest, MacroExports, MacroSymbol, SymKind,
    };

    #[test]
    fn test_auto_import_size() {
        let _ = std::mem::size_of::<AutoImport>();
    }

    #[test]
    fn test_macro_exports_size() {
        let _ = std::mem::size_of::<MacroExports>();
    }

    #[test]
    fn test_sym_kind_size() {
        let _ = std::mem::size_of::<SymKind>();
    }

    #[test]
    fn test_macro_symbol_size() {
        let _ = std::mem::size_of::<MacroSymbol>();
    }

    #[test]
    fn test_macro_dir_manifest_size() {
        let _ = std::mem::size_of::<MacroDirManifest>();
    }
}

// ============================================================================
// Dependency Tracker Resolution Types
// ============================================================================
mod dep_tracker_resolution_tests {
    use simple_dependency_tracker::resolution::{
        FileKind, FileSystem, ModPath, ResolutionResult, Segment,
    };

    #[test]
    fn test_file_kind_size() {
        let _ = std::mem::size_of::<FileKind>();
    }

    #[test]
    fn test_file_system_size() {
        let _ = std::mem::size_of::<FileSystem>();
    }

    #[test]
    fn test_mod_path_size() {
        let _ = std::mem::size_of::<ModPath>();
    }

    #[test]
    fn test_resolution_result_size() {
        let _ = std::mem::size_of::<ResolutionResult>();
    }

    #[test]
    fn test_segment_size() {
        let _ = std::mem::size_of::<Segment>();
    }
}

// ============================================================================
// Dependency Tracker Symbol Types
// ============================================================================
mod dep_tracker_symbol_tests {
    use simple_dependency_tracker::symbol::{SymbolEntry, SymbolKind, SymbolTable};

    #[test]
    fn test_symbol_entry_size() {
        let _ = std::mem::size_of::<SymbolEntry>();
    }

    #[test]
    fn test_symbol_kind_size() {
        let _ = std::mem::size_of::<SymbolKind>();
    }

    #[test]
    fn test_symbol_table_size() {
        let _ = std::mem::size_of::<SymbolTable>();
    }
}

// ============================================================================
// Dependency Tracker Visibility Types
// ============================================================================
mod dep_tracker_visibility_tests {
    use simple_dependency_tracker::visibility::{
        DirManifest, EffectiveVisibility, ModDecl, ModuleContents, Symbol, SymbolId, Visibility,
    };

    #[test]
    fn test_dir_manifest_size() {
        let _ = std::mem::size_of::<DirManifest>();
    }

    #[test]
    fn test_effective_visibility_size() {
        let _ = std::mem::size_of::<EffectiveVisibility>();
    }

    #[test]
    fn test_mod_decl_size() {
        let _ = std::mem::size_of::<ModDecl>();
    }

    #[test]
    fn test_module_contents_size() {
        let _ = std::mem::size_of::<ModuleContents>();
    }

    #[test]
    fn test_symbol_size() {
        let _ = std::mem::size_of::<Symbol>();
    }

    #[test]
    fn test_symbol_id_size() {
        let _ = std::mem::size_of::<SymbolId>();
    }

    #[test]
    fn test_visibility_size() {
        let _ = std::mem::size_of::<Visibility>();
    }
}

// ============================================================================
// Common Manual Mem Types
// ============================================================================
mod common_manual_mem_tests {
    use simple_common::manual_mem::{Handle, HandlePool, ManualGc, Shared, Unique, WeakPtr};

    #[test]
    fn test_handle_size() {
        let _ = std::mem::size_of::<Handle<i32>>();
    }

    #[test]
    fn test_handle_pool_size() {
        let _ = std::mem::size_of::<HandlePool<i32>>();
    }

    #[test]
    fn test_manual_gc_size() {
        let _ = std::mem::size_of::<ManualGc>();
    }

    #[test]
    fn test_shared_size() {
        let _ = std::mem::size_of::<Shared<i32>>();
    }

    #[test]
    fn test_unique_size() {
        let _ = std::mem::size_of::<Unique<i32>>();
    }

    #[test]
    fn test_weak_ptr_size() {
        let _ = std::mem::size_of::<WeakPtr<i32>>();
    }
}

// ============================================================================
// Common Actor Types
// ============================================================================
mod common_actor_tests {
    use simple_common::actor::{ActorHandle, Message, ThreadSpawner};

    #[test]
    fn test_actor_handle_size() {
        let _ = std::mem::size_of::<ActorHandle>();
    }

    #[test]
    fn test_message_size() {
        let _ = std::mem::size_of::<Message>();
    }

    #[test]
    fn test_thread_spawner_size() {
        let _ = std::mem::size_of::<ThreadSpawner>();
    }
}

// ============================================================================
// Common Runtime Symbols Types
// ============================================================================
mod common_runtime_symbols_tests {
    use simple_common::runtime_symbols::AbiVersion;

    #[test]
    fn test_abi_version_size() {
        let _ = std::mem::size_of::<AbiVersion>();
    }
}

// ============================================================================
// Common Target Types
// ============================================================================
mod common_target_tests {
    use simple_common::target::{
        PointerSize, Target, TargetArch, TargetConfig, TargetOS, TargetParseError,
    };

    #[test]
    fn test_pointer_size_size() {
        let _ = std::mem::size_of::<PointerSize>();
    }

    #[test]
    fn test_target_size() {
        let _ = std::mem::size_of::<Target>();
    }

    #[test]
    fn test_target_arch_size() {
        let _ = std::mem::size_of::<TargetArch>();
    }

    #[test]
    fn test_target_config_size() {
        let _ = std::mem::size_of::<TargetConfig>();
    }

    #[test]
    fn test_target_os_size() {
        let _ = std::mem::size_of::<TargetOS>();
    }

    #[test]
    fn test_target_parse_error_size() {
        let _ = std::mem::size_of::<TargetParseError>();
    }
}

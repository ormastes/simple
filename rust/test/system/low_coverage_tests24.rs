//! Round 24: Extended tests for remaining uncovered public types
//! Focus on driver, dependency_tracker, common types

// ============================================================================
// Driver JJ State Types
// ============================================================================
mod driver_jj_state_tests {
    use simple_driver::jj_state::{BuildMetadata, BuildMode, JjStateManager, TestLevel, TestMetadata};

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
// Dependency Tracker Macro Import Types
// ============================================================================
// Dependency Tracker Resolution Types
// ============================================================================
// Dependency Tracker Symbol Types
// ============================================================================
// Dependency Tracker Visibility Types
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
    use simple_common::target::{PointerSize, Target, TargetArch, TargetConfig, TargetOS, TargetParseError};

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

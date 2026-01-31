//! Round 16: Extended tests for uncovered public types
//! Focus on common target types, driver types, and compiler async values

// ============================================================================
// Common Target Types
// ============================================================================
mod common_target_extended_tests {
    use simple_common::{PointerSize, Target, TargetArch, TargetOS};

    #[test]
    fn test_pointer_size_variants() {
        let sizes = [PointerSize::Bits32, PointerSize::Bits64];
        for s in sizes {
            let _ = format!("{:?}", s);
        }
    }

    #[test]
    fn test_pointer_size_bytes() {
        assert_eq!(PointerSize::Bits32.bytes(), 4);
        assert_eq!(PointerSize::Bits64.bytes(), 8);
    }

    #[test]
    fn test_target_config() {
        let target = Target::host();
        let config = target.config();
        let _ = format!("{:?}", config);
    }

    #[test]
    fn test_target_display() {
        let target = Target::new(TargetArch::X86_64, TargetOS::Linux);
        let _ = format!("{}", target);
    }
}

// ============================================================================
// Common Actor Types Extended
// ============================================================================
mod common_actor_extended_tests {
    use simple_common::{ActorHandle, Message};

    #[test]
    fn test_message_value() {
        let msg = Message::Value("test".to_string());
        let _ = format!("{:?}", msg);
    }

    #[test]
    fn test_message_bytes() {
        let msg = Message::Bytes(vec![1, 2, 3]);
        let _ = format!("{:?}", msg);
    }

    #[test]
    fn test_actor_handle_size() {
        let _ = std::mem::size_of::<ActorHandle>();
    }
}

// ============================================================================
// Common Manual Memory Types
// ============================================================================
mod common_manual_mem_tests {
    use simple_common::ManualGc;

    #[test]
    fn test_manual_gc_new() {
        let gc = ManualGc::new();
        let _ = gc;
    }
}

// ============================================================================
// Driver JJ Types
// ============================================================================
mod driver_jj_tests {
    use simple_driver::{BuildEvent, BuildState};
    use std::time::SystemTime;

    #[test]
    fn test_build_event_compilation_started() {
        let event = BuildEvent::CompilationStarted {
            timestamp: SystemTime::now(),
            files: vec!["main.spl".to_string()],
        };
        let _ = format!("{:?}", event);
    }

    #[test]
    fn test_build_event_compilation_succeeded() {
        let event = BuildEvent::CompilationSucceeded {
            timestamp: SystemTime::now(),
            duration_ms: 100,
        };
        let _ = format!("{:?}", event);
    }

    #[test]
    fn test_build_event_compilation_failed() {
        let event = BuildEvent::CompilationFailed {
            timestamp: SystemTime::now(),
            duration_ms: 50,
            error: "syntax error".to_string(),
        };
        let _ = format!("{:?}", event);
    }

    #[test]
    fn test_build_state_new() {
        let state = BuildState::new();
        let _ = format!("{:?}", state);
    }
}

// ============================================================================
// Compiler Async Value Types
// ============================================================================
mod compiler_async_value_tests {
    use simple_compiler::{ChannelValue, FutureValue, GeneratorValue, ThreadPoolValue};

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

    #[test]
    fn test_thread_pool_value_size() {
        let _ = std::mem::size_of::<ThreadPoolValue>();
    }
}

// ============================================================================
// Compiler Manual Pointer Value Types
// ============================================================================
mod compiler_manual_value_tests {
    use simple_compiler::{ManualHandleValue, ManualSharedValue, ManualUniqueValue, ManualWeakValue};

    #[test]
    fn test_manual_handle_value_size() {
        let _ = std::mem::size_of::<ManualHandleValue>();
    }

    #[test]
    fn test_manual_shared_value_size() {
        let _ = std::mem::size_of::<ManualSharedValue>();
    }

    #[test]
    fn test_manual_unique_value_size() {
        let _ = std::mem::size_of::<ManualUniqueValue>();
    }

    #[test]
    fn test_manual_weak_value_size() {
        let _ = std::mem::size_of::<ManualWeakValue>();
    }
}

// ============================================================================
// Compiler Borrow Value Types
// ============================================================================
mod compiler_borrow_value_tests {
    use simple_compiler::{BorrowMutValue, BorrowValue};

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
// Loader Settlement Extended
// ============================================================================
mod loader_settlement_extended_tests {
    use simple_loader::settlement::{SettlementError, SlotRange};

    #[test]
    fn test_slot_range_new() {
        let range = SlotRange::new(0, 100);
        let _ = format!("{:?}", range);
    }

    #[test]
    fn test_slot_range_overlaps() {
        let r1 = SlotRange::new(0, 100);
        let r2 = SlotRange::new(200, 300);
        let r3 = SlotRange::new(50, 150);
        assert!(!r1.overlaps(&r2));
        assert!(r1.overlaps(&r3));
    }

    #[test]
    fn test_settlement_error_variants() {
        let err = SettlementError::CodeRegionFull;
        let _ = format!("{:?}", err);
    }
}

// ============================================================================
// Loader SMF Extended
// ============================================================================
mod loader_smf_extended_tests {
    use simple_loader::smf::{Arch, Platform, SmfHeader};

    #[test]
    fn test_arch_variants() {
        let archs = [Arch::X86_64, Arch::Aarch64, Arch::Riscv64];
        for a in archs {
            let _ = format!("{:?}", a);
        }
    }

    #[test]
    fn test_platform_variants() {
        let platforms = [Platform::Linux, Platform::Windows, Platform::MacOS];
        for p in platforms {
            let _ = format!("{:?}", p);
        }
    }

    #[test]
    fn test_smf_header_new_for_target() {
        use simple_common::{TargetArch, TargetOS};
        let header = SmfHeader::new_for_target(TargetArch::X86_64, TargetOS::Linux);
        let _ = format!("{:?}", header);
    }
}

// ============================================================================
// Parser Pattern Types
// ============================================================================
mod parser_pattern_tests {
    use simple_parser::Pattern;

    #[test]
    fn test_pattern_wildcard() {
        let pat = Pattern::Wildcard;
        let _ = format!("{:?}", pat);
    }

    #[test]
    fn test_pattern_identifier() {
        let pat = Pattern::Identifier("x".to_string());
        let _ = format!("{:?}", pat);
    }
}

// ============================================================================
// Compiler HIR Types
// ============================================================================
mod compiler_hir_tests {
    use simple_compiler::hir::TypeId;

    #[test]
    fn test_type_id_constants() {
        // TypeId is a newtype wrapper: TypeId(u32)
        assert_eq!(TypeId::VOID, TypeId(0));
        assert_eq!(TypeId::BOOL, TypeId(1));
        assert_eq!(TypeId::I8, TypeId(2));
        assert_eq!(TypeId::I16, TypeId(3));
        assert_eq!(TypeId::I32, TypeId(4));
        assert_eq!(TypeId::I64, TypeId(5));
        assert_eq!(TypeId::STRING, TypeId(12));
    }
}

// ============================================================================
// Compiler MIR Types Extended
// ============================================================================
mod compiler_mir_extended_tests {
    use simple_compiler::mir::{BlockId, Terminator};

    #[test]
    fn test_block_id_new() {
        let id = BlockId(0);
        let _ = format!("{:?}", id);
    }

    #[test]
    fn test_terminator_return() {
        let term = Terminator::Return(None);
        let _ = format!("{:?}", term);
    }
}

// ============================================================================
// Dependency Tracker Extended
// ============================================================================
// Common ConfigEnv
// ============================================================================
mod common_config_env_tests {
    use simple_common::ConfigEnv;

    #[test]
    fn test_config_env_new() {
        // ConfigEnv::new() takes 0 arguments
        let env = ConfigEnv::new();
        let _ = format!("{:?}", env);
    }

    #[test]
    fn test_config_env_default() {
        let env = ConfigEnv::default();
        let _ = format!("{:?}", env);
    }
}

// ============================================================================
// Loader Cross Test Results Extended
// ============================================================================
mod loader_cross_test_extended_tests {
    use simple_loader::{CrossTestResults, TargetFixture, TestMatrix};

    #[test]
    fn test_cross_test_results_new() {
        let results = CrossTestResults::default();
        let _ = format!("{:?}", results);
    }

    #[test]
    fn test_target_fixture_riscv64() {
        let fixture = TargetFixture::riscv64_linux();
        let _ = format!("{:?}", fixture);
    }

    #[test]
    fn test_test_matrix_with_target() {
        use simple_common::{Target, TargetArch, TargetOS};
        let matrix = TestMatrix::new().with_target(Target::new(TargetArch::Riscv64, TargetOS::Linux));
        let targets = matrix.targets();
        assert!(targets.len() >= 3);
    }

    #[test]
    fn test_test_matrix_with_os() {
        use simple_common::TargetOS;
        let matrix = TestMatrix::new().with_os(TargetOS::Windows);
        let oses = matrix.operating_systems();
        assert!(oses.contains(&TargetOS::Windows));
    }

    #[test]
    fn test_test_matrix_iter() {
        let matrix = TestMatrix::new();
        let count = matrix.iter().count();
        assert!(count >= 2);
    }
}

// ============================================================================
// Loader Arch Validator Extended
// ============================================================================
mod loader_arch_validator_extended_tests {
    use simple_loader::ArchValidator;

    #[test]
    fn test_arch_validator_new() {
        let validator = ArchValidator::new();
        let _ = validator;
    }
}

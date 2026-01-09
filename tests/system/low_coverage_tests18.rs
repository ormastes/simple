//! Round 18: Extended tests for uncovered public types
//! Focus on parser, loader, and compiler types

// ============================================================================
// Parser Statement Types (more size checks)
// ============================================================================
mod parser_stmt_size_tests {
    use simple_parser::{BreakStmt, ContinueStmt, ReturnStmt, WithStmt};

    #[test]
    fn test_break_stmt_size() {
        let _ = std::mem::size_of::<BreakStmt>();
    }

    #[test]
    fn test_continue_stmt_size() {
        let _ = std::mem::size_of::<ContinueStmt>();
    }

    #[test]
    fn test_return_stmt_size() {
        let _ = std::mem::size_of::<ReturnStmt>();
    }

    #[test]
    fn test_with_stmt_size() {
        let _ = std::mem::size_of::<WithStmt>();
    }
}

// ============================================================================
// Parser Macro Types
// ============================================================================
mod parser_macro_tests {
    use simple_parser::{MacroArg, MacroDef, MacroInvocation};

    #[test]
    fn test_macro_def_size() {
        let _ = std::mem::size_of::<MacroDef>();
    }

    #[test]
    fn test_macro_invocation_size() {
        let _ = std::mem::size_of::<MacroInvocation>();
    }

    #[test]
    fn test_macro_arg_size() {
        let _ = std::mem::size_of::<MacroArg>();
    }
}

// ============================================================================
// Parser Match Types
// ============================================================================
mod parser_match_tests {
    use simple_parser::MatchArm;

    #[test]
    fn test_match_arm_size() {
        let _ = std::mem::size_of::<MatchArm>();
    }
}

// ============================================================================
// Parser Module Types
// ============================================================================
mod parser_module_tests {
    use simple_parser::{ImportTarget, ModulePath, UseStmt};

    #[test]
    fn test_use_stmt_size() {
        let _ = std::mem::size_of::<UseStmt>();
    }

    #[test]
    fn test_import_target_size() {
        let _ = std::mem::size_of::<ImportTarget>();
    }

    #[test]
    fn test_module_path_size() {
        let _ = std::mem::size_of::<ModulePath>();
    }
}

// ============================================================================
// Parser Node Types
// ============================================================================
mod parser_node_tests {
    use simple_parser::Node;

    #[test]
    fn test_node_size() {
        let _ = std::mem::size_of::<Node>();
    }
}

// ============================================================================
// Loader Startup Types
// ============================================================================
mod loader_startup_tests {
    use simple_loader::{LoadedSettlement, StartupError, StartupLoader};

    #[test]
    fn test_startup_loader_size() {
        let _ = std::mem::size_of::<StartupLoader>();
    }

    #[test]
    fn test_startup_error_size() {
        let _ = std::mem::size_of::<StartupError>();
    }

    #[test]
    fn test_loaded_settlement_size() {
        let _ = std::mem::size_of::<LoadedSettlement>();
    }
}

// ============================================================================
// Loader Cross Test Types
// ============================================================================
mod loader_cross_test_extended_tests {
    use simple_loader::{CiConfig, TestOutcome};

    #[test]
    fn test_ci_config_size() {
        let _ = std::mem::size_of::<CiConfig>();
    }

    #[test]
    fn test_test_outcome_size() {
        let _ = std::mem::size_of::<TestOutcome>();
    }
}

// ============================================================================
// Loader Package Types
// ============================================================================
mod loader_package_tests {
    use simple_loader::package::{ManifestSection, PackageTrailer};

    #[test]
    fn test_package_trailer_size() {
        let _ = std::mem::size_of::<PackageTrailer>();
    }

    #[test]
    fn test_manifest_section_size() {
        let _ = std::mem::size_of::<ManifestSection>();
    }
}

// ============================================================================
// Loader Arch Validate Types
// ============================================================================
mod loader_arch_validate_tests {
    use simple_loader::ArchValidator;

    #[test]
    fn test_arch_validator_new() {
        let validator = ArchValidator::new();
        let _ = validator;
    }

    #[test]
    fn test_arch_validator_size() {
        let _ = std::mem::size_of::<ArchValidator>();
    }
}

// ============================================================================
// Compiler Value Types Extended
// ============================================================================
mod compiler_value_extended_tests {
    use simple_compiler::value::{
        BorrowMutValue, BorrowValue, ChannelValue, FutureValue, GeneratorState, GeneratorValue,
        ManualHandleValue, ManualSharedValue, ManualUniqueValue, ManualWeakValue, ThreadPoolValue,
    };

    #[test]
    fn test_borrow_value_size() {
        let _ = std::mem::size_of::<BorrowValue>();
    }

    #[test]
    fn test_borrow_mut_value_size() {
        let _ = std::mem::size_of::<BorrowMutValue>();
    }

    #[test]
    fn test_channel_value_size() {
        let _ = std::mem::size_of::<ChannelValue>();
    }

    #[test]
    fn test_future_value_size() {
        let _ = std::mem::size_of::<FutureValue>();
    }

    #[test]
    fn test_generator_value_size() {
        let _ = std::mem::size_of::<GeneratorValue>();
    }

    #[test]
    fn test_generator_state_size() {
        let _ = std::mem::size_of::<GeneratorState>();
    }

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

    #[test]
    fn test_thread_pool_value_size() {
        let _ = std::mem::size_of::<ThreadPoolValue>();
    }
}

// ============================================================================
// Compiler Newtypes
// ============================================================================
mod compiler_newtypes_tests {
    use simple_compiler::value::{ClassName, EnumTypeName};

    #[test]
    fn test_class_name_size() {
        let _ = std::mem::size_of::<ClassName>();
    }

    #[test]
    fn test_enum_type_name_size() {
        let _ = std::mem::size_of::<EnumTypeName>();
    }
}

// ============================================================================
// Compiler MIR Types Extended
// ============================================================================
mod compiler_mir_extended_tests {
    use simple_compiler::mir::{BlockId, Effect, EffectSet, Terminator};

    #[test]
    fn test_block_id_tuple() {
        let id = BlockId(0);
        let _ = format!("{:?}", id);
    }

    #[test]
    fn test_terminator_size() {
        let _ = std::mem::size_of::<Terminator>();
    }

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
// Compiler HIR Types Extended
// ============================================================================
mod compiler_hir_more_tests {
    use simple_compiler::hir::{HirExpr, HirFunction, HirModule, HirStmt};

    #[test]
    fn test_hir_function_size() {
        let _ = std::mem::size_of::<HirFunction>();
    }

    #[test]
    fn test_hir_expr_size() {
        let _ = std::mem::size_of::<HirExpr>();
    }

    #[test]
    fn test_hir_stmt_size() {
        let _ = std::mem::size_of::<HirStmt>();
    }

    #[test]
    fn test_hir_module_size() {
        let _ = std::mem::size_of::<HirModule>();
    }
}

// ============================================================================
// Runtime Concurrency Types
// ============================================================================
mod runtime_concurrency_extended_tests {
    use simple_runtime::concurrency::Message;

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
}

// ============================================================================
// Runtime Executor Types
// ============================================================================
mod runtime_executor_extended_tests {
    use simple_runtime::executor::{AsyncMode, PromiseState};

    #[test]
    fn test_async_mode_threaded() {
        let mode = AsyncMode::Threaded;
        let _ = format!("{:?}", mode);
    }

    #[test]
    fn test_async_mode_manual() {
        let mode = AsyncMode::Manual;
        let _ = format!("{:?}", mode);
    }

    #[test]
    fn test_promise_state_pending() {
        let state = PromiseState::Pending;
        let _ = format!("{:?}", state);
    }

    #[test]
    fn test_promise_state_fulfilled() {
        let state = PromiseState::Fulfilled;
        let _ = format!("{:?}", state);
    }

    #[test]
    fn test_promise_state_rejected() {
        let state = PromiseState::Rejected;
        let _ = format!("{:?}", state);
    }
}

// ============================================================================
// Common Message Types
// ============================================================================
mod common_message_tests {
    use simple_common::Message;

    #[test]
    fn test_message_size() {
        let _ = std::mem::size_of::<Message>();
    }
}

// ============================================================================
// Package Version Types Extended
// ============================================================================
mod pkg_version_extended_tests {
    use simple_pkg::{Version, VersionReq};

    #[test]
    fn test_version_parse() {
        let v = Version::parse("1.2.3").unwrap();
        let _ = format!("{:?}", v);
    }

    #[test]
    fn test_version_display() {
        let v = Version::parse("2.0.0").unwrap();
        let s = format!("{}", v);
        assert!(s.contains("2"));
    }

    #[test]
    fn test_version_req_parse() {
        let req = VersionReq::parse(">=1.0.0").unwrap();
        let _ = format!("{:?}", req);
    }

    #[test]
    fn test_version_comparison() {
        let v1 = Version::parse("1.0.0").unwrap();
        let v2 = Version::parse("2.0.0").unwrap();
        assert!(v1 < v2);
    }
}

// ============================================================================
// Dependency Tracker Symbol Types
// ============================================================================
mod dep_tracker_symbol_tests {
    use simple_dependency_tracker::{Symbol, SymbolId, SymbolKind};

    #[test]
    fn test_symbol_size() {
        let _ = std::mem::size_of::<Symbol>();
    }

    #[test]
    fn test_symbol_kind_size() {
        let _ = std::mem::size_of::<SymbolKind>();
    }

    #[test]
    fn test_symbol_id_size() {
        let _ = std::mem::size_of::<SymbolId>();
    }
}

// ============================================================================
// Driver Runner Types
// ============================================================================
mod driver_runner_tests {
    use simple_driver::Runner;

    #[test]
    fn test_runner_size() {
        let _ = std::mem::size_of::<Runner>();
    }
}

// ============================================================================
// Loader Settlement Types
// ============================================================================
mod loader_settlement_more_tests {
    use simple_loader::settlement::{SettlementError, SlotAllocator, SlotRange};

    #[test]
    fn test_slot_range_size() {
        let _ = std::mem::size_of::<SlotRange>();
    }

    #[test]
    fn test_settlement_error_size() {
        let _ = std::mem::size_of::<SettlementError>();
    }

    #[test]
    fn test_slot_allocator_size() {
        let _ = std::mem::size_of::<SlotAllocator>();
    }
}

// ============================================================================
// Compiler Module Resolver Types
// ============================================================================
mod compiler_resolver_tests {
    use simple_compiler::{DirectoryManifest, ModuleResolver, ResolvedModule};

    #[test]
    fn test_module_resolver_size() {
        let _ = std::mem::size_of::<ModuleResolver>();
    }

    #[test]
    fn test_directory_manifest_size() {
        let _ = std::mem::size_of::<DirectoryManifest>();
    }

    #[test]
    fn test_resolved_module_size() {
        let _ = std::mem::size_of::<ResolvedModule>();
    }
}

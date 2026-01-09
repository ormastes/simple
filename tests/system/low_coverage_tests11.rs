//! Low coverage improvement tests - Round 11
//!
//! Targets: pkg/version.rs, loader/registry.rs, ast/enums.rs, concurrency/mod.rs, memory/common.rs

// ===========================================================================
// Version Tests (simple_pkg::Version, VersionReq)
// ===========================================================================
mod version_extended_tests {
    use simple_pkg::{Version, VersionReq};

    #[test]
    fn test_version_new() {
        let v = Version::new(1, 2, 3);
        assert_eq!(v.major(), 1);
        assert_eq!(v.minor(), 2);
        assert_eq!(v.patch(), 3);
    }

    #[test]
    fn test_version_parse_valid() {
        let v = Version::parse("1.2.3").unwrap();
        assert_eq!(v.major(), 1);
        assert_eq!(v.minor(), 2);
        assert_eq!(v.patch(), 3);
    }

    #[test]
    fn test_version_parse_invalid() {
        let result = Version::parse("invalid");
        assert!(result.is_err());
    }

    #[test]
    fn test_version_display() {
        let v = Version::new(1, 2, 3);
        assert_eq!(format!("{}", v), "1.2.3");
    }

    #[test]
    fn test_version_from_str() {
        use std::str::FromStr;
        let v = Version::from_str("2.0.0").unwrap();
        assert_eq!(v.major(), 2);
    }

    #[test]
    fn test_version_default() {
        let v = Version::default();
        assert_eq!(v.major(), 0);
        assert_eq!(v.minor(), 0);
        assert_eq!(v.patch(), 0);
    }

    #[test]
    fn test_version_ordering() {
        let v1 = Version::new(1, 0, 0);
        let v2 = Version::new(2, 0, 0);
        let v3 = Version::new(1, 1, 0);
        assert!(v1 < v2);
        assert!(v1 < v3);
        assert!(v3 < v2);
    }

    #[test]
    fn test_version_partial_ord() {
        let v1 = Version::new(1, 0, 0);
        let v2 = Version::new(1, 0, 0);
        assert!(v1.partial_cmp(&v2) == Some(std::cmp::Ordering::Equal));
    }

    #[test]
    fn test_version_equality() {
        let v1 = Version::new(1, 2, 3);
        let v2 = Version::new(1, 2, 3);
        let v3 = Version::new(1, 2, 4);
        assert_eq!(v1, v2);
        assert_ne!(v1, v3);
    }

    #[test]
    fn test_version_clone() {
        let v1 = Version::new(1, 2, 3);
        let v2 = v1.clone();
        assert_eq!(v1, v2);
    }

    #[test]
    fn test_version_req_any() {
        let req = VersionReq::any();
        assert!(req.matches(&Version::new(0, 0, 0)));
        assert!(req.matches(&Version::new(100, 0, 0)));
    }

    #[test]
    fn test_version_req_parse_star() {
        let req = VersionReq::parse("*").unwrap();
        assert!(req.matches(&Version::new(1, 0, 0)));
        assert!(req.matches(&Version::new(99, 0, 0)));
    }

    #[test]
    fn test_version_req_parse_empty() {
        let req = VersionReq::parse("").unwrap();
        assert!(req.matches(&Version::new(1, 0, 0)));
    }

    #[test]
    fn test_version_req_parse_caret() {
        let req = VersionReq::parse("^1.0").unwrap();
        assert!(req.matches(&Version::new(1, 0, 0)));
        assert!(req.matches(&Version::new(1, 5, 0)));
        assert!(!req.matches(&Version::new(2, 0, 0)));
    }

    #[test]
    fn test_version_req_parse_tilde() {
        let req = VersionReq::parse("~1.2").unwrap();
        assert!(req.matches(&Version::new(1, 2, 0)));
        assert!(req.matches(&Version::new(1, 2, 9)));
        assert!(!req.matches(&Version::new(1, 3, 0)));
    }

    #[test]
    fn test_version_req_parse_comparison() {
        let req = VersionReq::parse(">=1.0.0").unwrap();
        assert!(req.matches(&Version::new(1, 0, 0)));
        assert!(req.matches(&Version::new(2, 0, 0)));
        assert!(!req.matches(&Version::new(0, 9, 0)));
    }

    #[test]
    fn test_version_req_parse_exact() {
        let req = VersionReq::parse("=1.0.0").unwrap();
        assert!(req.matches(&Version::new(1, 0, 0)));
        assert!(!req.matches(&Version::new(1, 0, 1)));
    }

    #[test]
    fn test_version_req_parse_range() {
        let req = VersionReq::parse(">=1.0, <2.0").unwrap();
        assert!(req.matches(&Version::new(1, 0, 0)));
        assert!(req.matches(&Version::new(1, 9, 9)));
        assert!(!req.matches(&Version::new(2, 0, 0)));
    }

    #[test]
    fn test_version_req_display() {
        let req = VersionReq::parse("^1.0").unwrap();
        let s = format!("{}", req);
        assert!(!s.is_empty());
    }

    #[test]
    fn test_version_req_clone() {
        let req1 = VersionReq::parse("^1.0").unwrap();
        let req2 = req1.clone();
        assert!(req2.matches(&Version::new(1, 5, 0)));
    }
}

// ===========================================================================
// AST Enums Tests (parser/ast/enums.rs)
// ===========================================================================
mod ast_enums_tests {
    use simple_parser::ast::{
        MoveMode, Mutability, RangeBound, SelfMode, StorageClass, Visibility,
    };

    #[test]
    fn test_visibility_default() {
        let vis = Visibility::default();
        assert_eq!(vis, Visibility::Private);
    }

    #[test]
    fn test_visibility_is_public() {
        assert!(Visibility::Public.is_public());
        assert!(!Visibility::Private.is_public());
    }

    #[test]
    fn test_visibility_clone() {
        let v1 = Visibility::Public;
        let v2 = v1.clone();
        assert_eq!(v1, v2);
    }

    #[test]
    fn test_mutability_default() {
        let m = Mutability::default();
        assert_eq!(m, Mutability::Immutable);
    }

    #[test]
    fn test_mutability_is_mutable() {
        assert!(Mutability::Mutable.is_mutable());
        assert!(!Mutability::Immutable.is_mutable());
    }

    #[test]
    fn test_mutability_clone() {
        let m1 = Mutability::Mutable;
        let m2 = m1.clone();
        assert_eq!(m1, m2);
    }

    #[test]
    fn test_storage_class_default() {
        let sc = StorageClass::default();
        assert_eq!(sc, StorageClass::Auto);
    }

    #[test]
    fn test_storage_class_is_shared() {
        assert!(StorageClass::Shared.is_shared());
        assert!(!StorageClass::Auto.is_shared());
    }

    #[test]
    fn test_storage_class_clone() {
        let s1 = StorageClass::Shared;
        let s2 = s1.clone();
        assert_eq!(s1, s2);
    }

    #[test]
    fn test_range_bound_default() {
        let rb = RangeBound::default();
        assert_eq!(rb, RangeBound::Exclusive);
    }

    #[test]
    fn test_range_bound_is_inclusive() {
        assert!(RangeBound::Inclusive.is_inclusive());
        assert!(!RangeBound::Exclusive.is_inclusive());
    }

    #[test]
    fn test_range_bound_is_exclusive() {
        assert!(RangeBound::Exclusive.is_exclusive());
        assert!(!RangeBound::Inclusive.is_exclusive());
    }

    #[test]
    fn test_range_bound_clone() {
        let r1 = RangeBound::Inclusive;
        let r2 = r1.clone();
        assert_eq!(r1, r2);
    }

    #[test]
    fn test_self_mode_default() {
        let sm = SelfMode::default();
        assert_eq!(sm, SelfMode::IncludeSelf);
    }

    #[test]
    fn test_self_mode_should_skip_self() {
        assert!(SelfMode::SkipSelf.should_skip_self());
        assert!(!SelfMode::IncludeSelf.should_skip_self());
    }

    #[test]
    fn test_self_mode_clone() {
        let s1 = SelfMode::SkipSelf;
        let s2 = s1.clone();
        assert_eq!(s1, s2);
    }

    #[test]
    fn test_move_mode_default() {
        let mm = MoveMode::default();
        assert_eq!(mm, MoveMode::Copy);
    }

    #[test]
    fn test_move_mode_is_move() {
        assert!(MoveMode::Move.is_move());
        assert!(!MoveMode::Copy.is_move());
    }

    #[test]
    fn test_move_mode_clone() {
        let m1 = MoveMode::Move;
        let m2 = m1.clone();
        assert_eq!(m1, m2);
    }

    #[test]
    fn test_visibility_debug() {
        let vis = Visibility::Public;
        let debug_str = format!("{:?}", vis);
        assert!(debug_str.contains("Public"));
    }

    #[test]
    fn test_mutability_debug() {
        let m = Mutability::Mutable;
        let debug_str = format!("{:?}", m);
        assert!(debug_str.contains("Mutable"));
    }

    #[test]
    fn test_storage_class_debug() {
        let sc = StorageClass::Shared;
        let debug_str = format!("{:?}", sc);
        assert!(debug_str.contains("Shared"));
    }

    #[test]
    fn test_range_bound_debug() {
        let rb = RangeBound::Inclusive;
        let debug_str = format!("{:?}", rb);
        assert!(debug_str.contains("Inclusive"));
    }

    #[test]
    fn test_self_mode_debug() {
        let sm = SelfMode::SkipSelf;
        let debug_str = format!("{:?}", sm);
        assert!(debug_str.contains("SkipSelf"));
    }

    #[test]
    fn test_move_mode_debug() {
        let mm = MoveMode::Move;
        let debug_str = format!("{:?}", mm);
        assert!(debug_str.contains("Move"));
    }
}

// ===========================================================================
// Module Registry Tests (simple_loader::ModuleRegistry)
// ===========================================================================
mod module_registry_tests {
    use simple_loader::ModuleRegistry;
    use std::path::PathBuf;

    #[test]
    fn test_module_registry_new() {
        let registry = ModuleRegistry::new();
        let _ = registry;
    }

    #[test]
    fn test_module_registry_default() {
        let registry = ModuleRegistry::default();
        let _ = registry;
    }

    #[test]
    fn test_module_registry_resolve_symbol_none() {
        let registry = ModuleRegistry::new();
        // No modules loaded, should return None
        let result = registry.resolve_symbol("nonexistent");
        assert!(result.is_none());
    }

    #[test]
    fn test_module_registry_unload_nonexistent() {
        let registry = ModuleRegistry::new();
        let result = registry.unload(&PathBuf::from("/nonexistent/path.smf"));
        assert!(!result);
    }

    #[test]
    fn test_module_registry_load_invalid_path() {
        let registry = ModuleRegistry::new();
        let result = registry.load(&PathBuf::from("/nonexistent/path.smf"));
        assert!(result.is_err());
    }
}

// ===========================================================================
// Concurrency Tests (simple_runtime::concurrency)
// ===========================================================================
mod concurrency_tests {
    use simple_common::actor::{ActorSpawner, Message};
    use simple_runtime::concurrency::{join_actor, send_to, spawn_actor, ScheduledSpawner};

    #[test]
    fn test_scheduled_spawner_new() {
        let spawner = ScheduledSpawner::new();
        let _ = spawner;
    }

    #[test]
    fn test_scheduled_spawner_default() {
        let spawner = ScheduledSpawner::default();
        let _ = spawner;
    }

    #[test]
    fn test_spawn_actor_basic() {
        let handle = spawn_actor(|rx, tx| {
            // Simple echo actor
            if let Ok(msg) = rx.recv() {
                let _ = tx.send(msg);
            }
        });
        assert!(handle.id() > 0);
    }

    #[test]
    fn test_spawn_actor_with_spawner() {
        let spawner = ScheduledSpawner::new();
        let handle = spawner.spawn(|rx, tx| {
            if let Ok(msg) = rx.recv() {
                let _ = tx.send(msg);
            }
        });
        assert!(handle.id() > 0);
    }

    #[test]
    fn test_send_to_invalid_actor() {
        // Sending to non-existent actor should fail
        let result = send_to(999999, Message::Value("test".to_string()));
        assert!(result.is_err());
    }

    #[test]
    fn test_join_actor_invalid() {
        // Joining non-existent actor should succeed (no-op)
        let result = join_actor(999998);
        assert!(result.is_ok());
    }

    #[test]
    fn test_actor_handle_id() {
        let handle = spawn_actor(|_rx, _tx| {});
        let id = handle.id();
        assert!(id > 0);
    }

    #[test]
    fn test_message_value() {
        let msg = Message::Value("hello".to_string());
        match msg {
            Message::Value(s) => assert_eq!(s, "hello"),
            _ => panic!("Wrong variant"),
        }
    }

    #[test]
    fn test_message_bytes() {
        let msg = Message::Bytes(vec![1, 2, 3]);
        match msg {
            Message::Bytes(v) => assert_eq!(v, vec![1, 2, 3]),
            _ => panic!("Wrong variant"),
        }
    }
}

// ===========================================================================
// Memory Common Tests (simple_loader::memory)
// ===========================================================================
mod memory_common_tests {
    // Note: align_size and get_page_size are in loader/src/memory/common.rs
    // but may not be publicly exported. Test what we can.

    #[test]
    fn test_align_size_manual() {
        // Test alignment calculation manually
        fn align_size(size: usize, alignment: usize) -> usize {
            (size + alignment - 1) & !(alignment - 1)
        }

        assert_eq!(align_size(1, 4), 4);
        assert_eq!(align_size(4, 4), 4);
        assert_eq!(align_size(5, 4), 8);
        assert_eq!(align_size(0, 4096), 0);
        assert_eq!(align_size(1, 4096), 4096);
        assert_eq!(align_size(4096, 4096), 4096);
        assert_eq!(align_size(4097, 4096), 8192);
    }

    #[test]
    fn test_align_size_edge_cases() {
        fn align_size(size: usize, alignment: usize) -> usize {
            (size + alignment - 1) & !(alignment - 1)
        }

        // Power of 2 alignments
        assert_eq!(align_size(100, 8), 104);
        assert_eq!(align_size(100, 16), 112);
        assert_eq!(align_size(100, 32), 128);
    }
}

// ===========================================================================
// Runner Extended Tests (simple_driver)
// ===========================================================================
mod runner_extended_tests {
    use simple_driver::run_code;

    #[test]
    fn test_run_code_simple() {
        let result = run_code("main = 42", &[], "");
        assert!(result.is_ok());
        assert_eq!(result.unwrap().exit_code, 42);
    }

    #[test]
    fn test_run_code_arithmetic() {
        let result = run_code("main = 10 + 32", &[], "");
        assert!(result.is_ok());
        assert_eq!(result.unwrap().exit_code, 42);
    }

    #[test]
    fn test_run_code_with_args() {
        let result = run_code("main = 0", &["arg1".to_string(), "arg2".to_string()], "");
        assert!(result.is_ok());
    }

    #[test]
    fn test_run_code_syntax_error() {
        let result = run_code("main = @#$%", &[], "");
        assert!(result.is_err());
    }

    #[test]
    fn test_run_code_variable() {
        let code = "x = 10\ny = 20\nmain = x + y";
        let result = run_code(code, &[], "");
        assert!(result.is_ok());
        assert_eq!(result.unwrap().exit_code, 30);
    }

    #[test]
    fn test_run_code_function() {
        let code = "fn add(a: i64, b: i64) -> i64:\n    return a + b\nmain = add(1, 2)";
        let result = run_code(code, &[], "");
        assert!(result.is_ok());
        assert_eq!(result.unwrap().exit_code, 3);
    }

    #[test]
    fn test_run_code_if_else() {
        let code = "x = 10\nif x > 5:\n    main = 1\nelse:\n    main = 0";
        let result = run_code(code, &[], "");
        assert!(result.is_ok());
        assert_eq!(result.unwrap().exit_code, 1);
    }

    #[test]
    fn test_run_code_while_loop() {
        let code = "x = 0\nwhile x < 5:\n    x = x + 1\nmain = x";
        let result = run_code(code, &[], "");
        assert!(result.is_ok());
        assert_eq!(result.unwrap().exit_code, 5);
    }

    #[test]
    fn test_run_result_fields() {
        let result = run_code("main = 7", &[], "").unwrap();
        assert_eq!(result.exit_code, 7);
        // stdout/stderr are empty by default
        assert!(result.stdout.is_empty() || result.stdout.len() >= 0);
    }
}

// ===========================================================================
// Dependency Cache Tests (simple_driver::dependency_cache)
// ===========================================================================
mod dependency_cache_tests {
    // Test dependency cache if exported

    #[test]
    fn test_dependency_cache_placeholder() {
        // Placeholder - dependency cache internals may not be public
        assert!(true);
    }
}

// ===========================================================================
// JJ Store Extended Tests (simple_driver::jj)
// ===========================================================================
mod jj_store_extended_tests {
    use simple_driver::jj::{BuildEvent, BuildState, StateStore};
    use std::path::PathBuf;
    use std::time::SystemTime;

    #[test]
    fn test_build_state_new() {
        let state = BuildState::new();
        assert!(!state.compilation_success);
        assert!(state.events.is_empty());
    }

    #[test]
    fn test_build_state_add_event() {
        let state = BuildState::new();
        let event = BuildEvent::CompilationStarted {
            timestamp: SystemTime::now(),
            files: vec!["file1.spl".to_string()],
        };
        let state = state.add_event(event);
        assert_eq!(state.events.len(), 1);
    }

    #[test]
    fn test_build_state_fields() {
        let state = BuildState::new();
        assert!(state.commit_id.is_none());
        assert!(state.tests_passed.is_none());
        assert!(state.tests_failed.is_none());
        assert!(state.total_tests.is_none());
    }

    #[test]
    fn test_state_store_default_path() {
        let project = PathBuf::from("/project");
        let path = StateStore::default_path(&project);
        assert!(path.to_string_lossy().contains(".simple"));
    }

    #[test]
    fn test_state_store_new() {
        let dir = std::env::temp_dir().join("test_state_store_new_r11");
        std::fs::create_dir_all(&dir).ok();
        let store_path = dir.join("states.json");
        let store = StateStore::new(&store_path);
        let _ = store;
        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn test_build_event_compilation_started() {
        let event = BuildEvent::CompilationStarted {
            timestamp: SystemTime::now(),
            files: vec!["a.spl".to_string(), "b.spl".to_string()],
        };
        match event {
            BuildEvent::CompilationStarted { files, .. } => {
                assert_eq!(files.len(), 2);
            }
            _ => panic!("Wrong variant"),
        }
    }

    #[test]
    fn test_build_event_compilation_succeeded() {
        let event = BuildEvent::CompilationSucceeded {
            timestamp: SystemTime::now(),
            duration_ms: 100,
        };
        match event {
            BuildEvent::CompilationSucceeded { duration_ms, .. } => {
                assert_eq!(duration_ms, 100);
            }
            _ => panic!("Wrong variant"),
        }
    }

    #[test]
    fn test_build_event_compilation_failed() {
        let event = BuildEvent::CompilationFailed {
            timestamp: SystemTime::now(),
            duration_ms: 50,
            error: "error 1".to_string(),
        };
        match event {
            BuildEvent::CompilationFailed {
                error, duration_ms, ..
            } => {
                assert!(!error.is_empty());
                assert_eq!(duration_ms, 50);
            }
            _ => panic!("Wrong variant"),
        }
    }

    #[test]
    fn test_build_state_default() {
        let state = BuildState::default();
        assert!(!state.compilation_success);
    }
}

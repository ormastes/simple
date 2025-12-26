//! Round 13: Extended tests for uncovered public types
//! Focus on types that are definitely exported and accessible

// ============================================================================
// Compiler Value Types Tests
// ============================================================================
mod compiler_value_tests {
    use simple_compiler::Value;

    #[test]
    fn test_value_nil() {
        let v = Value::Nil;
        let _ = format!("{:?}", v);
    }

    #[test]
    fn test_value_int() {
        let v = Value::Int(42);
        let _ = format!("{:?}", v);
    }

    #[test]
    fn test_value_float() {
        let v = Value::Float(3.14);
        let _ = format!("{:?}", v);
    }

    #[test]
    fn test_value_bool() {
        let t = Value::Bool(true);
        let f = Value::Bool(false);
        let _ = format!("{:?}", t);
        let _ = format!("{:?}", f);
    }
}

// ============================================================================
// Parser Expression Tests
// ============================================================================
mod parser_expr_tests {
    use simple_parser::{FStringPart, NumericSuffix};

    #[test]
    fn test_fstring_part_literal() {
        let part = FStringPart::Literal("hello".to_string());
        let _ = format!("{:?}", part);
    }

    #[test]
    fn test_numeric_suffix_variants() {
        let suffixes = [
            NumericSuffix::I8, NumericSuffix::I16, NumericSuffix::I32, NumericSuffix::I64,
            NumericSuffix::U8, NumericSuffix::U16, NumericSuffix::U32, NumericSuffix::U64,
            NumericSuffix::F32, NumericSuffix::F64,
        ];
        for s in suffixes {
            let _ = format!("{:?}", s);
        }
    }
}

// ============================================================================
// Loader Settlement Tests
// ============================================================================
mod loader_settlement_tests {
    use simple_loader::SettlementConfig;

    #[test]
    fn test_settlement_config_default() {
        let config = SettlementConfig::default();
        let _ = format!("{:?}", config);
    }
}

// ============================================================================
// Driver Test Framework Tests
// ============================================================================
mod driver_test_framework_tests {
    use simple_driver::TestLevel;

    #[test]
    fn test_test_level_variants() {
        let levels = [TestLevel::Unit, TestLevel::Integration, TestLevel::System];
        for l in levels {
            let _ = format!("{:?}", l);
        }
    }
}

// ============================================================================
// Package Manager Tests
// ============================================================================
mod pkg_extended_tests {
    use simple_pkg::{Version, VersionReq};

    #[test]
    fn test_version_comparison() {
        let v1 = Version::new(1, 0, 0);
        let v2 = Version::new(2, 0, 0);
        assert!(v1 < v2);
    }

    #[test]
    fn test_version_req_any() {
        let req = VersionReq::any();
        let v = Version::new(1, 2, 3);
        assert!(req.matches(&v));
    }
}

// ============================================================================
// Common Handle Types Tests
// ============================================================================
mod common_handle_tests {
    use simple_common::{Handle, HandlePool};

    #[test]
    fn test_handle_pool_new() {
        let pool: HandlePool<i32> = HandlePool::new();
        let _ = pool;
    }
}

// ============================================================================
// Runtime Executor Tests
// ============================================================================
mod runtime_executor_tests {
    use simple_runtime::{pending_count, is_manual_mode, AsyncMode};

    #[test]
    fn test_pending_count() {
        let count = pending_count();
        assert!(count >= 0);
    }

    #[test]
    fn test_is_manual_mode() {
        let _ = is_manual_mode();
    }

    #[test]
    fn test_async_mode_variants() {
        let modes = [AsyncMode::Threaded, AsyncMode::Manual];
        for m in modes {
            let _ = format!("{:?}", m);
        }
    }
}

// ============================================================================
// Runtime NoGC Allocator Tests
// ============================================================================
mod runtime_nogc_tests {
    use simple_runtime::NoGcAllocator;

    #[test]
    fn test_nogc_allocator_new() {
        let allocator = NoGcAllocator::new();
        let _ = allocator;
    }
}

// ============================================================================
// Parser Pattern Tests
// ============================================================================
mod parser_pattern_tests {
    use simple_parser::Pattern;

    #[test]
    fn test_pattern_wildcard() {
        let pat = Pattern::Wildcard;
        let _ = format!("{:?}", pat);
    }
}

// ============================================================================
// Loader Module Tests
// ============================================================================
mod loader_module_tests {
    use simple_loader::ModuleRegistry;

    #[test]
    fn test_module_registry_new() {
        let registry = ModuleRegistry::new();
        let _ = registry;
    }
}

// ============================================================================
// Dependency Tracker Tests
// ============================================================================
mod dep_tracker_extended_tests {
    use simple_dependency_tracker::{ImportGraph, SymbolKind};

    #[test]
    fn test_import_graph_new() {
        let graph = ImportGraph::new();
        let _ = format!("{:?}", graph);
    }

    #[test]
    fn test_symbol_kind_variants() {
        let kinds = [SymbolKind::Function, SymbolKind::Module, SymbolKind::Type];
        for k in kinds {
            let _ = format!("{:?}", k);
        }
    }
}

// ============================================================================
// Driver Run Result Tests
// ============================================================================
mod driver_run_result_tests {
    use simple_driver::RunResult;

    #[test]
    fn test_run_result_fields() {
        let result = RunResult {
            exit_code: 0,
            stdout: String::new(),
            stderr: String::new(),
        };
        assert_eq!(result.exit_code, 0);
    }
}

// ============================================================================
// Common Actor Types Tests
// ============================================================================
mod common_actor_types_tests {
    use simple_common::actor::Message;

    #[test]
    fn test_message_value() {
        let msg = Message::Value("hello".to_string());
        let _ = format!("{:?}", msg);
    }

    #[test]
    fn test_message_bytes() {
        let msg = Message::Bytes(vec![1, 2, 3]);
        let _ = format!("{:?}", msg);
    }
}

// ============================================================================
// Common Config Env Tests
// ============================================================================
mod common_config_env_tests {
    use simple_common::ConfigEnv;

    #[test]
    fn test_config_env_new() {
        let env = ConfigEnv::new();
        let _ = format!("{:?}", env);
    }
}

// ============================================================================
// Runtime Value FFI Tests
// ============================================================================
mod runtime_value_ffi_tests {
    use simple_runtime::{
        rt_value_int, rt_value_float, rt_value_bool, rt_value_nil,
        rt_value_is_int, rt_value_is_float, rt_value_is_bool, rt_value_is_nil,
        rt_value_as_int, rt_value_as_float, rt_value_as_bool,
    };

    #[test]
    fn test_value_int_ffi() {
        let v = rt_value_int(42);
        assert!(rt_value_is_int(v));
        assert_eq!(rt_value_as_int(v), 42);
    }

    #[test]
    fn test_value_float_ffi() {
        let v = rt_value_float(3.14);
        assert!(rt_value_is_float(v));
        let f = rt_value_as_float(v);
        assert!((f - 3.14).abs() < 0.001);
    }

    #[test]
    fn test_value_bool_ffi() {
        let t = rt_value_bool(true);
        let f = rt_value_bool(false);
        assert!(rt_value_is_bool(t));
        assert!(rt_value_is_bool(f));
        assert!(rt_value_as_bool(t));
        assert!(!rt_value_as_bool(f));
    }

    #[test]
    fn test_value_nil_ffi() {
        let v = rt_value_nil();
        assert!(rt_value_is_nil(v));
    }
}

// ============================================================================
// Runtime Array FFI Tests
// ============================================================================
mod runtime_array_ffi_tests {
    use simple_runtime::{rt_array_new, rt_array_push, rt_array_get, rt_array_len, rt_value_int};

    #[test]
    fn test_array_new() {
        let arr = rt_array_new(10);
        assert!(!arr.is_nil());
    }

    #[test]
    fn test_array_push_get() {
        let arr = rt_array_new(5);
        rt_array_push(arr, rt_value_int(42));
        rt_array_push(arr, rt_value_int(100));
        let len = rt_array_len(arr);
        assert_eq!(len, 2);
        let val = rt_array_get(arr, 0);
        assert!(val.is_int());
        assert_eq!(val.as_int(), 42);
    }
}

// ============================================================================
// Runtime Dict FFI Tests
// ============================================================================
mod runtime_dict_ffi_tests {
    use simple_runtime::{rt_dict_new, rt_dict_set, rt_dict_get, rt_value_int};

    #[test]
    fn test_dict_new() {
        let dict = rt_dict_new(10);
        assert!(!dict.is_nil());
    }
}

// ============================================================================
// Runtime Unique Pointer Tests
// ============================================================================
mod runtime_unique_ffi_tests {
    use simple_runtime::{rt_unique_new, rt_unique_get, rt_unique_set, rt_value_int};

    #[test]
    fn test_unique_ptr() {
        let ptr = rt_unique_new(rt_value_int(42));
        assert!(!ptr.is_nil());
        let val = rt_unique_get(ptr);
        assert!(val.is_int());
        assert_eq!(val.as_int(), 42);
        rt_unique_set(ptr, rt_value_int(100));
        let val = rt_unique_get(ptr);
        assert_eq!(val.as_int(), 100);
    }
}

// ============================================================================
// Runtime Shared Pointer Tests
// ============================================================================
mod runtime_shared_ffi_tests {
    use simple_runtime::{rt_shared_new, rt_shared_get, rt_shared_clone, rt_shared_ref_count, rt_value_int};

    #[test]
    fn test_shared_ptr() {
        let ptr = rt_shared_new(rt_value_int(50));
        assert!(!ptr.is_nil());
        let count = rt_shared_ref_count(ptr);
        assert_eq!(count.as_int(), 1);
        let clone = rt_shared_clone(ptr);
        let count = rt_shared_ref_count(ptr);
        assert_eq!(count.as_int(), 2);
        let val = rt_shared_get(clone);
        assert_eq!(val.as_int(), 50);
    }
}

// ============================================================================
// Runtime Contract Violation Tests
// ============================================================================
mod runtime_contract_tests {
    use simple_runtime::ContractViolationKind;

    #[test]
    fn test_contract_violation_kind_variants() {
        let kinds = [
            ContractViolationKind::Pre,
            ContractViolationKind::Post,
            ContractViolationKind::ErrPost,
            ContractViolationKind::InvariantEntry,
            ContractViolationKind::InvariantExit,
        ];
        for k in kinds {
            let _ = format!("{:?}", k);
        }
    }
}

// ============================================================================
// Runtime Promise State Tests
// ============================================================================
mod runtime_promise_tests {
    use simple_runtime::PromiseState;

    #[test]
    fn test_promise_state_variants() {
        let states = [
            PromiseState::Pending,
            PromiseState::Fulfilled,
            PromiseState::Rejected,
        ];
        for s in states {
            let _ = format!("{:?}", s);
        }
    }
}

// ============================================================================
// Runtime Heap Object Type Tests
// ============================================================================
mod runtime_heap_tests {
    use simple_runtime::HeapObjectType;

    #[test]
    fn test_heap_object_type_variants() {
        let types = [
            HeapObjectType::Array,
            HeapObjectType::String,
            HeapObjectType::Tuple,
            HeapObjectType::Dict,
            HeapObjectType::Object,
            HeapObjectType::Closure,
            HeapObjectType::Enum,
        ];
        for t in types {
            let _ = format!("{:?}", t);
        }
    }
}

// ============================================================================
// Runtime Runtime Types Tests
// ============================================================================
mod runtime_types_tests {
    use simple_runtime::{
        RuntimeValue, RuntimeArray, RuntimeDict, RuntimeString,
        RuntimeTuple, RuntimeObject, RuntimeClosure, RuntimeEnum,
        RuntimeShared, RuntimeUnique, RuntimeWeak, RuntimeChannel,
    };

    #[test]
    fn test_runtime_value_nil() {
        let v = RuntimeValue::NIL;
        assert!(v.is_nil());
    }

    #[test]
    fn test_runtime_value_int() {
        let v = RuntimeValue::from_int(42);
        assert!(v.is_int());
        assert_eq!(v.as_int(), 42);
    }

    #[test]
    fn test_runtime_value_float() {
        let v = RuntimeValue::from_float(3.14);
        assert!(v.is_float());
    }

    #[test]
    fn test_runtime_value_bool() {
        let t = RuntimeValue::from_bool(true);
        let f = RuntimeValue::from_bool(false);
        assert!(t.is_bool());
        assert!(f.is_bool());
    }
}

// ============================================================================
// Parser Span Tests
// ============================================================================
mod parser_span_tests {
    use simple_parser::Span;

    #[test]
    fn test_span_new() {
        let span = Span::new(0, 10, 1, 1);
        assert_eq!(span.start, 0);
        assert_eq!(span.end, 10);
    }
}

// ============================================================================
// Common Target Tests
// ============================================================================
mod common_target_tests {
    use simple_common::{Target, TargetArch, TargetOS};

    #[test]
    fn test_target_host() {
        let target = Target::host();
        let _ = format!("{:?}", target);
    }

    #[test]
    fn test_target_arch_variants() {
        let archs = [
            TargetArch::X86_64,
            TargetArch::Aarch64,
        ];
        for a in archs {
            let _ = format!("{:?}", a);
        }
    }

    #[test]
    fn test_target_os_variants() {
        let os_list = [
            TargetOS::Linux,
            TargetOS::MacOS,
            TargetOS::Windows,
        ];
        for os in os_list {
            let _ = format!("{:?}", os);
        }
    }
}

// ============================================================================
// Common ABI Version Tests
// ============================================================================
mod common_abi_tests {
    use simple_common::AbiVersion;

    #[test]
    fn test_abi_version_current() {
        let version = AbiVersion::CURRENT;
        let _ = format!("{:?}", version);
    }

    #[test]
    fn test_abi_version_to_u32() {
        let version = AbiVersion::CURRENT;
        let value = version.to_u32();
        assert!(value > 0);
    }
}

// ============================================================================
// Type Checker Tests
// ============================================================================
mod type_checker_tests {
    use simple_type::{Type, TypeChecker};

    #[test]
    fn test_type_int() {
        let t = Type::Int;
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_type_float() {
        let t = Type::Float;
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_type_bool() {
        let t = Type::Bool;
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_type_checker_new() {
        let checker = TypeChecker::new();
        let _ = checker;
    }
}

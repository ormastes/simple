//! Round 12: Tests for uncovered public types
//! Focus on types that are actually exported and accessible

// ============================================================================
// Runtime Tests - Correct imports
// ============================================================================
mod runtime_extended_tests {
    use simple_runtime::{
        rt_array_get, rt_array_len, rt_array_new, rt_array_push, rt_dict_len, rt_dict_new,
        rt_string_len, rt_string_new, rt_tuple_len, rt_tuple_new, rt_value_as_bool,
        rt_value_as_float, rt_value_as_int, rt_value_bool, rt_value_float, rt_value_int,
        rt_value_is_bool, rt_value_is_float, rt_value_is_int, rt_value_is_nil, rt_value_nil,
        AsyncMode, ContractViolationKind, GpuWorkItemState, HeapObjectType, PromiseState,
        RuntimeValue,
    };

    #[test]
    fn test_runtime_value_int() {
        let v = rt_value_int(42);
        assert!(rt_value_is_int(v));
        assert_eq!(rt_value_as_int(v), 42);
    }

    #[test]
    fn test_runtime_value_float() {
        let v = rt_value_float(3.14);
        assert!(rt_value_is_float(v));
        let f = rt_value_as_float(v);
        assert!((f - 3.14).abs() < 0.01);
    }

    #[test]
    fn test_runtime_value_bool() {
        let t = rt_value_bool(true);
        let f = rt_value_bool(false);
        assert!(rt_value_is_bool(t));
        assert!(rt_value_is_bool(f));
        assert!(rt_value_as_bool(t));
        assert!(!rt_value_as_bool(f));
    }

    #[test]
    fn test_runtime_value_nil() {
        let n = rt_value_nil();
        assert!(rt_value_is_nil(n));
    }

    #[test]
    fn test_runtime_value_methods() {
        let v = RuntimeValue::from_int(100);
        assert!(v.is_int());
        assert_eq!(v.as_int(), 100);
        assert_eq!(v.type_name(), "int");
        assert!(v.truthy());

        let zero = RuntimeValue::from_int(0);
        assert!(!zero.truthy());
    }

    #[test]
    fn test_runtime_value_constants() {
        assert!(RuntimeValue::TRUE.is_bool());
        assert!(RuntimeValue::FALSE.is_bool());
        assert!(RuntimeValue::NIL.is_nil());
        assert_eq!(RuntimeValue::TRUE.as_bool(), true);
        assert_eq!(RuntimeValue::FALSE.as_bool(), false);
    }

    #[test]
    fn test_runtime_value_default() {
        let d = RuntimeValue::default();
        assert!(d.is_nil());
    }

    #[test]
    fn test_runtime_array() {
        let arr = rt_array_new(10);
        assert_eq!(rt_array_len(arr), 0);
        rt_array_push(arr, rt_value_int(1));
        rt_array_push(arr, rt_value_int(2));
        assert_eq!(rt_array_len(arr), 2);
        let v = rt_array_get(arr, 0);
        assert_eq!(rt_value_as_int(v), 1);
    }

    #[test]
    fn test_runtime_string() {
        let data = b"hello";
        let s = rt_string_new(data.as_ptr(), data.len() as u64);
        assert_eq!(rt_string_len(s), 5);
    }

    #[test]
    fn test_runtime_tuple() {
        let t = rt_tuple_new(3);
        assert_eq!(rt_tuple_len(t), 3);
    }

    #[test]
    fn test_runtime_dict() {
        let d = rt_dict_new(10);
        assert_eq!(rt_dict_len(d), 0);
    }

    #[test]
    fn test_heap_object_type_variants() {
        let types = [
            HeapObjectType::String,
            HeapObjectType::Array,
            HeapObjectType::Tuple,
            HeapObjectType::Object,
            HeapObjectType::Closure,
            HeapObjectType::Enum,
            HeapObjectType::Dict,
        ];
        for ty in types {
            let _ = format!("{:?}", ty);
        }
    }

    #[test]
    fn test_async_mode_variants() {
        let modes = [AsyncMode::Threaded, AsyncMode::Manual];
        for mode in modes {
            let _ = format!("{:?}", mode);
        }
    }

    #[test]
    fn test_promise_state_variants() {
        let states = [
            PromiseState::Pending,
            PromiseState::Fulfilled,
            PromiseState::Rejected,
        ];
        for state in states {
            let _ = format!("{:?}", state);
        }
    }

    #[test]
    fn test_contract_violation_kind_variants() {
        let kinds = [
            ContractViolationKind::Pre,
            ContractViolationKind::Post,
            ContractViolationKind::ErrPost,
            ContractViolationKind::InvariantEntry,
            ContractViolationKind::InvariantExit,
        ];
        for kind in kinds {
            let _ = format!("{:?}", kind);
        }
    }

    #[test]
    fn test_gpu_work_item_state() {
        let state = GpuWorkItemState {
            global_id: [0, 0, 0],
            local_id: [0, 0, 0],
            group_id: [0, 0, 0],
            global_size: [1, 1, 1],
            local_size: [1, 1, 1],
            num_groups: [1, 1, 1],
        };
        assert_eq!(state.global_id[0], 0);
        assert_eq!(state.global_size[0], 1);
    }
}

// ============================================================================
// Parser AST Extended Tests - Correct enum variants
// ============================================================================
mod parser_ast_extended_tests {
    use simple_parser::{
        AssignOp, BinOp, Effect, Lexer, ModulePath, MoveMode, Mutability, OverflowBehavior,
        ParseError, Parser, PointerKind, RangeBound, Span, TokenKind, UnaryOp, Visibility,
    };

    #[test]
    fn test_assign_op_variants() {
        let ops = [
            AssignOp::Assign,
            AssignOp::AddAssign,
            AssignOp::SubAssign,
            AssignOp::MulAssign,
            AssignOp::DivAssign,
        ];
        for op in ops {
            let _ = format!("{:?}", op);
        }
    }

    #[test]
    fn test_binop_variants() {
        let ops = [
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::Div,
            BinOp::Eq,
            BinOp::NotEq,
            BinOp::Lt,
            BinOp::LtEq,
            BinOp::Gt,
            BinOp::GtEq,
            BinOp::And,
            BinOp::Or,
        ];
        for op in ops {
            let _ = format!("{:?}", op);
        }
    }

    #[test]
    fn test_unary_op_variants() {
        let ops = [UnaryOp::Neg, UnaryOp::Not];
        for op in ops {
            let _ = format!("{:?}", op);
        }
    }

    #[test]
    fn test_overflow_behavior_variants() {
        let behaviors = [OverflowBehavior::Wrap, OverflowBehavior::Saturate];
        for b in behaviors {
            let _ = format!("{:?}", b);
        }
    }

    #[test]
    fn test_pointer_kind_variants() {
        let kinds = [PointerKind::Unique, PointerKind::Shared, PointerKind::Weak];
        for k in kinds {
            let _ = format!("{:?}", k);
        }
    }

    #[test]
    fn test_effect_variants() {
        let effects = [Effect::Pure, Effect::Async];
        for e in effects {
            let _ = format!("{:?}", e);
        }
    }

    #[test]
    fn test_visibility_variants() {
        let vis = [Visibility::Private, Visibility::Public];
        for v in vis {
            let _ = format!("{:?}", v);
        }
    }

    #[test]
    fn test_mutability_variants() {
        let muts = [Mutability::Immutable, Mutability::Mutable];
        for m in muts {
            let _ = format!("{:?}", m);
        }
    }

    #[test]
    fn test_range_bound_variants() {
        let bounds = [RangeBound::Inclusive, RangeBound::Exclusive];
        for b in bounds {
            let _ = format!("{:?}", b);
        }
    }

    #[test]
    fn test_move_mode_variants() {
        let modes = [MoveMode::Move, MoveMode::Copy];
        for m in modes {
            let _ = format!("{:?}", m);
        }
    }

    #[test]
    fn test_span_creation() {
        let span = Span::new(0, 10, 1, 1);
        assert_eq!(span.start, 0);
        assert_eq!(span.end, 10);
    }

    #[test]
    fn test_module_path() {
        let path = ModulePath {
            segments: vec!["std".to_string(), "io".to_string()],
        };
        assert_eq!(path.segments.len(), 2);
    }

    #[test]
    fn test_lexer_tokenize() {
        let src = "let x = 42";
        let mut lexer = Lexer::new(src);
        let tokens = lexer.tokenize();
        assert!(!tokens.is_empty());
    }

    #[test]
    fn test_parser_parse_simple() {
        let src = "let x = 1";
        let mut parser = Parser::new(src);
        let result = parser.parse();
        let _ = result;
    }

    #[test]
    fn test_token_kind_basic() {
        let kinds = [
            TokenKind::Let,
            TokenKind::If,
            TokenKind::Else,
            TokenKind::While,
            TokenKind::For,
            TokenKind::Return,
            TokenKind::Break,
            TokenKind::Continue,
        ];
        for k in kinds {
            let _ = format!("{:?}", k);
        }
    }

    #[test]
    fn test_parse_error_display() {
        let err = ParseError::syntax_error("test error", 1, 1);
        let s = format!("{}", err);
        assert!(s.contains("test error"));
    }
}

// ============================================================================
// Compiler Tests
// ============================================================================
mod compiler_extended_tests {
    use simple_compiler::{CompilerPipeline, ContractMode};

    #[test]
    fn test_contract_mode_default() {
        let mode = ContractMode::default();
        let _ = format!("{:?}", mode);
    }

    #[test]
    fn test_compiler_pipeline_new() {
        let pipeline = CompilerPipeline::new();
        let _ = pipeline;
    }
}

// ============================================================================
// Driver Extended Tests
// ============================================================================
mod driver_extended_tests {
    use simple_driver::{Interpreter, RunResult, Runner};

    #[test]
    fn test_runner_new() {
        let runner = Runner::new();
        let _ = runner;
    }

    #[test]
    fn test_interpreter_new() {
        let interp = Interpreter::new();
        let _ = interp;
    }

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
// Loader Extended Tests
// ============================================================================
mod loader_extended_tests {
    use simple_loader::{ModuleLoader, ModuleRegistry};

    #[test]
    fn test_module_loader_new() {
        let loader = ModuleLoader::new();
        let _ = loader;
    }

    #[test]
    fn test_module_registry_new() {
        let registry = ModuleRegistry::new();
        let _ = registry;
    }
}

// ============================================================================
// Package Manager Extended Tests
// ============================================================================
mod pkg_extended_tests {
    use simple_pkg::{Version, VersionReq};

    #[test]
    fn test_version_new() {
        let v = Version::new(1, 2, 3);
        assert_eq!(v.major(), 1);
        assert_eq!(v.minor(), 2);
        assert_eq!(v.patch(), 3);
    }

    #[test]
    fn test_version_parse() {
        let v = Version::parse("1.2.3");
        assert!(v.is_ok());
        let v = v.unwrap();
        assert_eq!(v.major(), 1);
    }

    #[test]
    fn test_version_req_any() {
        let req = VersionReq::any();
        let v = Version::new(1, 0, 0);
        assert!(req.matches(&v));
    }

    #[test]
    fn test_version_display() {
        let v = Version::new(1, 2, 3);
        let s = format!("{}", v);
        assert_eq!(s, "1.2.3");
    }
}

// ============================================================================
// Common Types Extended Tests
// ============================================================================
mod common_extended_tests {
    use simple_common::{AbiVersion, ConfigEnv, Message, Target, TargetArch, TargetOS};

    #[test]
    fn test_target_arch_variants() {
        let archs = [TargetArch::X86_64, TargetArch::Aarch64, TargetArch::Riscv64];
        for a in archs {
            let _ = format!("{:?}", a);
        }
    }

    #[test]
    fn test_target_os_variants() {
        let oses = [
            TargetOS::Linux,
            TargetOS::MacOS,
            TargetOS::Windows,
            TargetOS::None,
        ];
        for o in oses {
            let _ = format!("{:?}", o);
        }
    }

    #[test]
    fn test_target_host() {
        let target = Target::host();
        let _ = format!("{:?}", target);
    }

    #[test]
    fn test_abi_version_current() {
        let version = AbiVersion::CURRENT;
        let v = version.to_u32();
        assert!(v > 0);
    }

    #[test]
    fn test_message_variants() {
        let msg = Message::Value("hello".to_string());
        let _ = format!("{:?}", msg);

        let msg2 = Message::Bytes(vec![1, 2, 3]);
        let _ = format!("{:?}", msg2);
    }

    #[test]
    fn test_config_env_new() {
        let config = ConfigEnv::new();
        let _ = config;
    }
}

// ============================================================================
// Type Checker Tests
// ============================================================================
mod type_checker_tests {
    use simple_type::{Type, TypeChecker};

    #[test]
    fn test_type_int() {
        let ty = Type::Int;
        let _ = format!("{:?}", ty);
    }

    #[test]
    fn test_type_float() {
        let ty = Type::Float;
        let _ = format!("{:?}", ty);
    }

    #[test]
    fn test_type_bool() {
        let ty = Type::Bool;
        let _ = format!("{:?}", ty);
    }

    #[test]
    fn test_type_checker_new() {
        let checker = TypeChecker::new();
        let _ = checker;
    }
}

// ============================================================================
// Dependency Tracker Tests
// ============================================================================
mod dep_tracker_tests {
    use simple_dependency_tracker::{ImportGraph, SymbolKind};

    #[test]
    fn test_import_graph_new() {
        let graph = ImportGraph::new();
        let _ = graph;
    }

    #[test]
    fn test_symbol_kind_function() {
        let kind = SymbolKind::Function;
        let _ = format!("{:?}", kind);
    }

    #[test]
    fn test_symbol_kind_module() {
        let kind = SymbolKind::Module;
        let _ = format!("{:?}", kind);
    }

    #[test]
    fn test_symbol_kind_type() {
        let kind = SymbolKind::Type;
        let _ = format!("{:?}", kind);
    }
}

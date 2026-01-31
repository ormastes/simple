//! Round 17: Extended tests for uncovered public types
//! Focus on SMF types, settlement tables, and lint types

// ============================================================================
// Loader SMF Section Types
// ============================================================================
mod loader_smf_section_tests {
    use simple_loader::smf::{SectionType, SmfSection};

    #[test]
    fn test_section_type_code() {
        let t = SectionType::Code;
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_section_type_data() {
        let t = SectionType::Data;
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_smf_section_size() {
        let _ = std::mem::size_of::<SmfSection>();
    }
}

// ============================================================================
// Loader SMF Symbol Types
// ============================================================================
mod loader_smf_symbol_tests {
    use simple_loader::smf::{SmfSymbol, SymbolBinding};

    #[test]
    fn test_symbol_binding_local() {
        let b = SymbolBinding::Local;
        let _ = format!("{:?}", b);
    }

    #[test]
    fn test_symbol_binding_global() {
        let b = SymbolBinding::Global;
        let _ = format!("{:?}", b);
    }

    #[test]
    fn test_symbol_binding_weak() {
        let b = SymbolBinding::Weak;
        let _ = format!("{:?}", b);
    }

    #[test]
    fn test_smf_symbol_size() {
        let _ = std::mem::size_of::<SmfSymbol>();
    }
}

// ============================================================================
// Loader SMF Relocation Types
// ============================================================================
mod loader_smf_reloc_tests {
    use simple_loader::smf::{RelocationType, SmfRelocation};

    #[test]
    fn test_relocation_type_none() {
        let t = RelocationType::None;
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_relocation_type_abs64() {
        let t = RelocationType::Abs64;
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_relocation_type_pc32() {
        let t = RelocationType::Pc32;
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_smf_relocation_size() {
        let _ = std::mem::size_of::<SmfRelocation>();
    }
}

// ============================================================================
// Loader Settlement Tables
// ============================================================================
mod loader_settlement_tables_tests {
    use simple_loader::settlement::TableIndex;

    #[test]
    fn test_table_index() {
        let idx = TableIndex(42);
        let _ = format!("{:?}", idx);
        assert_eq!(idx.0, 42);
    }

    #[test]
    fn test_table_index_zero() {
        let idx = TableIndex(0);
        let _ = format!("{:?}", idx);
    }
}

// ============================================================================
// Compiler Lint Types Extended
// ============================================================================
mod compiler_lint_extended_tests {
    use simple_compiler::{LintConfig, LintLevel};

    #[test]
    fn test_lint_level_allow() {
        let level = LintLevel::Allow;
        let _ = format!("{:?}", level);
    }

    #[test]
    fn test_lint_level_warn() {
        let level = LintLevel::Warn;
        let _ = format!("{:?}", level);
    }

    #[test]
    fn test_lint_level_deny() {
        let level = LintLevel::Deny;
        let _ = format!("{:?}", level);
    }

    #[test]
    fn test_lint_config_default() {
        let config = LintConfig::default();
        let _ = format!("{:?}", config);
    }
}

// ============================================================================
// Compiler MIR Extended Types
// ============================================================================
mod compiler_mir_more_tests {
    use simple_compiler::mir::VReg;

    #[test]
    fn test_vreg_index() {
        let vreg = VReg(42);
        let _ = format!("{:?}", vreg);
        assert_eq!(vreg.0, 42);
    }

    #[test]
    fn test_vreg_zero() {
        let vreg = VReg(0);
        let _ = format!("{:?}", vreg);
    }
}

// ============================================================================
// Compiler HIR Extended Types
// ============================================================================
mod compiler_hir_extended_tests {
    use simple_compiler::hir::{HirType, Signedness, TypeId};

    #[test]
    fn test_hir_type_int() {
        // HirType::Int has bits and signedness fields
        let ty = HirType::Int {
            bits: 64,
            signedness: Signedness::Signed,
        };
        let _ = format!("{:?}", ty);
    }

    #[test]
    fn test_hir_type_bool() {
        let ty = HirType::Bool;
        let _ = format!("{:?}", ty);
    }

    #[test]
    fn test_hir_type_string() {
        let ty = HirType::String;
        let _ = format!("{:?}", ty);
    }

    #[test]
    fn test_hir_type_void() {
        let ty = HirType::Void;
        let _ = format!("{:?}", ty);
    }

    #[test]
    fn test_type_id_new() {
        let id = TypeId(100);
        let _ = format!("{:?}", id);
    }

    #[test]
    fn test_signedness_variants() {
        let signed = Signedness::Signed;
        let unsigned = Signedness::Unsigned;
        let _ = format!("{:?}", signed);
        let _ = format!("{:?}", unsigned);
    }
}

// ============================================================================
// Compiler Error Types
// ============================================================================
mod compiler_error_tests {
    use simple_compiler::{CompileError, ErrorContext};

    #[test]
    fn test_compile_error_size() {
        let _ = std::mem::size_of::<CompileError>();
    }

    #[test]
    fn test_error_context_new() {
        let ctx = ErrorContext::new();
        let _ = format!("{:?}", ctx);
    }
}

// ============================================================================
// Compiler Monomorphize Types Extended
// ============================================================================
mod compiler_mono_extended_tests {
    use simple_compiler::monomorphize::{ConcreteType, MonomorphizationTable, SpecializationKey, TypeBindings};

    #[test]
    fn test_concrete_type_int() {
        let ty = ConcreteType::Int;
        let _ = format!("{:?}", ty);
    }

    #[test]
    fn test_concrete_type_bool() {
        let ty = ConcreteType::Bool;
        let _ = format!("{:?}", ty);
    }

    #[test]
    fn test_specialization_key_new() {
        let key = SpecializationKey::new("test_func", vec![ConcreteType::Int]);
        let _ = format!("{:?}", key);
        assert_eq!(key.name, "test_func");
    }

    #[test]
    fn test_type_bindings_insert() {
        let mut bindings = TypeBindings::new();
        bindings.insert("T".to_string(), ConcreteType::Bool);
        let _ = format!("{:?}", bindings);
    }

    #[test]
    fn test_monomorphization_table_new() {
        let table = MonomorphizationTable::new();
        let _ = format!("{:?}", table);
    }
}

// ============================================================================
// Runtime Memory Types
// ============================================================================
mod runtime_memory_tests {
    use simple_runtime::memory::gc::GcRuntime;
    use simple_runtime::NoGcAllocator;

    #[test]
    fn test_gc_runtime_new() {
        let gc = GcRuntime::new();
        let _ = gc;
    }

    #[test]
    fn test_no_gc_allocator_new() {
        let alloc = NoGcAllocator::new();
        let _ = alloc;
    }
}

// ============================================================================
// Common Runtime Symbols
// ============================================================================
mod common_runtime_symbols_tests {
    use simple_common::{AbiVersion, RUNTIME_SYMBOL_NAMES};

    #[test]
    fn test_abi_version_size() {
        let _ = std::mem::size_of::<AbiVersion>();
    }

    #[test]
    fn test_runtime_symbol_names_not_empty() {
        assert!(!RUNTIME_SYMBOL_NAMES.is_empty());
    }

    #[test]
    fn test_runtime_symbol_names_valid() {
        for name in RUNTIME_SYMBOL_NAMES {
            assert!(!name.is_empty());
        }
    }
}

// ============================================================================
// Parser Span Extended
// ============================================================================
mod parser_span_extended_tests {
    use simple_parser::Span;

    #[test]
    fn test_span_fields() {
        let span = Span::new(5, 15, 1, 1);
        assert_eq!(span.start, 5);
        assert_eq!(span.end, 15);
        assert_eq!(span.end - span.start, 10);
    }

    #[test]
    fn test_span_line_column() {
        let span = Span::new(0, 10, 5, 3);
        assert_eq!(span.line, 5);
        assert_eq!(span.column, 3);
    }
}

// ============================================================================
// Parser Lexer Types Extended
// ============================================================================
mod parser_lexer_extended_tests {
    use simple_parser::{Lexer, Span, Token, TokenKind};

    #[test]
    fn test_lexer_tokenize() {
        let mut lexer = Lexer::new("let x = 42");
        let tokens = lexer.tokenize();
        assert!(!tokens.is_empty());
    }

    #[test]
    fn test_token_new() {
        let token = Token::new(TokenKind::Let, Span::new(0, 3, 1, 1), "let".to_string());
        let _ = format!("{:?}", token);
    }

    #[test]
    fn test_token_kind() {
        let token = Token::new(TokenKind::If, Span::new(0, 2, 1, 1), "if".to_string());
        assert_eq!(token.kind, TokenKind::If);
    }
}

// ============================================================================
// Compiler Coverage Types
// ============================================================================
mod compiler_coverage_tests {
    use simple_compiler::coverage::is_coverage_enabled;

    #[test]
    fn test_is_coverage_enabled() {
        let _ = is_coverage_enabled();
    }
}

// ============================================================================
// Compiler Pipeline Types
// ============================================================================
mod compiler_pipeline_tests {
    use simple_compiler::CompilerPipeline;

    #[test]
    fn test_compiler_pipeline_size() {
        let _ = std::mem::size_of::<CompilerPipeline>();
    }
}

// ============================================================================
// Loader Module Types
// ============================================================================
mod loader_module_extended_tests {
    use simple_loader::{LoadedModule, ModuleLoader, ModuleRegistry};

    #[test]
    fn test_module_loader_size() {
        let _ = std::mem::size_of::<ModuleLoader>();
    }

    #[test]
    fn test_module_registry_new() {
        let registry = ModuleRegistry::new();
        // ModuleRegistry doesn't impl Debug, just check it exists
        let _ = registry;
    }

    #[test]
    fn test_loaded_module_size() {
        let _ = std::mem::size_of::<LoadedModule>();
    }
}

// ============================================================================
// Parser AST Types (size checks for types without Default)
// ============================================================================
mod parser_ast_size_tests {
    use simple_parser::{
        ActorDef, Argument, Attribute, ClassDef, Decorator, EnumDef, EnumVariant, Expr, Field, ForStmt, FunctionDef,
        IfStmt, ImplBlock, LetStmt, MatchStmt, Pattern, StructDef, TraitDef, WhileStmt,
    };

    #[test]
    fn test_actor_def_size() {
        let _ = std::mem::size_of::<ActorDef>();
    }

    #[test]
    fn test_class_def_size() {
        let _ = std::mem::size_of::<ClassDef>();
    }

    #[test]
    fn test_enum_def_size() {
        let _ = std::mem::size_of::<EnumDef>();
    }

    #[test]
    fn test_struct_def_size() {
        let _ = std::mem::size_of::<StructDef>();
    }

    #[test]
    fn test_trait_def_size() {
        let _ = std::mem::size_of::<TraitDef>();
    }

    #[test]
    fn test_function_def_size() {
        let _ = std::mem::size_of::<FunctionDef>();
    }

    #[test]
    fn test_impl_block_size() {
        let _ = std::mem::size_of::<ImplBlock>();
    }

    #[test]
    fn test_if_stmt_size() {
        let _ = std::mem::size_of::<IfStmt>();
    }

    #[test]
    fn test_for_stmt_size() {
        let _ = std::mem::size_of::<ForStmt>();
    }

    #[test]
    fn test_while_stmt_size() {
        let _ = std::mem::size_of::<WhileStmt>();
    }

    #[test]
    fn test_match_stmt_size() {
        let _ = std::mem::size_of::<MatchStmt>();
    }

    #[test]
    fn test_let_stmt_size() {
        let _ = std::mem::size_of::<LetStmt>();
    }

    #[test]
    fn test_argument_size() {
        let _ = std::mem::size_of::<Argument>();
    }

    #[test]
    fn test_decorator_size() {
        let _ = std::mem::size_of::<Decorator>();
    }

    #[test]
    fn test_attribute_size() {
        let _ = std::mem::size_of::<Attribute>();
    }

    #[test]
    fn test_expr_size() {
        let _ = std::mem::size_of::<Expr>();
    }

    #[test]
    fn test_pattern_size() {
        let _ = std::mem::size_of::<Pattern>();
    }

    #[test]
    fn test_field_size() {
        let _ = std::mem::size_of::<Field>();
    }

    #[test]
    fn test_enum_variant_size() {
        let _ = std::mem::size_of::<EnumVariant>();
    }
}

// ============================================================================
// Runtime Value Types
// ============================================================================
mod runtime_value_extended_tests {
    use simple_runtime::value::RuntimeValue;
    use simple_runtime::{RuntimeArray, RuntimeObject, RuntimeString, RuntimeTuple};

    #[test]
    fn test_runtime_value_size() {
        let _ = std::mem::size_of::<RuntimeValue>();
    }

    #[test]
    fn test_runtime_array_size() {
        let _ = std::mem::size_of::<RuntimeArray>();
    }

    #[test]
    fn test_runtime_tuple_size() {
        let _ = std::mem::size_of::<RuntimeTuple>();
    }

    #[test]
    fn test_runtime_string_size() {
        let _ = std::mem::size_of::<RuntimeString>();
    }

    #[test]
    fn test_runtime_object_size() {
        let _ = std::mem::size_of::<RuntimeObject>();
    }
}

// ============================================================================
// Compiler Value Extended Types
// ============================================================================
mod compiler_value_more_tests {
    use simple_compiler::value::{Env, Value};

    #[test]
    fn test_value_nil() {
        let v = Value::Nil;
        let _ = format!("{:?}", v);
    }

    #[test]
    fn test_value_bool() {
        let v = Value::Bool(true);
        let _ = format!("{:?}", v);
    }

    #[test]
    fn test_value_int() {
        let v = Value::Int(42);
        let _ = format!("{:?}", v);
    }

    #[test]
    fn test_value_float() {
        let v = Value::Float(3.15);
        let _ = format!("{:?}", v);
    }

    #[test]
    fn test_env_new() {
        let env = Env::new();
        let _ = format!("{:?}", env);
    }
}

// ============================================================================
// Dependency Tracker Extended Types
// ============================================================================
// Driver Extended Types
// ============================================================================
mod driver_more_tests {
    use simple_driver::{RunResult, Runner};

    #[test]
    fn test_runner_new() {
        let runner = Runner::new();
        let _ = runner;
    }

    #[test]
    fn test_run_result_size() {
        let _ = std::mem::size_of::<RunResult>();
    }
}

// ============================================================================
// Common Extended Types
// ============================================================================
mod common_more_tests {
    use simple_common::{PointerSize, Target};

    #[test]
    fn test_target_size() {
        let _ = std::mem::size_of::<Target>();
    }

    #[test]
    fn test_pointer_size_bits() {
        let ps = PointerSize::Bits64;
        assert_eq!(ps.bytes(), 8);
    }
}

// ============================================================================
// Type Checker Extended Types
// ============================================================================
mod type_checker_more_tests {
    use simple_type::{Substitution, Type};

    #[test]
    fn test_type_int() {
        let t = Type::Int;
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_type_bool() {
        let t = Type::Bool;
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_substitution_size() {
        let _ = std::mem::size_of::<Substitution>();
    }
}

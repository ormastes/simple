//! Round 14: Extended tests for uncovered public types
//! Focus on parser AST types and compiler exports

// ============================================================================
// Compiler Lint Types Tests
// ============================================================================
mod compiler_lint_tests {
    use simple_compiler::{LintConfig, LintLevel};

    #[test]
    fn test_lint_level_variants() {
        let levels = [LintLevel::Allow, LintLevel::Warn, LintLevel::Deny];
        for l in levels {
            let _ = format!("{:?}", l);
        }
    }

    #[test]
    fn test_lint_config_default() {
        let config = LintConfig::default();
        let _ = format!("{:?}", config);
    }
}

// ============================================================================
// Compiler Monomorphize Types Tests
// ============================================================================
mod compiler_mono_tests {
    use simple_compiler::{ConcreteType, MonomorphizationTable, PointerKind, TypeBindings};

    #[test]
    fn test_concrete_type_variants() {
        let types = [
            ConcreteType::Int,
            ConcreteType::Float,
            ConcreteType::Bool,
            ConcreteType::String,
        ];
        for t in types {
            let _ = format!("{:?}", t);
        }
    }

    #[test]
    fn test_monomorphization_table_new() {
        let table = MonomorphizationTable::new();
        let _ = format!("{:?}", table);
    }

    #[test]
    fn test_type_bindings_new() {
        let bindings = TypeBindings::new();
        let _ = format!("{:?}", bindings);
    }

    #[test]
    fn test_pointer_kind_variants() {
        let kinds = [PointerKind::Unique, PointerKind::Shared, PointerKind::Weak];
        for k in kinds {
            let _ = format!("{:?}", k);
        }
    }
}

// ============================================================================
// Compiler Value Types Tests
// ============================================================================
mod compiler_value_types_tests {
    use simple_compiler::Env;

    #[test]
    fn test_env_new() {
        let env = Env::new();
        let _ = format!("{:?}", env);
    }
}

// ============================================================================
// Compiler Coverage Types Tests
// ============================================================================
mod compiler_coverage_tests {
    use simple_compiler::is_coverage_enabled;

    #[test]
    fn test_is_coverage_enabled() {
        let enabled = is_coverage_enabled();
        let _ = enabled;
    }
}

// ============================================================================
// Compiler Error Types Tests
// ============================================================================
mod compiler_error_tests {
    use simple_compiler::ErrorContext;

    #[test]
    fn test_error_context_new() {
        let ctx = ErrorContext::new();
        let _ = format!("{:?}", ctx);
    }
}

// ============================================================================
// Compiler Module Resolver Tests
// ============================================================================
mod compiler_resolver_tests {
    use simple_compiler::DirectoryManifest;

    #[test]
    fn test_directory_manifest_default() {
        let manifest = DirectoryManifest::default();
        let _ = format!("{:?}", manifest);
    }
}

// ============================================================================
// Loader Types Tests
// ============================================================================
mod loader_types_tests {
    use simple_loader::{ModuleRegistry, SettlementConfig};

    #[test]
    fn test_module_registry_new() {
        let registry = ModuleRegistry::new();
        let _ = registry;
    }

    #[test]
    fn test_settlement_config_new() {
        let config = SettlementConfig::default();
        let _ = format!("{:?}", config);
    }
}

// ============================================================================
// Parser Lexer Types Tests
// ============================================================================
mod parser_lexer_tests {
    use simple_parser::{Lexer, TokenKind};

    #[test]
    fn test_lexer_new() {
        let lexer = Lexer::new("let x = 42");
        let _ = lexer;
    }

    #[test]
    fn test_token_kind_keyword_variants() {
        let kinds = [
            TokenKind::Let,
            TokenKind::If,
            TokenKind::Else,
            TokenKind::While,
            TokenKind::For,
            TokenKind::Fn,
            TokenKind::Return,
            TokenKind::Class,
            TokenKind::Struct,
            TokenKind::Enum,
            TokenKind::Trait,
            TokenKind::Impl,
            TokenKind::Use,
            TokenKind::Mod,
            TokenKind::Pub,
        ];
        for k in kinds {
            let _ = format!("{:?}", k);
        }
    }
}

// ============================================================================
// Parser Diagnostic Types Tests
// ============================================================================
// NOTE: Diagnostics struct was refactored - now uses simple_common::diagnostic::Diagnostic
// mod parser_diagnostic_tests {
//     use simple_parser::Diagnostics;
//
//     #[test]
//     fn test_diagnostics_new() {
//         let diag = Diagnostics::new();
//         let _ = format!("{:?}", diag);
//     }
// }

// ============================================================================
// Parser Doc Types Tests
// ============================================================================
mod parser_doc_tests {
    use simple_parser::DocItemKind;

    #[test]
    fn test_doc_item_kind_variants() {
        let kinds = [
            DocItemKind::Function,
            DocItemKind::Class,
            DocItemKind::Struct,
            DocItemKind::Enum,
            DocItemKind::Trait,
        ];
        for k in kinds {
            let _ = format!("{:?}", k);
        }
    }
}

// ============================================================================
// Parser Module Path Tests
// ============================================================================
mod parser_module_path_tests {
    use simple_parser::ModulePath;

    #[test]
    fn test_module_path_new() {
        let path = ModulePath::new(vec!["foo".to_string(), "bar".to_string()]);
        let _ = format!("{:?}", path);
    }
}

// ============================================================================
// Runtime GC Module Tests
// ============================================================================
mod runtime_gc_module_tests {
    use simple_runtime::gc::GcRuntime;

    #[test]
    fn test_gc_runtime_new() {
        let gc = GcRuntime::new();
        let _ = gc;
    }
}

// ============================================================================
// Parser Block Tests
// ============================================================================
mod parser_block_tests {
    use simple_parser::Block;

    #[test]
    fn test_block_default() {
        let block = Block::default();
        let _ = format!("{:?}", block);
    }
}

// ============================================================================
// Parser DocComment Tests
// ============================================================================
mod parser_doc_comment_tests {
    use simple_parser::DocComment;

    #[test]
    fn test_doc_comment_default() {
        let doc = DocComment::default();
        let _ = format!("{:?}", doc);
    }
}

// ============================================================================
// Parser ContractBlock Tests
// ============================================================================
mod parser_contract_block_tests {
    use simple_parser::ContractBlock;

    #[test]
    fn test_contract_block_default() {
        let block = ContractBlock::default();
        let _ = format!("{:?}", block);
    }
}

// ============================================================================
// Compiler NewType Tests
// ============================================================================
mod compiler_newtype_tests {
    use simple_compiler::{ClassName, EnumTypeName, VariantName};

    #[test]
    fn test_class_name() {
        let name = ClassName("MyClass".to_string());
        let _ = format!("{:?}", name);
    }

    #[test]
    fn test_enum_type_name() {
        let name = EnumTypeName("MyEnum".to_string());
        let _ = format!("{:?}", name);
    }

    #[test]
    fn test_variant_name() {
        let name = VariantName("Some".to_string());
        let _ = format!("{:?}", name);
    }
}

// ============================================================================
// Compiler Contract Mode Tests
// ============================================================================
mod compiler_contract_mode_tests {
    use simple_compiler::ContractMode;

    #[test]
    fn test_contract_mode_default() {
        let mode = ContractMode::default();
        let _ = format!("{:?}", mode);
    }
}

// ============================================================================
// Parser BinaryOp Operator Tests
// ============================================================================
mod parser_binop_tests {
    use simple_parser::BinOp;

    #[test]
    fn test_binop_variants() {
        let ops = [
            BinOp::Add,
            BinOp::Sub,
            BinOp::Mul,
            BinOp::Div,
            BinOp::Mod,
            BinOp::Eq,
            BinOp::Lt,
            BinOp::Gt,
            BinOp::And,
            BinOp::Or,
        ];
        for op in ops {
            let _ = format!("{:?}", op);
        }
    }
}

// ============================================================================
// Parser UnaryOp Operator Tests
// ============================================================================
mod parser_unaryop_tests {
    use simple_parser::UnaryOp;

    #[test]
    fn test_unaryop_variants() {
        let ops = [UnaryOp::Neg, UnaryOp::Not];
        for op in ops {
            let _ = format!("{:?}", op);
        }
    }
}

// ============================================================================
// Parser AssignOp Tests
// ============================================================================
mod parser_assignop_tests {
    use simple_parser::AssignOp;

    #[test]
    fn test_assignop_variants() {
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
}

// ============================================================================
// Parser Visibility Tests
// ============================================================================
mod parser_visibility_tests {
    use simple_parser::Visibility;

    #[test]
    fn test_visibility_variants() {
        let vis = [Visibility::Private, Visibility::Public];
        for v in vis {
            let _ = format!("{:?}", v);
        }
    }
}

// ============================================================================
// Parser Mutability Tests
// ============================================================================
mod parser_mutability_tests {
    use simple_parser::Mutability;

    #[test]
    fn test_mutability_variants() {
        let muts = [Mutability::Immutable, Mutability::Mutable];
        for m in muts {
            let _ = format!("{:?}", m);
        }
    }
}

// ============================================================================
// Parser Effect Tests
// ============================================================================
mod parser_effect_tests {
    use simple_parser::Effect;

    #[test]
    fn test_effect_variants() {
        let effects = [Effect::Pure, Effect::Async];
        for e in effects {
            let _ = format!("{:?}", e);
        }
    }
}

// ============================================================================
// Parser PointerKind Tests
// ============================================================================
mod parser_pointer_tests {
    use simple_parser::PointerKind;

    #[test]
    fn test_pointer_kind_variants() {
        let kinds = [PointerKind::Unique, PointerKind::Shared, PointerKind::Weak];
        for k in kinds {
            let _ = format!("{:?}", k);
        }
    }
}

// ============================================================================
// Parser RangeBound Tests
// ============================================================================
mod parser_rangebound_tests {
    use simple_parser::RangeBound;

    #[test]
    fn test_range_bound_variants() {
        let bounds = [RangeBound::Inclusive, RangeBound::Exclusive];
        for b in bounds {
            let _ = format!("{:?}", b);
        }
    }
}

// ============================================================================
// Parser OverflowBehavior Tests
// ============================================================================
mod parser_overflow_tests {
    use simple_parser::OverflowBehavior;

    #[test]
    fn test_overflow_behavior_variants() {
        let behaviors = [OverflowBehavior::Wrap, OverflowBehavior::Saturate];
        for b in behaviors {
            let _ = format!("{:?}", b);
        }
    }
}

//! Round 20: Extended tests for remaining uncovered public types
//! Focus on parser unit/arithmetic types, loader native, and compiler types

// ============================================================================
// Parser Unit Definition Types
// ============================================================================
mod parser_unit_def_tests {
    use simple_parser::{UnitDef, UnitExpr, UnitFamilyDef, UnitVariant};

    #[test]
    fn test_unit_def_size() {
        let _ = std::mem::size_of::<UnitDef>();
    }

    #[test]
    fn test_unit_expr_size() {
        let _ = std::mem::size_of::<UnitExpr>();
    }

    #[test]
    fn test_unit_variant_size() {
        let _ = std::mem::size_of::<UnitVariant>();
    }

    #[test]
    fn test_unit_family_def_size() {
        let _ = std::mem::size_of::<UnitFamilyDef>();
    }
}

// ============================================================================
// Parser Arithmetic Types
// ============================================================================
mod parser_arithmetic_tests {
    use simple_parser::{BinaryArithmeticOp, BinaryArithmeticRule, UnaryArithmeticOp, UnaryArithmeticRule, UnitArithmetic};

    #[test]
    fn test_binary_arithmetic_op_size() {
        let _ = std::mem::size_of::<BinaryArithmeticOp>();
    }

    #[test]
    fn test_binary_arithmetic_rule_size() {
        let _ = std::mem::size_of::<BinaryArithmeticRule>();
    }

    #[test]
    fn test_unary_arithmetic_op_size() {
        let _ = std::mem::size_of::<UnaryArithmeticOp>();
    }

    #[test]
    fn test_unary_arithmetic_rule_size() {
        let _ = std::mem::size_of::<UnaryArithmeticRule>();
    }

    #[test]
    fn test_unit_arithmetic_size() {
        let _ = std::mem::size_of::<UnitArithmetic>();
    }
}

// ============================================================================
// Parser Bounds Extended Types
// ============================================================================
mod parser_bounds_extended_tests {
    use simple_parser::{BoundsAtom, BoundsCase, BoundsPattern};

    #[test]
    fn test_bounds_atom_size() {
        let _ = std::mem::size_of::<BoundsAtom>();
    }

    #[test]
    fn test_bounds_case_size() {
        let _ = std::mem::size_of::<BoundsCase>();
    }

    #[test]
    fn test_bounds_pattern_size() {
        let _ = std::mem::size_of::<BoundsPattern>();
    }
}

// ============================================================================
// Parser Type Alias Types
// ============================================================================
mod parser_type_alias_tests {
    use simple_parser::{RefinementType, TypeAliasDef, WhereBound};

    #[test]
    fn test_type_alias_def_size() {
        let _ = std::mem::size_of::<TypeAliasDef>();
    }

    #[test]
    fn test_refinement_type_size() {
        let _ = std::mem::size_of::<RefinementType>();
    }

    #[test]
    fn test_where_bound_size() {
        let _ = std::mem::size_of::<WhereBound>();
    }
}

// ============================================================================
// Parser Repr Types
// ============================================================================
mod parser_repr_tests {
    use simple_parser::{ReprType, UnitReprConstraints, UnitWithRepr};

    #[test]
    fn test_repr_type_size() {
        let _ = std::mem::size_of::<ReprType>();
    }

    #[test]
    fn test_unit_with_repr_size() {
        let _ = std::mem::size_of::<UnitWithRepr>();
    }

    #[test]
    fn test_unit_repr_constraints_size() {
        let _ = std::mem::size_of::<UnitReprConstraints>();
    }
}

// ============================================================================
// Parser Static and Requires Types
// ============================================================================
mod parser_static_tests {
    use simple_parser::{RequiresCapabilitiesStmt, StaticStmt};

    #[test]
    fn test_static_stmt_size() {
        let _ = std::mem::size_of::<StaticStmt>();
    }

    #[test]
    fn test_requires_capabilities_stmt_size() {
        let _ = std::mem::size_of::<RequiresCapabilitiesStmt>();
    }
}

// ============================================================================
// Parser Bitfield Extended Types
// ============================================================================
mod parser_bitfield_extended_tests {
    use simple_parser::BitfieldConstant;

    #[test]
    fn test_bitfield_constant_size() {
        let _ = std::mem::size_of::<BitfieldConstant>();
    }
}

// ============================================================================
// Parser Mode Types
// ============================================================================
mod parser_mode_tests {
    use simple_parser::ParserMode;

    #[test]
    fn test_parser_mode_size() {
        let _ = std::mem::size_of::<ParserMode>();
    }
}

// ============================================================================
// Parser Source Registry Types
// ============================================================================
// NOTE: SourceRegistry was refactored and removed from public API
// mod parser_source_registry_tests {
//     use simple_parser::SourceRegistry;
//
//     #[test]
//     fn test_source_registry_size() {
//         let _ = std::mem::size_of::<SourceRegistry>();
//     }
// }

// ============================================================================
// Loader Symbol Export/Import Types
// ============================================================================
mod loader_symbol_extended_tests {
    use simple_loader::settlement::{ExportedSymbol, ImportedSymbol};

    #[test]
    fn test_exported_symbol_size() {
        let _ = std::mem::size_of::<ExportedSymbol>();
    }

    #[test]
    fn test_imported_symbol_size() {
        let _ = std::mem::size_of::<ImportedSymbol>();
    }
}

// ============================================================================
// Loader Memory Protection Types
// ============================================================================
mod loader_memory_protection_tests {
    use simple_loader::memory::Protection;

    #[test]
    fn test_protection_size() {
        let _ = std::mem::size_of::<Protection>();
    }
}

// ============================================================================
// Compiler Async Lowering Types
// ============================================================================
mod compiler_async_lowering_tests {
    use simple_compiler::mir::{AsyncLowering, AsyncState};

    #[test]
    fn test_async_lowering_size() {
        let _ = std::mem::size_of::<AsyncLowering>();
    }

    #[test]
    fn test_async_state_size() {
        let _ = std::mem::size_of::<AsyncState>();
    }
}

// ============================================================================
// Compiler Generator Lowering Types
// ============================================================================
mod compiler_generator_lowering_tests {
    use simple_compiler::mir::GeneratorLowering;

    #[test]
    fn test_generator_lowering_size() {
        let _ = std::mem::size_of::<GeneratorLowering>();
    }
}

// ============================================================================
// Compiler Block Types
// ============================================================================
// NOTE: BlockState is not publicly exported from mir module
// mod compiler_block_tests {
//     use simple_compiler::mir::{BlockState, BlockBuildError};
//
//     #[test]
//     fn test_block_state_size() {
//         let _ = std::mem::size_of::<BlockState>();
//     }
//
//     #[test]
//     fn test_block_build_error_size() {
//         let _ = std::mem::size_of::<BlockBuildError>();
//     }
// }

// ============================================================================
// Compiler HIR Extended Types
// ============================================================================
mod compiler_hir_extended_tests {
    use simple_compiler::hir::{HirRefinedType, HirTypeInvariant};

    #[test]
    fn test_hir_refined_type_size() {
        let _ = std::mem::size_of::<HirRefinedType>();
    }

    #[test]
    fn test_hir_type_invariant_size() {
        let _ = std::mem::size_of::<HirTypeInvariant>();
    }
}

// ============================================================================
// Runtime Heap Types Extended
// ============================================================================
mod runtime_heap_extended_tests {
    use simple_runtime::value::HeapObjectType;

    #[test]
    fn test_heap_object_type_size() {
        let _ = std::mem::size_of::<HeapObjectType>();
    }
}

// ============================================================================
// Runtime Closure Types
// ============================================================================
mod runtime_closure_tests {
    use simple_runtime::RuntimeClosure;

    #[test]
    fn test_runtime_closure_size() {
        let _ = std::mem::size_of::<RuntimeClosure>();
    }
}

// ============================================================================
// Runtime Enum Types
// ============================================================================
mod runtime_enum_tests {
    use simple_runtime::RuntimeEnum;

    #[test]
    fn test_runtime_enum_size() {
        let _ = std::mem::size_of::<RuntimeEnum>();
    }
}

// ============================================================================
// Common Config Env Types
// ============================================================================
mod common_config_env_tests {
    use simple_common::ConfigEnv;

    #[test]
    fn test_config_env_size() {
        let _ = std::mem::size_of::<ConfigEnv>();
    }

    #[test]
    fn test_config_env_default() {
        let env = ConfigEnv::default();
        let _ = env;
    }
}

// ============================================================================
// Loader Link Result Types
// ============================================================================
mod loader_link_result_tests {
    use simple_loader::settlement::LinkResult;

    #[test]
    fn test_link_result_size() {
        let _ = std::mem::size_of::<LinkResult>();
    }
}

// ============================================================================
// Loader Indirection Table Types
// ============================================================================
mod loader_indirection_table_tests {
    use simple_loader::settlement::IndirectionTable;

    #[test]
    fn test_indirection_table_size() {
        // IndirectionTable is generic, use a concrete type
        let _ = std::mem::size_of::<IndirectionTable<u64>>();
    }
}

// ============================================================================
// Loader Cross Compile Error Types
// ============================================================================
mod loader_cross_compile_error_tests {
    use simple_loader::native_cross::CrossCompileError;

    #[test]
    fn test_cross_compile_error_size() {
        let _ = std::mem::size_of::<CrossCompileError>();
    }
}

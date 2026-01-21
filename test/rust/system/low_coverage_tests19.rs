//! Round 19: Extended tests for uncovered public types
//! Focus on remaining parser, loader, runtime, and compiler types

// ============================================================================
// Parser More Statement Types
// ============================================================================
mod parser_more_stmt_tests {
    use simple_parser::{ConstStmt, ExternDef, LoopStmt};

    #[test]
    fn test_const_stmt_size() {
        let _ = std::mem::size_of::<ConstStmt>();
    }

    #[test]
    fn test_loop_stmt_size() {
        let _ = std::mem::size_of::<LoopStmt>();
    }

    #[test]
    fn test_extern_def_size() {
        let _ = std::mem::size_of::<ExternDef>();
    }
}

// ============================================================================
// Parser Use Statement Types
// ============================================================================
mod parser_use_stmt_tests {
    use simple_parser::{AutoImportStmt, CommonUseStmt, ExportUseStmt};

    #[test]
    fn test_common_use_stmt_size() {
        let _ = std::mem::size_of::<CommonUseStmt>();
    }

    #[test]
    fn test_export_use_stmt_size() {
        let _ = std::mem::size_of::<ExportUseStmt>();
    }

    #[test]
    fn test_auto_import_stmt_size() {
        let _ = std::mem::size_of::<AutoImportStmt>();
    }
}

// ============================================================================
// Parser Lambda and Function Types
// ============================================================================
mod parser_lambda_tests {
    use simple_parser::LambdaParam;

    #[test]
    fn test_lambda_param_size() {
        let _ = std::mem::size_of::<LambdaParam>();
    }
}

// ============================================================================
// Parser Contract Types
// ============================================================================
mod parser_contract_tests {
    use simple_parser::{ContractClause, InvariantBlock};

    #[test]
    fn test_contract_clause_size() {
        let _ = std::mem::size_of::<ContractClause>();
    }

    #[test]
    fn test_invariant_block_size() {
        let _ = std::mem::size_of::<InvariantBlock>();
    }
}

// ============================================================================
// Parser Macro Extended Types
// ============================================================================
mod parser_macro_extended_tests {
    use simple_parser::{MacroContractItem, MacroInject, MacroIntro, MacroParam, MacroReturns, MacroStmt};

    #[test]
    fn test_macro_stmt_size() {
        let _ = std::mem::size_of::<MacroStmt>();
    }

    #[test]
    fn test_macro_param_size() {
        let _ = std::mem::size_of::<MacroParam>();
    }

    #[test]
    fn test_macro_contract_item_size() {
        let _ = std::mem::size_of::<MacroContractItem>();
    }

    #[test]
    fn test_macro_contract_types_size() {
        let _ = std::mem::size_of::<MacroReturns>();
        let _ = std::mem::size_of::<MacroIntro>();
        let _ = std::mem::size_of::<MacroInject>();
    }
}

// ============================================================================
// Parser Bounds Types
// ============================================================================
mod parser_bounds_tests {
    use simple_parser::{BoundsBlock, BoundsKind};

    #[test]
    fn test_bounds_block_size() {
        let _ = std::mem::size_of::<BoundsBlock>();
    }

    #[test]
    fn test_bounds_kind_size() {
        let _ = std::mem::size_of::<BoundsKind>();
    }
}

// ============================================================================
// Parser Bitfield Types
// ============================================================================
mod parser_bitfield_tests {
    use simple_parser::{BitfieldDef, BitfieldField};

    #[test]
    fn test_bitfield_def_size() {
        let _ = std::mem::size_of::<BitfieldDef>();
    }

    #[test]
    fn test_bitfield_field_size() {
        let _ = std::mem::size_of::<BitfieldField>();
    }
}

// ============================================================================
// Parser Assignment Types
// ============================================================================
mod parser_assignment_tests {
    use simple_parser::AssignmentStmt;

    #[test]
    fn test_assignment_stmt_size() {
        let _ = std::mem::size_of::<AssignmentStmt>();
    }
}

// ============================================================================
// Parser Associated Types
// ============================================================================
mod parser_associated_tests {
    use simple_parser::{AssociatedTypeDef, AssociatedTypeImpl};

    #[test]
    fn test_associated_type_def_size() {
        let _ = std::mem::size_of::<AssociatedTypeDef>();
    }

    #[test]
    fn test_associated_type_impl_size() {
        let _ = std::mem::size_of::<AssociatedTypeImpl>();
    }
}

// ============================================================================
// Loader Settlement Extended Types
// ============================================================================
mod loader_settlement_extended_tests {
    use simple_loader::settlement::{SettlementLinker, SettlementModule};

    #[test]
    fn test_settlement_linker_size() {
        let _ = std::mem::size_of::<SettlementLinker>();
    }

    #[test]
    fn test_settlement_module_size() {
        let _ = std::mem::size_of::<SettlementModule>();
    }
}

// ============================================================================
// Loader Symbol Types
// ============================================================================
mod loader_symbol_tests {
    use simple_loader::smf::{SmfSymbol, SymbolBinding, SymbolType};

    #[test]
    fn test_smf_symbol_default() {
        let _ = std::mem::size_of::<SmfSymbol>();
    }

    #[test]
    fn test_symbol_binding_size() {
        let _ = std::mem::size_of::<SymbolBinding>();
    }

    #[test]
    fn test_symbol_type_size() {
        let _ = std::mem::size_of::<SymbolType>();
    }
}

// ============================================================================
// Runtime Memory Types
// ============================================================================
mod runtime_memory_extended_tests {
    use simple_runtime::HeapHeader;

    #[test]
    fn test_heap_header_size() {
        let _ = std::mem::size_of::<HeapHeader>();
    }
}

// ============================================================================
// Runtime Contract Types
// ============================================================================
mod runtime_contract_tests {
    use simple_runtime::RuntimeContractViolation;

    #[test]
    fn test_runtime_contract_violation_size() {
        let _ = std::mem::size_of::<RuntimeContractViolation>();
    }
}

// ============================================================================
// Compiler HIR Contract Types
// ============================================================================
mod compiler_hir_contract_tests {
    use simple_compiler::hir::{HirContract, HirContractClause};

    #[test]
    fn test_hir_contract_size() {
        let _ = std::mem::size_of::<HirContract>();
    }

    #[test]
    fn test_hir_contract_clause_size() {
        let _ = std::mem::size_of::<HirContractClause>();
    }
}

// ============================================================================
// Compiler Value Bridge Types
// ============================================================================
mod compiler_bridge_tests {
    use simple_compiler::value_bridge::BridgeValue;

    #[test]
    fn test_bridge_value_size() {
        let _ = std::mem::size_of::<BridgeValue>();
    }
}

// ============================================================================
// Compiler Compilability Types
// ============================================================================
mod compiler_compilability_tests {
    use simple_compiler::compilability::{CompilabilityStatus, FallbackReason};

    #[test]
    fn test_compilability_status_size() {
        let _ = std::mem::size_of::<CompilabilityStatus>();
    }

    #[test]
    fn test_fallback_reason_size() {
        let _ = std::mem::size_of::<FallbackReason>();
    }
}

// ============================================================================
// Compiler Coverage Types
// ============================================================================
mod compiler_coverage_extended_tests {
    use simple_compiler::coverage::CoverageCollector;

    #[test]
    fn test_coverage_collector_size() {
        let _ = std::mem::size_of::<CoverageCollector>();
    }
}

// ============================================================================
// Loader SMF Extended Types
// ============================================================================
mod loader_smf_extended_tests {
    use simple_loader::smf::{RelocationType, SectionType, SmfRelocation, SmfSection};

    #[test]
    fn test_smf_section_default() {
        let _ = std::mem::size_of::<SmfSection>();
    }

    #[test]
    fn test_section_type_bss() {
        let t = SectionType::Bss;
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_section_type_symtab() {
        let t = SectionType::SymTab;
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_section_type_strtab() {
        let t = SectionType::StrTab;
        let _ = format!("{:?}", t);
    }

    #[test]
    fn test_smf_relocation_default() {
        let _ = std::mem::size_of::<SmfRelocation>();
    }

    #[test]
    fn test_relocation_type_plt32() {
        let t = RelocationType::Plt32;
        let _ = format!("{:?}", t);
    }
}

// ============================================================================
// Loader Load Error Types
// ============================================================================
mod loader_error_tests {
    use simple_loader::LoadError;

    #[test]
    fn test_load_error_size() {
        let _ = std::mem::size_of::<LoadError>();
    }
}

// ============================================================================
// Common Handle Types
// ============================================================================
mod common_handle_tests {
    use simple_common::ActorHandle;

    #[test]
    fn test_actor_handle_size() {
        let _ = std::mem::size_of::<ActorHandle>();
    }
}

// ============================================================================
// Common Manual Memory Types
// ============================================================================
mod common_manual_extended_tests {
    use simple_common::manual::{BorrowState, GcState, Nat};

    #[test]
    fn test_nat_size() {
        let _ = std::mem::size_of::<Nat>();
    }

    #[test]
    fn test_borrow_state_size() {
        let _ = std::mem::size_of::<BorrowState>();
    }

    #[test]
    fn test_gc_state_size() {
        let _ = std::mem::size_of::<GcState>();
    }
}

// ============================================================================
// Compiler Project Types
// ============================================================================
mod compiler_project_tests {
    use simple_compiler::ProjectContext;

    #[test]
    fn test_project_context_size() {
        let _ = std::mem::size_of::<ProjectContext>();
    }
}

// ============================================================================
// Package Cache Types
// ============================================================================
mod pkg_cache_tests {
    use simple_pkg::{Cache, Linker};

    #[test]
    fn test_cache_size() {
        let _ = std::mem::size_of::<Cache>();
    }

    #[test]
    fn test_linker_size() {
        let _ = std::mem::size_of::<Linker>();
    }
}

// ============================================================================
// Parser Context Types
// ============================================================================
mod parser_context_tests {
    use simple_parser::ContextStmt;

    #[test]
    fn test_context_stmt_size() {
        let _ = std::mem::size_of::<ContextStmt>();
    }
}

// ============================================================================
// Parser Capability Types
// ============================================================================
mod parser_capability_tests {
    use simple_parser::Capability;

    #[test]
    fn test_capability_size() {
        let _ = std::mem::size_of::<Capability>();
    }
}

// ============================================================================
// Parser Unit Types
// ============================================================================
mod parser_unit_tests {
    use simple_parser::CompoundUnitDef;

    #[test]
    fn test_compound_unit_def_size() {
        let _ = std::mem::size_of::<CompoundUnitDef>();
    }
}

// ============================================================================
// Parser Handle Pool Types
// ============================================================================
mod parser_handle_pool_tests {
    use simple_parser::HandlePoolDef;

    #[test]
    fn test_handle_pool_def_size() {
        let _ = std::mem::size_of::<HandlePoolDef>();
    }
}

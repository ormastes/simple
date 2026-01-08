//! MIR lowering from HIR
//!
//! This module handles the transformation of High-level IR (HIR) to Mid-level IR (MIR),
//! including contract checking, dependency injection, GPU intrinsics, and coverage instrumentation.

// Module declarations
mod lowering_core;
mod lowering_types;
mod lowering_contracts;
mod lowering_stmt;
mod lowering_expr;
mod lowering_di;
mod lowering_gpu;
mod lowering_coverage;

#[cfg(test)]
mod tests;

// Re-export the main types and functions
pub use lowering_core::{
    ContractContext, ContractMode, LoopContext, LowererState, MirLowerer, MirLowerError,
    MirLowerResult,
};

// Re-export public API functions
use crate::hir::HirModule;
use crate::mir::function::MirModule;

/// Lower HIR to MIR with default contract mode (All).
pub fn lower_to_mir(hir: &HirModule) -> MirLowerResult<MirModule> {
    MirLowerer::new()
        .with_refined_types(&hir.refined_types)
        .with_type_registry(&hir.types)
        .with_trait_infos(&hir.trait_infos)
        .lower_module(hir)
}

/// Lower HIR to MIR with a specific contract mode.
pub fn lower_to_mir_with_mode(
    hir: &HirModule,
    contract_mode: ContractMode,
) -> MirLowerResult<MirModule> {
    MirLowerer::with_contract_mode(contract_mode)
        .with_refined_types(&hir.refined_types)
        .with_type_registry(&hir.types)
        .with_trait_infos(&hir.trait_infos)
        .lower_module(hir)
}

/// Lower HIR to MIR with contract mode and DI configuration.
pub fn lower_to_mir_with_mode_and_di(
    hir: &HirModule,
    contract_mode: ContractMode,
    di_config: Option<crate::di::DiConfig>,
) -> MirLowerResult<MirModule> {
    MirLowerer::with_contract_mode(contract_mode)
        .with_di_config(di_config)
        .with_refined_types(&hir.refined_types)
        .with_type_registry(&hir.types)
        .with_trait_infos(&hir.trait_infos)
        .lower_module(hir)
}

/// Apply AOP weaving to a MIR module.
/// Returns statistics about the weaving process.
pub fn apply_weaving(
    mir_module: &mut MirModule,
    aop_config: &crate::aop_config::AopConfig,
) -> Vec<crate::weaving::WeavingResult> {
    let weaving_config = crate::weaving::WeavingConfig::from_aop_config(aop_config);
    let weaver = crate::weaving::Weaver::new(weaving_config);

    mir_module
        .functions
        .iter_mut()
        .map(|func| weaver.weave_function(func))
        .collect()
}

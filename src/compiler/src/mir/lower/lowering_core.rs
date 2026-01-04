//! Core MIR lowering infrastructure
//!
//! This module contains the main `MirLowerer` struct definition,
//! constructors, state management methods, and the primary `lower_module` entry point.

use super::super::{
    blocks::Terminator,
    effects::LocalKind,
    function::{MirFunction, MirLocal, MirModule},
    instructions::BlockId,
};
use crate::di::DiConfig;
use crate::hir::{HirExpr, HirFunction, HirModule, TypeId};
use crate::mir::instructions::VReg;
use std::collections::HashMap;
use thiserror::Error;

//==============================================================================
// Contract Mode (CTR-040 to CTR-043)
//==============================================================================

/// Contract checking mode (--contracts flag)
///
/// Controls when contract checks (preconditions, postconditions, invariants)
/// are emitted during compilation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ContractMode {
    /// No contract checks emitted (CTR-040)
    Off,
    /// Only check contracts at public API boundaries (CTR-041)
    Boundary,
    /// Check all contracts (default) (CTR-042)
    #[default]
    All,
    /// Test mode: Check all contracts with rich diagnostics (CTR-043)
    ///
    /// In test mode, contract violations include:
    /// - Full function name and signature
    /// - The exact expression that failed
    /// - Source location (file, line, column) if available
    /// - Stack trace information
    Test,
}

impl ContractMode {
    /// Parse contract mode from string (CLI flag value)
    pub fn from_str(s: &str) -> Option<Self> {
        match s.to_lowercase().as_str() {
            "off" | "none" => Some(ContractMode::Off),
            "boundary" | "public" => Some(ContractMode::Boundary),
            "all" | "on" => Some(ContractMode::All),
            "test" | "debug" => Some(ContractMode::Test),
            _ => None,
        }
    }

    /// Get string representation for CLI/config
    pub fn as_str(&self) -> &'static str {
        match self {
            ContractMode::Off => "off",
            ContractMode::Boundary => "boundary",
            ContractMode::All => "all",
            ContractMode::Test => "test",
        }
    }

    /// Returns true if this mode includes rich diagnostics (CTR-043)
    pub fn has_rich_diagnostics(&self) -> bool {
        matches!(self, ContractMode::Test)
    }

    /// Returns true if this mode checks all contracts
    pub fn checks_all(&self) -> bool {
        matches!(self, ContractMode::All | ContractMode::Test)
    }
}

//==============================================================================
// Explicit State Machine (for formal verification)
//==============================================================================

/// Loop context for break/continue handling
#[derive(Debug, Clone)]
pub struct LoopContext {
    /// Block to jump to on `continue`
    pub continue_target: BlockId,
    /// Block to jump to on `break`
    pub break_target: BlockId,
}

/// Context for contract lowering
#[derive(Debug, Clone, Default)]
pub struct ContractContext {
    /// Captured old() values: maps index to VReg holding the captured value
    pub old_captures: HashMap<usize, VReg>,
    /// Maps index to the HirExpr that was captured (for reverse lookup during lowering)
    pub old_expr_map: HashMap<usize, HirExpr>,
    /// VReg holding the return value (set before postcondition checks)
    pub return_value: Option<VReg>,
    /// Function name for error messages
    pub func_name: String,
    /// Whether the function is public (for boundary mode checks)
    pub is_public: bool,
}

/// Explicit lowerer state - makes state transitions verifiable
#[derive(Debug)]
pub enum LowererState {
    /// Not currently lowering any function
    Idle,
    /// Actively lowering a function
    Lowering {
        func: MirFunction,
        current_block: BlockId,
        loop_stack: Vec<LoopContext>,
        /// Contract context for Design by Contract support
        contract_ctx: ContractContext,
    },
}

impl LowererState {
    /// Check if we're in idle state
    pub fn is_idle(&self) -> bool {
        matches!(self, LowererState::Idle)
    }

    /// Check if we're lowering
    pub fn is_lowering(&self) -> bool {
        matches!(self, LowererState::Lowering { .. })
    }

    /// Get current block ID (returns error if idle)
    pub fn try_current_block(&self) -> MirLowerResult<BlockId> {
        match self {
            LowererState::Lowering { current_block, .. } => Ok(*current_block),
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Get mutable reference to function (returns error if idle)
    pub fn try_func_mut(&mut self) -> MirLowerResult<&mut MirFunction> {
        match self {
            LowererState::Lowering { func, .. } => Ok(func),
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    fn idle_state_error() -> MirLowerError {
        MirLowerError::InvalidState {
            expected: "Lowering".to_string(),
            found: "Idle".to_string(),
        }
    }

    /// Get loop stack (returns error if idle)
    pub fn try_loop_stack(&self) -> MirLowerResult<&Vec<LoopContext>> {
        match self {
            LowererState::Lowering { loop_stack, .. } => Ok(loop_stack),
            LowererState::Idle => Err(Self::idle_state_error()),
        }
    }

    /// Get mutable loop stack (returns error if idle)
    pub fn try_loop_stack_mut(&mut self) -> MirLowerResult<&mut Vec<LoopContext>> {
        match self {
            LowererState::Lowering { loop_stack, .. } => Ok(loop_stack),
            LowererState::Idle => Err(Self::idle_state_error()),
        }
    }

    /// Set current block (returns error if idle)
    pub fn try_set_current_block(&mut self, block: BlockId) -> MirLowerResult<()> {
        match self {
            LowererState::Lowering { current_block, .. } => {
                *current_block = block;
                Ok(())
            }
            LowererState::Idle => Err(Self::idle_state_error()),
        }
    }

    /// Get loop depth for verification
    pub fn loop_depth(&self) -> usize {
        match self {
            LowererState::Lowering { loop_stack, .. } => loop_stack.len(),
            LowererState::Idle => 0,
        }
    }
}

#[derive(Error, Debug)]
pub enum MirLowerError {
    #[error("Unsupported HIR construct: {0}")]
    Unsupported(String),
    #[error("Invalid state: expected {expected}, found {found}")]
    InvalidState { expected: String, found: String },
    #[error("Break outside loop")]
    BreakOutsideLoop,
    #[error("Continue outside loop")]
    ContinueOutsideLoop,
    #[error("AOP weaving failed: {0}")]
    AopWeavingFailed(String),
    #[error("Circular dependency detected in DI: {0}")]
    CircularDependency(String),
}

pub type MirLowerResult<T> = Result<T, MirLowerError>;

/// Lowers HIR to MIR with explicit state tracking
pub struct MirLowerer<'a> {
    pub(super) state: LowererState,
    /// Contract checking mode
    pub(super) contract_mode: ContractMode,
    /// Reference to refined types for emitting refinement checks (CTR-020)
    pub(super) refined_types: Option<&'a std::collections::HashMap<String, crate::hir::HirRefinedType>>,
    /// Reference to type registry for looking up unit type constraints
    pub(super) type_registry: Option<&'a crate::hir::TypeRegistry>,
    /// DI configuration for constructor injection
    pub(super) di_config: Option<DiConfig>,
    /// Map of injectable function names to parameter types and inject flags (#1013)
    pub(super) inject_functions: HashMap<String, Vec<(TypeId, bool)>>,
    /// Singleton instance cache for DI (impl_type -> VReg)
    pub(super) singleton_cache: HashMap<String, super::super::instructions::VReg>,
    /// Dependency graph for cycle detection (#1009)
    pub(super) dependency_graph: crate::di::DependencyGraph,
    /// Current DI resolution stack for cycle detection
    pub(super) di_resolution_stack: Vec<String>,
    /// Coverage instrumentation mode
    pub(super) coverage_enabled: bool,
    /// Counter for generating unique decision IDs
    pub(super) decision_counter: u32,
    /// Current file being lowered (for coverage source locations)
    pub(super) current_file: Option<String>,
}

impl<'a> MirLowerer<'a> {
    pub fn new() -> Self {
        Self {
            state: LowererState::Idle,
            contract_mode: ContractMode::All,
            refined_types: None,
            type_registry: None,
            di_config: None,
            inject_functions: HashMap::new(),
            singleton_cache: HashMap::new(),
            dependency_graph: crate::di::DependencyGraph::default(),
            di_resolution_stack: Vec::new(),
            coverage_enabled: false,
            decision_counter: 0,
            current_file: None,
        }
    }

    /// Create a lowerer with a specific contract mode
    pub fn with_contract_mode(contract_mode: ContractMode) -> Self {
        Self {
            state: LowererState::Idle,
            contract_mode,
            refined_types: None,
            type_registry: None,
            di_config: None,
            inject_functions: HashMap::new(),
            singleton_cache: HashMap::new(),
            dependency_graph: crate::di::DependencyGraph::default(),
            di_resolution_stack: Vec::new(),
            coverage_enabled: false,
            decision_counter: 0,
            current_file: None,
        }
    }

    pub fn with_di_config(mut self, di_config: Option<DiConfig>) -> Self {
        self.di_config = di_config;
        self
    }

    /// Enable coverage instrumentation
    pub fn with_coverage(mut self, enabled: bool) -> Self {
        self.coverage_enabled = enabled;
        self
    }

    /// Set the current file for coverage source locations
    pub fn with_file(mut self, file: String) -> Self {
        self.current_file = Some(file);
        self
    }

    /// Set refined types reference for emitting refinement checks (CTR-020)
    pub fn with_refined_types(mut self, refined_types: &'a std::collections::HashMap<String, crate::hir::HirRefinedType>) -> Self {
        self.refined_types = Some(refined_types);
        self
    }

    /// Set type registry reference for looking up unit type constraints
    pub fn with_type_registry(mut self, registry: &'a crate::hir::TypeRegistry) -> Self {
        self.type_registry = Some(registry);
        self
    }

    /// Get the current contract mode
    pub fn contract_mode(&self) -> ContractMode {
        self.contract_mode
    }

    /// Check if contracts should be emitted for the current function
    /// based on the contract mode and function visibility.
    pub(super) fn should_emit_contracts(&self) -> bool {
        match self.contract_mode {
            ContractMode::Off => false,
            ContractMode::Boundary => {
                // Only emit for public functions
                self.try_contract_ctx()
                    .map(|ctx| ctx.is_public)
                    .unwrap_or(false)
            }
            ContractMode::All | ContractMode::Test => true,
        }
    }

    /// Get current state for verification
    pub fn state(&self) -> &LowererState {
        &self.state
    }

    /// Transition from Idle to Lowering - explicit state transition
    pub(super) fn begin_function(&mut self, func: MirFunction, func_name: &str, is_public: bool) -> MirLowerResult<()> {
        match &self.state {
            LowererState::Idle => {
                self.state = LowererState::Lowering {
                    func,
                    current_block: BlockId(0),
                    loop_stack: Vec::new(),
                    contract_ctx: ContractContext {
                        old_captures: HashMap::new(),
                        old_expr_map: HashMap::new(),
                        return_value: None,
                        func_name: func_name.to_string(),
                        is_public,
                    },
                };
                Ok(())
            }
            LowererState::Lowering { .. } => Err(MirLowerError::InvalidState {
                expected: "Idle".to_string(),
                found: "Lowering".to_string(),
            }),
        }
    }

    /// Get contract context (returns error if idle)
    pub(super) fn try_contract_ctx(&self) -> MirLowerResult<&ContractContext> {
        match &self.state {
            LowererState::Lowering { contract_ctx, .. } => Ok(contract_ctx),
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Get mutable contract context (returns error if idle)
    pub(super) fn try_contract_ctx_mut(&mut self) -> MirLowerResult<&mut ContractContext> {
        match &mut self.state {
            LowererState::Lowering { contract_ctx, .. } => Ok(contract_ctx),
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Transition from Lowering to Idle - explicit state transition
    pub(super) fn end_function(&mut self) -> MirLowerResult<MirFunction> {
        match std::mem::replace(&mut self.state, LowererState::Idle) {
            LowererState::Lowering { func, .. } => Ok(func),
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Get mutable access to current function (requires Lowering state)
    pub(super) fn with_func<T>(
        &mut self,
        f: impl FnOnce(&mut MirFunction, BlockId) -> T,
    ) -> MirLowerResult<T> {
        match &mut self.state {
            LowererState::Lowering {
                func,
                current_block,
                ..
            } => Ok(f(func, *current_block)),
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Set current block - explicit state mutation
    pub(super) fn set_current_block(&mut self, block: BlockId) -> MirLowerResult<()> {
        self.state.try_set_current_block(block)
    }

    /// Push loop context - for break/continue handling
    pub(super) fn push_loop(&mut self, ctx: LoopContext) -> MirLowerResult<()> {
        self.state.try_loop_stack_mut().map(|stack| stack.push(ctx))
    }

    /// Pop loop context
    pub(super) fn pop_loop(&mut self) -> MirLowerResult<LoopContext> {
        self.state
            .try_loop_stack_mut()?
            .pop()
            .ok_or(MirLowerError::BreakOutsideLoop)
    }

    /// Get current loop context (for break/continue)
    pub(super) fn current_loop(&self) -> Option<&LoopContext> {
        match &self.state {
            LowererState::Lowering { loop_stack, .. } => loop_stack.last(),
            LowererState::Idle => None,
        }
    }

    /// Helper to set jump target if block terminator is still Unreachable
    pub(super) fn finalize_block_jump(&mut self, target: BlockId) -> MirLowerResult<()> {
        self.with_func(|func, current_block| {
            if let Some(block) = func.block_mut(current_block) {
                if matches!(block.terminator, Terminator::Unreachable) {
                    block.terminator = Terminator::Jump(target);
                }
            }
        })
    }

    /// Lower HIR module to MIR module (main entry point)
    pub fn lower_module(mut self, hir: &'a HirModule) -> MirLowerResult<MirModule> {
        // Store reference to type registry for unit type bound checks
        self.type_registry = Some(&hir.types);
        self.inject_functions.clear();
        self.singleton_cache.clear(); // Clear singleton cache for each module
        self.dependency_graph = crate::di::DependencyGraph::default(); // Reset dependency graph per module (#1009)
        self.di_resolution_stack.clear(); // Clear DI resolution stack per module

        for func in &hir.functions {
            // For per-parameter injection (#1013), we need to track which params are injectable
            // A function is injectable if it has @inject decorator OR any parameter has @inject
            let has_any_injectable = func.inject || func.params.iter().any(|p| p.inject);
            if has_any_injectable {
                // If function-level @inject, all params without explicit @inject are injectable
                // If no function-level @inject, only params with @inject are injectable
                let param_info: Vec<(TypeId, bool)> = func.params.iter()
                    .map(|p| (p.ty, func.inject || p.inject))
                    .collect();
                self.inject_functions.insert(func.name.clone(), param_info);
            }
        }

        let mut module = MirModule::new();
        module.name = hir.name.clone();

        for func in &hir.functions {
            let mir_func = self.lower_function(func)?;
            module.functions.push(mir_func);
        }

        // Apply AOP weaving if there are advice declarations (#1000-1050)
        if !hir.aop_advices.is_empty() {
            let weaving_config = crate::weaving::WeavingConfig::from_hir_advices(&hir.aop_advices);
            let weaver = crate::weaving::Weaver::new(weaving_config);

            let mut total_join_points = 0;
            let mut total_advices = 0;
            let mut all_diagnostics = Vec::new();

            for func in &mut module.functions {
                let result = weaver.weave_function(func);
                total_join_points += result.join_points_woven;
                total_advices += result.advices_inserted;
                all_diagnostics.extend(result.diagnostics);
            }

            // Report weaving summary and diagnostics
            if total_join_points > 0 {
                tracing::info!(
                    "AOP weaving complete: {} advice calls at {} join points",
                    total_advices,
                    total_join_points
                );
            }

            // Report diagnostics
            for diagnostic in &all_diagnostics {
                match diagnostic.level {
                    crate::weaving::DiagnosticLevel::Error => {
                        tracing::error!(
                            "AOP weaving error{}: {}{}",
                            diagnostic.location.as_ref().map(|l| format!(" in {}", l)).unwrap_or_default(),
                            diagnostic.message,
                            diagnostic.predicate.as_ref().map(|p| format!(" (predicate: {})", p)).unwrap_or_default()
                        );
                    }
                    crate::weaving::DiagnosticLevel::Warning => {
                        tracing::warn!(
                            "AOP weaving warning{}: {}{}",
                            diagnostic.location.as_ref().map(|l| format!(" in {}", l)).unwrap_or_default(),
                            diagnostic.message,
                            diagnostic.predicate.as_ref().map(|p| format!(" (predicate: {})", p)).unwrap_or_default()
                        );
                    }
                    crate::weaving::DiagnosticLevel::Info => {
                        tracing::info!(
                            "AOP weaving{}: {}",
                            diagnostic.location.as_ref().map(|l| format!(" in {}", l)).unwrap_or_default(),
                            diagnostic.message
                        );
                    }
                }
            }

            // Fail compilation if there are errors
            let error_count = all_diagnostics.iter()
                .filter(|d| d.level == crate::weaving::DiagnosticLevel::Error)
                .count();
            if error_count > 0 {
                return Err(MirLowerError::AopWeavingFailed(format!(
                    "{} weaving error(s) occurred",
                    error_count
                )));
            }
        }

        Ok(module)
    }

    /// Lower a single HIR function to MIR function
    pub(super) fn lower_function(&mut self, func: &HirFunction) -> MirLowerResult<MirFunction> {
        let mut mir_func = MirFunction::new(func.name.clone(), func.return_type, func.visibility);

        // Populate metadata for AOP join point matching
        mir_func.module_path = self.current_module_path();
        mir_func.attributes = self.extract_function_attributes(func);
        mir_func.effects = self.extract_function_effects(func);

        // Propagate layout hints for code locality optimization
        mir_func.layout_phase = func.layout_phase();
        mir_func.is_event_loop_anchor = func.is_event_loop_anchor();

        // Add parameters
        for param in &func.params {
            mir_func.params.push(MirLocal {
                name: param.name.clone(),
                ty: param.ty,
                kind: LocalKind::Parameter,
                is_ghost: param.is_ghost,
            });
        }

        // Add locals
        for local in &func.locals {
            mir_func.locals.push(MirLocal {
                name: local.name.clone(),
                ty: local.ty,
                kind: LocalKind::Local,
                is_ghost: local.is_ghost,
            });
        }

        // Explicit state transition: Idle -> Lowering
        self.begin_function(mir_func, &func.name, func.is_public())?;

        // Emit entry contract checks (preconditions, old captures, invariants)
        // based on contract mode
        if let Some(ref contract) = func.contract {
            if self.should_emit_contracts() {
                self.emit_entry_contracts(contract)?;
            }
        }

        // Lower body
        for stmt in &func.body {
            self.lower_stmt(stmt, func.contract.as_ref())?;
        }

        // Ensure void functions have a return (non-void functions should have explicit returns)
        // Only convert Unreachable to Return(None) for void functions.
        // For non-void functions, if we reach an Unreachable block, it means all paths
        // returned earlier (e.g., if/else with returns in both branches), so we leave
        // the terminator as Unreachable (dead code).
        let is_void = func.return_type == TypeId::VOID;
        self.with_func(|mir_func, current_block| {
            if let Some(block) = mir_func.block_mut(current_block) {
                if matches!(block.terminator, Terminator::Unreachable) && is_void {
                    block.terminator = Terminator::Return(None);
                }
            }
        })?;

        // Explicit state transition: Lowering -> Idle
        self.end_function()
    }
}

impl<'a> Default for MirLowerer<'a> {
    fn default() -> Self {
        Self::new()
    }
}

//! Core MIR lowering infrastructure
//!
//! This module contains the main `MirLowerer` struct definition,
//! constructors, state management methods, and the primary `lower_module` entry point.

use super::super::{
    blocks::Terminator,
    effects::{CallTarget, LocalKind},
    function::{MirFunction, MirLocal, MirModule},
    instructions::{BlockId, MirInst},
};
use crate::di::DiConfig;
use crate::hir::{BinOp, HirContract, HirExpr, HirExprKind, HirFunction, HirModule, HirStmt, TypeId};
use crate::mir::instructions::VReg;
use std::collections::{HashMap, HashSet};
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
    #[allow(clippy::should_implement_trait)] // reason: standard trait signature does not match this fallible or extended variant
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ArrayLenBoundProof {
    pub array_local_index: usize,
    pub index_local_index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ArrayAppendBoundProof {
    pub array_local_index: usize,
    pub index_local_index: usize,
    pub capacity_local_index: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct ArrayAppendPtrs {
    pub array_local_index: usize,
    pub index_local_index: usize,
    pub capacity_local_index: usize,
    pub header_ptr: VReg,
    pub data_ptr: VReg,
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
#[allow(clippy::large_enum_variant)] // reason: enum variant sizes are bounded; Box refactor deferred
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
        /// Stack of deferred statement blocks (executed in LIFO order at scope exit)
        defer_stack: Vec<Vec<HirStmt>>,
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

    /// Get mutable defer stack (returns error if idle)
    pub fn try_defer_stack_mut(&mut self) -> MirLowerResult<&mut Vec<Vec<HirStmt>>> {
        match self {
            LowererState::Lowering { defer_stack, .. } => Ok(defer_stack),
            LowererState::Idle => Err(Self::idle_state_error()),
        }
    }

    /// Get defer stack (returns error if idle)
    pub fn try_defer_stack(&self) -> MirLowerResult<&Vec<Vec<HirStmt>>> {
        match self {
            LowererState::Lowering { defer_stack, .. } => Ok(defer_stack),
            LowererState::Idle => Err(Self::idle_state_error()),
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
    /// Reference to trait infos for vtable slot resolution (static polymorphism)
    pub(super) trait_infos: Option<&'a std::collections::HashMap<String, crate::hir::HirTraitInfo>>,
    /// Project-wide trait implementations for cross-module vtable dispatch.
    pub(super) global_trait_impls: Option<&'a std::collections::HashMap<String, Vec<String>>>,
    /// DI configuration for constructor injection
    pub(super) di_config: Option<DiConfig>,
    /// Active DI profile for selecting profile-specific bindings.
    pub(super) di_profile: String,
    /// Map of injectable function names to parameter types, source type hints, and inject flags (#1013)
    pub(super) inject_functions: HashMap<String, Vec<(TypeId, Option<String>, bool)>>,
    /// All lowered function names, used by convention DI to avoid inventing constructors.
    pub(super) available_functions: HashSet<String>,
    /// Parameter types for direct function calls whose global expression only carries return type.
    pub(super) function_param_types: HashMap<String, Vec<TypeId>>,
    /// Cross-module private-helper collisions: bare `_name` defined by several
    /// co-compiled files with differing signatures (import flattening merges
    /// them; codegen name maps are last-write-wins → wrong-variant dispatch /
    /// SIGSEGV, e.g. `_sin(f32)` vs `_sin(f64)` in rollball). Maps bare name →
    /// definitions in lowering order as (param types, mangled name). Defs are
    /// emitted under the mangled name; call sites resolve by exact arg-type
    /// match, falling back to the extern decl (if any) then the last def
    /// (= previous behavior). See
    /// doc/08_tracking/bug/cranelift_f32_trig_wrapper_codegen_2026-07-02.md.
    pub(super) private_dup_overloads: HashMap<String, Vec<(Vec<TypeId>, String)>>,
    /// Extern fn names for the module being lowered (dup-overload fallback).
    pub(super) extern_fn_name_set: HashSet<String>,
    /// Types of HIR globals, used to recover method calls parsed as `GLOBAL.method`.
    pub(super) global_types: HashMap<String, TypeId>,
    /// Function-typed globals whose calls must load the stored closure value.
    pub(super) function_value_globals: HashSet<String>,
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
    /// Counter for generating unique condition IDs per decision
    pub(super) condition_counters: HashMap<u32, u32>,
    /// Counter for generating unique path IDs (function entry coverage)
    pub(super) path_counter: u32,
    /// Current file being lowered (for coverage source locations)
    pub(super) current_file: Option<String>,
    /// Last expression value for implicit returns (non-void functions)
    pub(super) last_expr_value: Option<super::super::instructions::VReg>,
    /// VRegs known to hold tagged RuntimeValues (from runtime function calls, BoxInt, etc.)
    /// Used to avoid double-tagging when enum payloads flow into typed variables.
    pub(super) tagged_vregs: std::collections::HashSet<super::super::instructions::VReg>,
    /// Local indices known to hold tagged RuntimeValues
    pub(super) tagged_locals: std::collections::HashSet<usize>,
    /// Locals known to hold the current length of an array local.
    pub(super) len_local_sources: HashMap<usize, usize>,
    /// Array locals known to have been created with a capacity local.
    pub(super) array_capacity_local_sources: HashMap<usize, usize>,
    /// Active loop-body proofs of `index < array.len()`.
    pub(super) active_array_len_bounds: Vec<ArrayLenBoundProof>,
    /// Active loop-body proofs that `array.push(x)` targets slot `index`.
    pub(super) active_array_append_bounds: Vec<ArrayAppendBoundProof>,
    /// Hoisted array header/data pointers for proven append loops.
    pub(super) active_array_append_ptrs: Vec<ArrayAppendPtrs>,
    /// Hoisted array data pointers for read-only loops with active length proofs.
    pub(super) active_array_data_ptrs: Vec<(usize, VReg)>,
    /// Array locals allocated only to receive ignored appends.
    pub(super) dead_append_array_locals: HashSet<usize>,
}

impl<'a> MirLowerer<'a> {
    pub fn new() -> Self {
        Self {
            state: LowererState::Idle,
            contract_mode: ContractMode::All,
            refined_types: None,
            type_registry: None,
            trait_infos: None,
            global_trait_impls: None,
            di_config: None,
            di_profile: "default".to_string(),
            inject_functions: HashMap::new(),
            available_functions: HashSet::new(),
            function_param_types: HashMap::new(),
            private_dup_overloads: HashMap::new(),
            extern_fn_name_set: HashSet::new(),
            global_types: HashMap::new(),
            function_value_globals: HashSet::new(),
            singleton_cache: HashMap::new(),
            dependency_graph: crate::di::DependencyGraph::default(),
            di_resolution_stack: Vec::new(),
            coverage_enabled: false,
            decision_counter: 0,
            condition_counters: HashMap::new(),
            path_counter: 0,
            current_file: None,
            last_expr_value: None,
            tagged_vregs: std::collections::HashSet::new(),
            tagged_locals: std::collections::HashSet::new(),
            len_local_sources: HashMap::new(),
            array_capacity_local_sources: HashMap::new(),
            active_array_len_bounds: Vec::new(),
            active_array_append_bounds: Vec::new(),
            active_array_append_ptrs: Vec::new(),
            active_array_data_ptrs: Vec::new(),
            dead_append_array_locals: HashSet::new(),
        }
    }

    /// Create a lowerer with a specific contract mode
    pub fn with_contract_mode(contract_mode: ContractMode) -> Self {
        Self {
            state: LowererState::Idle,
            contract_mode,
            refined_types: None,
            type_registry: None,
            trait_infos: None,
            global_trait_impls: None,
            di_config: None,
            di_profile: "default".to_string(),
            inject_functions: HashMap::new(),
            available_functions: HashSet::new(),
            function_param_types: HashMap::new(),
            private_dup_overloads: HashMap::new(),
            extern_fn_name_set: HashSet::new(),
            global_types: HashMap::new(),
            function_value_globals: HashSet::new(),
            singleton_cache: HashMap::new(),
            dependency_graph: crate::di::DependencyGraph::default(),
            di_resolution_stack: Vec::new(),
            coverage_enabled: false,
            tagged_vregs: std::collections::HashSet::new(),
            tagged_locals: std::collections::HashSet::new(),
            len_local_sources: HashMap::new(),
            array_capacity_local_sources: HashMap::new(),
            active_array_len_bounds: Vec::new(),
            active_array_append_bounds: Vec::new(),
            active_array_append_ptrs: Vec::new(),
            active_array_data_ptrs: Vec::new(),
            dead_append_array_locals: HashSet::new(),
            decision_counter: 0,
            condition_counters: HashMap::new(),
            path_counter: 0,
            current_file: None,
            last_expr_value: None,
        }
    }

    pub fn with_di_config(mut self, di_config: Option<DiConfig>) -> Self {
        self.di_config = di_config;
        self
    }

    pub fn with_di_profile(mut self, profile: impl Into<String>) -> Self {
        self.di_profile = profile.into();
        self
    }

    /// Enable coverage instrumentation
    pub fn with_coverage(mut self, enabled: bool) -> Self {
        self.coverage_enabled = enabled;
        self
    }

    pub(super) fn local_index_for_expr(expr: &HirExpr) -> Option<usize> {
        match &expr.kind {
            HirExprKind::Local(idx) => Some(*idx),
            _ => None,
        }
    }

    pub(super) fn array_local_for_len_expr(expr: &HirExpr) -> Option<usize> {
        match &expr.kind {
            HirExprKind::MethodCall {
                receiver, method, args, ..
            } if args.is_empty() && method == "len" => Self::local_index_for_expr(receiver),
            HirExprKind::MethodCall {
                receiver, method, args, ..
            } if args.is_empty() && matches!(method.as_str(), "to_u64" | "to_i64" | "to_usize") => {
                Self::array_local_for_len_expr(receiver)
            }
            _ => None,
        }
    }

    pub(super) fn capacity_local_for_new_array_expr(expr: &HirExpr) -> Option<usize> {
        match &expr.kind {
            HirExprKind::Call { func, args } if args.len() == 1 => {
                if matches!(&func.kind, HirExprKind::Global(name) if matches!(name.as_str(), "rt_array_new_with_cap" | "rt_array_new_with_cap_u64"))
                {
                    Self::local_index_for_expr(&args[0])
                } else {
                    None
                }
            }
            HirExprKind::MethodCall {
                receiver, method, args, ..
            } if args.is_empty() && matches!(method.as_str(), "to_u64" | "to_i64" | "to_usize") => {
                Self::capacity_local_for_new_array_expr(receiver)
            }
            _ => None,
        }
    }

    pub(super) fn record_len_local_source(&mut self, local_index: usize, value: Option<&HirExpr>) {
        self.len_local_sources.remove(&local_index);
        self.len_local_sources.retain(|_, array_idx| *array_idx != local_index);
        if let Some(array_local_index) = value.and_then(Self::array_local_for_len_expr) {
            self.len_local_sources.insert(local_index, array_local_index);
        }
    }

    pub(super) fn record_array_capacity_local_source(&mut self, local_index: usize, value: Option<&HirExpr>) {
        self.array_capacity_local_sources.remove(&local_index);
        if let Some(capacity_local_index) = value.and_then(Self::capacity_local_for_new_array_expr) {
            self.array_capacity_local_sources
                .insert(local_index, capacity_local_index);
        }
    }

    pub(super) fn loop_len_bound_proof(&self, condition: &HirExpr) -> Option<ArrayLenBoundProof> {
        let HirExprKind::Binary { op, left, right } = &condition.kind else {
            return None;
        };
        if *op != BinOp::Lt || !Self::is_unsigned_int_type(left.ty) {
            return None;
        }
        let index_local_index = Self::local_index_for_expr(left)?;
        let len_local_index = Self::local_index_for_expr(right)?;
        let array_local_index = *self.len_local_sources.get(&len_local_index)?;
        Some(ArrayLenBoundProof {
            array_local_index,
            index_local_index,
        })
    }

    pub(super) fn loop_append_bound_proof(
        &self,
        condition: &HirExpr,
        body: &[HirStmt],
    ) -> Option<ArrayAppendBoundProof> {
        let HirExprKind::Binary { op, left, right } = &condition.kind else {
            return None;
        };
        if *op != BinOp::Lt || !Self::is_unsigned_int_type(left.ty) {
            return None;
        }
        let index_local_index = Self::local_index_for_expr(left)?;
        let capacity_local_index = Self::local_index_for_expr(right)?;
        self.array_capacity_local_sources
            .iter()
            .find_map(|(array_local_index, cap_idx)| {
                (*cap_idx == capacity_local_index
                    && Self::body_is_single_append_loop(body, *array_local_index, index_local_index))
                .then_some(ArrayAppendBoundProof {
                    array_local_index: *array_local_index,
                    index_local_index,
                    capacity_local_index,
                })
            })
    }

    pub(super) fn index_has_active_len_bound(&self, receiver: &HirExpr, index: &HirExpr) -> bool {
        let Some(array_local_index) = Self::local_index_for_expr(receiver) else {
            return false;
        };
        let Some(index_local_index) = Self::local_index_for_expr(index) else {
            return false;
        };
        self.active_array_len_bounds
            .iter()
            .any(|proof| proof.array_local_index == array_local_index && proof.index_local_index == index_local_index)
    }

    pub(super) fn active_array_data_ptr(&self, receiver: &HirExpr, index: &HirExpr) -> Option<VReg> {
        if !self.index_has_active_len_bound(receiver, index) {
            return None;
        }
        let array_local_index = Self::local_index_for_expr(receiver)?;
        self.active_array_data_ptrs
            .iter()
            .rev()
            .find_map(|(idx, ptr)| (*idx == array_local_index).then_some(*ptr))
    }

    pub(super) fn active_array_append_index(&self, receiver: &HirExpr) -> Option<usize> {
        let array_local_index = Self::local_index_for_expr(receiver)?;
        self.active_array_append_bounds
            .iter()
            .rev()
            .find_map(|proof| (proof.array_local_index == array_local_index).then_some(proof.index_local_index))
    }

    pub(super) fn active_array_append_ptrs(&self, receiver: &HirExpr) -> Option<ArrayAppendPtrs> {
        let array_local_index = Self::local_index_for_expr(receiver)?;
        self.active_array_append_ptrs
            .iter()
            .rev()
            .find_map(|ptrs| (ptrs.array_local_index == array_local_index).then_some(*ptrs))
    }

    pub(super) fn is_dead_append_array_local(&self, receiver: &HirExpr) -> bool {
        Self::local_index_for_expr(receiver).is_some_and(|idx| self.dead_append_array_locals.contains(&idx))
    }

    pub(super) fn body_may_mutate_or_escape_array(body: &[HirStmt], array_local_index: usize) -> bool {
        body.iter()
            .any(|stmt| Self::stmt_may_mutate_or_escape_array(stmt, array_local_index))
    }

    fn stmt_may_mutate_or_escape_array(stmt: &HirStmt, array_local_index: usize) -> bool {
        match stmt {
            HirStmt::Assign { target, value } => {
                Self::expr_assigns_array(target, array_local_index)
                    || Self::expr_may_escape_array(value, array_local_index)
            }
            HirStmt::Expr(expr) | HirStmt::Return(Some(expr)) => Self::expr_may_escape_array(expr, array_local_index),
            HirStmt::If {
                condition,
                then_block,
                else_block,
            } => {
                Self::expr_may_escape_array(condition, array_local_index)
                    || Self::body_may_mutate_or_escape_array(then_block, array_local_index)
                    || else_block
                        .as_ref()
                        .is_some_and(|body| Self::body_may_mutate_or_escape_array(body, array_local_index))
            }
            HirStmt::While { condition, body, .. } => {
                Self::expr_may_escape_array(condition, array_local_index)
                    || Self::body_may_mutate_or_escape_array(body, array_local_index)
            }
            HirStmt::Loop { body, .. } | HirStmt::Defer { body } => {
                Self::body_may_mutate_or_escape_array(body, array_local_index)
            }
            HirStmt::For { iterable, body, .. } => {
                Self::expr_may_escape_array(iterable, array_local_index)
                    || Self::body_may_mutate_or_escape_array(body, array_local_index)
            }
            HirStmt::Return(None)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::ProofHint { .. }
            | HirStmt::Calc { .. }
            | HirStmt::InlineAsm { .. } => false,
            HirStmt::Let { value, .. } => value
                .as_ref()
                .is_some_and(|expr| Self::expr_may_escape_array(expr, array_local_index)),
            HirStmt::Assert { condition, .. }
            | HirStmt::Assume { condition, .. }
            | HirStmt::Admit { condition, .. } => Self::expr_may_escape_array(condition, array_local_index),
        }
    }

    fn expr_assigns_array(expr: &HirExpr, array_local_index: usize) -> bool {
        match &expr.kind {
            HirExprKind::Local(idx) => *idx == array_local_index,
            HirExprKind::Index { receiver, .. } => Self::local_index_for_expr(receiver) == Some(array_local_index),
            _ => false,
        }
    }

    fn expr_may_escape_array(expr: &HirExpr, array_local_index: usize) -> bool {
        match &expr.kind {
            HirExprKind::Local(idx) => *idx == array_local_index,
            HirExprKind::MethodCall {
                receiver, method, args, ..
            } => {
                (Self::local_index_for_expr(receiver) == Some(array_local_index) && method != "len")
                    || args
                        .iter()
                        .any(|arg| Self::expr_may_escape_array(arg, array_local_index))
            }
            HirExprKind::Call { func, args } => {
                Self::expr_may_escape_array(func, array_local_index)
                    || args
                        .iter()
                        .any(|arg| Self::expr_may_escape_array(arg, array_local_index))
            }
            HirExprKind::Binary { left, right, .. } => {
                Self::expr_may_escape_array(left, array_local_index)
                    || Self::expr_may_escape_array(right, array_local_index)
            }
            HirExprKind::Unary { operand, .. } => Self::expr_may_escape_array(operand, array_local_index),
            HirExprKind::Index { receiver, index } => {
                Self::expr_may_escape_array(index, array_local_index)
                    || (Self::local_index_for_expr(receiver) != Some(array_local_index)
                        && Self::expr_may_escape_array(receiver, array_local_index))
            }
            HirExprKind::Tuple(items) | HirExprKind::Array(items) | HirExprKind::VecLiteral(items) => items
                .iter()
                .any(|item| Self::expr_may_escape_array(item, array_local_index)),
            _ => false,
        }
    }

    fn body_is_single_append_loop(body: &[HirStmt], array_local_index: usize, _index_local_index: usize) -> bool {
        let mut append_count = 0usize;
        for stmt in body {
            match stmt {
                HirStmt::Expr(expr) => match &expr.kind {
                    HirExprKind::MethodCall {
                        receiver, method, args, ..
                    } if method == "push"
                        && args.len() == 1
                        && Self::local_index_for_expr(receiver) == Some(array_local_index)
                        && !Self::expr_may_escape_array(&args[0], array_local_index) =>
                    {
                        append_count += 1;
                    }
                    _ if Self::expr_may_escape_array(expr, array_local_index) => return false,
                    _ => {}
                },
                HirStmt::Let { value, .. } => {
                    if value
                        .as_ref()
                        .is_some_and(|expr| Self::expr_may_escape_array(expr, array_local_index))
                    {
                        return false;
                    }
                }
                HirStmt::Assign { target, value } => {
                    if Self::expr_assigns_array(target, array_local_index)
                        || Self::expr_may_escape_array(value, array_local_index)
                    {
                        return false;
                    }
                }
                HirStmt::Assert { condition, .. }
                | HirStmt::Assume { condition, .. }
                | HirStmt::Admit { condition, .. } => {
                    if Self::expr_may_escape_array(condition, array_local_index) {
                        return false;
                    }
                }
                HirStmt::Break
                | HirStmt::Continue
                | HirStmt::Return(_)
                | HirStmt::If { .. }
                | HirStmt::While { .. }
                | HirStmt::Loop { .. }
                | HirStmt::For { .. }
                | HirStmt::Defer { .. } => return false,
                HirStmt::ProofHint { .. } | HirStmt::Calc { .. } | HirStmt::InlineAsm { .. } => {}
            }
        }
        append_count == 1
    }

    fn dead_append_array_locals_for_body(body: &[HirStmt]) -> HashSet<usize> {
        let mut candidates = Vec::new();
        Self::collect_dead_append_candidates(body, &mut candidates);
        candidates
            .into_iter()
            .filter(|local_index| {
                let mut push_count = 0usize;
                Self::body_uses_array_only_for_ignored_appends(body, *local_index, &mut push_count) && push_count > 0
            })
            .collect()
    }

    fn collect_dead_append_candidates(body: &[HirStmt], candidates: &mut Vec<usize>) {
        for stmt in body {
            match stmt {
                HirStmt::Let {
                    local_index,
                    value: Some(value),
                    ..
                } if Self::capacity_local_for_new_array_expr(value).is_some() => {
                    candidates.push(*local_index);
                }
                HirStmt::If {
                    then_block, else_block, ..
                } => {
                    Self::collect_dead_append_candidates(then_block, candidates);
                    if let Some(else_block) = else_block {
                        Self::collect_dead_append_candidates(else_block, candidates);
                    }
                }
                HirStmt::While { body, .. }
                | HirStmt::Loop { body, .. }
                | HirStmt::For { body, .. }
                | HirStmt::Defer { body } => {
                    Self::collect_dead_append_candidates(body, candidates);
                }
                _ => {}
            }
        }
    }

    fn body_uses_array_only_for_ignored_appends(
        body: &[HirStmt],
        array_local_index: usize,
        push_count: &mut usize,
    ) -> bool {
        body.iter()
            .all(|stmt| Self::stmt_uses_array_only_for_ignored_appends(stmt, array_local_index, push_count))
    }

    fn stmt_uses_array_only_for_ignored_appends(
        stmt: &HirStmt,
        array_local_index: usize,
        push_count: &mut usize,
    ) -> bool {
        match stmt {
            HirStmt::Let {
                local_index,
                value: Some(value),
                ..
            } if *local_index == array_local_index && Self::capacity_local_for_new_array_expr(value).is_some() => true,
            HirStmt::Expr(expr) => {
                if let HirExprKind::MethodCall {
                    receiver, method, args, ..
                } = &expr.kind
                {
                    if method == "push"
                        && args.len() == 1
                        && Self::local_index_for_expr(receiver) == Some(array_local_index)
                        && !Self::expr_mentions_array(&args[0], array_local_index)
                    {
                        *push_count += 1;
                        return true;
                    }
                }
                !Self::expr_mentions_array(expr, array_local_index)
            }
            HirStmt::Let { value, .. } => value
                .as_ref()
                .is_none_or(|expr| !Self::expr_mentions_array(expr, array_local_index)),
            HirStmt::Assign { target, value } => {
                !Self::expr_mentions_array(target, array_local_index)
                    && !Self::expr_mentions_array(value, array_local_index)
            }
            HirStmt::If {
                condition,
                then_block,
                else_block,
            } => {
                !Self::expr_mentions_array(condition, array_local_index)
                    && Self::body_uses_array_only_for_ignored_appends(then_block, array_local_index, push_count)
                    && else_block.as_ref().is_none_or(|body| {
                        Self::body_uses_array_only_for_ignored_appends(body, array_local_index, push_count)
                    })
            }
            HirStmt::While { condition, body, .. } => {
                !Self::expr_mentions_array(condition, array_local_index)
                    && Self::body_uses_array_only_for_ignored_appends(body, array_local_index, push_count)
            }
            HirStmt::Loop { body, .. } | HirStmt::Defer { body } => {
                Self::body_uses_array_only_for_ignored_appends(body, array_local_index, push_count)
            }
            HirStmt::For { iterable, body, .. } => {
                !Self::expr_mentions_array(iterable, array_local_index)
                    && Self::body_uses_array_only_for_ignored_appends(body, array_local_index, push_count)
            }
            HirStmt::Return(Some(expr))
            | HirStmt::Assert { condition: expr, .. }
            | HirStmt::Assume { condition: expr, .. }
            | HirStmt::Admit { condition: expr, .. } => !Self::expr_mentions_array(expr, array_local_index),
            HirStmt::Return(None)
            | HirStmt::Break
            | HirStmt::Continue
            | HirStmt::ProofHint { .. }
            | HirStmt::Calc { .. }
            | HirStmt::InlineAsm { .. } => true,
        }
    }

    fn expr_mentions_array(expr: &HirExpr, array_local_index: usize) -> bool {
        match &expr.kind {
            HirExprKind::Local(idx) => *idx == array_local_index,
            HirExprKind::MethodCall { receiver, args, .. } => {
                Self::expr_mentions_array(receiver, array_local_index)
                    || args.iter().any(|arg| Self::expr_mentions_array(arg, array_local_index))
            }
            HirExprKind::Call { func, args } => {
                Self::expr_mentions_array(func, array_local_index)
                    || args.iter().any(|arg| Self::expr_mentions_array(arg, array_local_index))
            }
            HirExprKind::Binary { left, right, .. } => {
                Self::expr_mentions_array(left, array_local_index)
                    || Self::expr_mentions_array(right, array_local_index)
            }
            HirExprKind::Unary { operand, .. } => Self::expr_mentions_array(operand, array_local_index),
            HirExprKind::Index { receiver, index } => {
                Self::expr_mentions_array(receiver, array_local_index)
                    || Self::expr_mentions_array(index, array_local_index)
            }
            HirExprKind::Tuple(items) | HirExprKind::Array(items) | HirExprKind::VecLiteral(items) => items
                .iter()
                .any(|item| Self::expr_mentions_array(item, array_local_index)),
            _ => false,
        }
    }

    fn is_unsigned_int_type(ty: TypeId) -> bool {
        matches!(ty, TypeId::U8 | TypeId::U16 | TypeId::U32 | TypeId::U64)
    }

    /// Set the current file for coverage source locations
    pub fn with_file(mut self, file: String) -> Self {
        self.current_file = Some(file);
        self
    }

    /// Set refined types reference for emitting refinement checks (CTR-020)
    pub fn with_refined_types(
        mut self,
        refined_types: &'a std::collections::HashMap<String, crate::hir::HirRefinedType>,
    ) -> Self {
        self.refined_types = Some(refined_types);
        self
    }

    /// Set type registry reference for looking up unit type constraints
    pub fn with_type_registry(mut self, registry: &'a crate::hir::TypeRegistry) -> Self {
        self.type_registry = Some(registry);
        self
    }

    /// Set trait infos reference for vtable slot resolution (static polymorphism)
    pub fn with_trait_infos(
        mut self,
        trait_infos: &'a std::collections::HashMap<String, crate::hir::HirTraitInfo>,
    ) -> Self {
        self.trait_infos = Some(trait_infos);
        self
    }

    pub fn with_global_trait_impls(mut self, trait_impls: &'a std::collections::HashMap<String, Vec<String>>) -> Self {
        self.global_trait_impls = Some(trait_impls);
        self
    }

    /// Get vtable slot for a method on a trait
    /// Returns None if trait or method not found
    pub(super) fn get_vtable_slot(&self, trait_name: &str, method_name: &str) -> Option<u32> {
        self.trait_infos
            .and_then(|infos| infos.get(trait_name))
            .and_then(|info| info.get_vtable_slot(method_name))
    }

    /// Get method signature from a trait
    /// Returns param_types (excluding self) and return_type
    pub(super) fn get_trait_method_signature(
        &self,
        trait_name: &str,
        method_name: &str,
    ) -> Option<(Vec<crate::hir::TypeId>, crate::hir::TypeId)> {
        self.trait_infos
            .and_then(|infos| infos.get(trait_name))
            .and_then(|info| info.get_method(method_name))
            .map(|sig| (sig.param_types.clone(), sig.return_type))
    }

    /// Receiver-aware trait lookup for DispatchMode::Dynamic.
    ///
    /// A name-only trait match mis-lowers `e.name()` on a concrete class that
    /// merely SHARES a method name with some trait: the receiver has no
    /// vtable, so slot dispatch loads field data as a function pointer and
    /// segfaults (engine3d Engine3D delegation, 2026-07-03). Take the virtual
    /// path only when the receiver is statically the trait itself, is of
    /// unknown type, or actually implements a trait owning this method.
    /// Returns the sentinel slot [`crate::mir::DUCK_DISPATCH_UNSUPPORTED_SLOT`]
    /// when the call would go virtual through a trait that has NO recorded
    /// `impl Trait for Type` anywhere in the unit (duck-typing only, e.g.
    /// game2d's `App`/`GameBackend`): no constructor ever writes that vtable,
    /// so real slot dispatch would read field data as a function pointer and
    /// jump to garbage. Codegen lowers the sentinel to a named diagnostic +
    /// trap, so DEAD duck-typed sites cost nothing (unit stays JIT) and LIVE
    /// ones fail loudly instead of silently (bug
    /// jit_game2d_backend_method_dispatch_sigsegv_2026-07-02).
    pub(super) fn find_trait_for_method_on_receiver(
        &self,
        method_name: &str,
        receiver_type_name: Option<&str>,
    ) -> Option<(u32, Vec<crate::hir::TypeId>, crate::hir::TypeId)> {
        let infos = self.trait_infos?;
        let trait_is_implemented = |trait_name: &str| {
            self.dependency_graph
                .get_implementations(trait_name)
                .is_some_and(|impls| !impls.is_empty())
        };
        let slot_for = |trait_name: &str, sig: &crate::hir::HirMethodSignature| {
            if trait_is_implemented(trait_name) {
                sig.vtable_slot
            } else {
                crate::mir::DUCK_DISPATCH_UNSUPPORTED_SLOT
            }
        };
        let Some(recv) = receiver_type_name else {
            // Unknown receiver type: legacy name-based virtual dispatch.
            for (trait_name, info) in infos {
                if let Some(sig) = info.get_method(method_name) {
                    return Some((slot_for(trait_name, sig), sig.param_types.clone(), sig.return_type));
                }
            }
            return None;
        };
        // Receiver statically typed as the trait itself → virtual through it.
        if let Some(info) = infos.get(recv) {
            if let Some(sig) = info.get_method(method_name) {
                return Some((slot_for(recv, sig), sig.param_types.clone(), sig.return_type));
            }
        }
        // Concrete receiver with its own `Type.method` definition: devirtualize.
        // The static type is exact, so a direct call is always correct — and it
        // sidesteps JIT vtable dispatch, which SIGSEGVs for these units (bug
        // jit_game2d_backend_method_dispatch_sigsegv_2026-07-02: `b.init(...)`
        // on a statically-typed SoftwareBackend jumped through a bogus vtable).
        if self.available_functions.contains(&format!("{}.{}", recv, method_name)) {
            return None;
        }
        // Concrete receiver: virtual only via a trait it is known to implement
        // (e.g. inherited default trait methods with no concrete definition).
        for (trait_name, info) in infos {
            if let Some(sig) = info.get_method(method_name) {
                let implements = self
                    .dependency_graph
                    .get_implementations(trait_name)
                    .is_some_and(|impls| impls.iter().any(|t| t == recv));
                if implements {
                    return Some((sig.vtable_slot, sig.param_types.clone(), sig.return_type));
                }
            }
        }
        None
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
                self.try_contract_ctx().map(|ctx| ctx.is_public).unwrap_or(false)
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
                    defer_stack: Vec::new(),
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
    pub(super) fn with_func<T>(&mut self, f: impl FnOnce(&mut MirFunction, BlockId) -> T) -> MirLowerResult<T> {
        match &mut self.state {
            LowererState::Lowering {
                func, current_block, ..
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

    /// Push a defer body onto the defer stack
    pub(super) fn push_defer(&mut self, body: Vec<HirStmt>) -> MirLowerResult<()> {
        self.state.try_defer_stack_mut().map(|stack| stack.push(body))
    }

    /// Emit all deferred blocks in LIFO order (reverse of defer registration order).
    /// This should be called at scope exit points: return, break, continue, end of function.
    pub(super) fn emit_deferred_blocks(&mut self, contract: Option<&HirContract>) -> MirLowerResult<()> {
        // Clone the defer stack so we can iterate without borrowing self
        let deferred: Vec<Vec<HirStmt>> = self.state.try_defer_stack()?.clone();

        // Iterate in reverse (LIFO) order
        for body in deferred.iter().rev() {
            for stmt in body {
                self.lower_stmt(stmt, contract)?;
            }
        }

        Ok(())
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
        self.di_config = crate::di::merge_di_config_with_hir_graphs(self.di_config.take(), &hir.inject_graphs)
            .map_err(MirLowerError::Unsupported)?;

        // Store reference to type registry for unit type bound checks
        self.type_registry = Some(&hir.types);
        // Store reference to trait_infos for vtable slot resolution and vtable_impls construction
        if !hir.trait_infos.is_empty() {
            self.trait_infos = Some(&hir.trait_infos);
        }
        self.inject_functions.clear();
        self.available_functions.clear();
        self.function_param_types.clear();
        self.global_types = hir.globals.iter().map(|(name, ty)| (name.clone(), *ty)).collect();
        self.function_value_globals = hir.global_init_functions.keys().cloned().collect();
        self.singleton_cache.clear(); // Clear singleton cache for each module
        self.dependency_graph = crate::di::DependencyGraph::default(); // Reset dependency graph per module (#1009)
        if let Some(global_trait_impls) = self.global_trait_impls {
            for (trait_name, implementations) in global_trait_impls {
                for type_name in implementations {
                    self.dependency_graph
                        .add_implementation(trait_name.clone(), type_name.clone());
                }
            }
        }
        self.di_resolution_stack.clear(); // Clear DI resolution stack per module

        for func in &hir.functions {
            if func.name == "_append_bytes" {
                eprintln!("PROBE_MODPATH name={} module_path={:?}", func.name, func.module_path);
            }
            self.available_functions.insert(func.name.clone());
            self.function_param_types.insert(
                func.name.clone(),
                func.params.iter().filter(|p| p.name != "self").map(|p| p.ty).collect(),
            );
            // For per-parameter injection (#1013), we need to track which params are injectable
            // A function is injectable if it has @inject decorator OR any parameter has @inject
            let has_any_injectable = func.inject || func.params.iter().any(|p| p.inject);
            if has_any_injectable {
                // If function-level @inject, all params without explicit @inject are injectable
                // If no function-level @inject, only params with @inject are injectable
                let param_info: Vec<(TypeId, Option<String>, bool)> = func
                    .params
                    .iter()
                    .filter(|p| p.name != "self")
                    .map(|p| (p.ty, p.type_name_hint.clone(), func.inject || p.inject))
                    .collect();
                self.inject_functions.insert(func.name.clone(), param_info);
            }
        }

        for hir_impl in &hir.impls {
            if let Some(trait_name) = &hir_impl.trait_name {
                self.dependency_graph
                    .add_implementation(trait_name.clone(), hir_impl.type_name.clone());
            }
        }

        // Detect cross-module private-helper name collisions (see the field doc
        // on `private_dup_overloads`) and assign each colliding definition a
        // mangled name. Only bare `_`-prefixed free functions are considered —
        // methods are `Type.method`-qualified and cannot collide this way.
        self.extern_fn_name_set = hir.extern_fn_names.iter().cloned().collect();
        {
            let mut sigs_by_name: HashMap<&str, Vec<Vec<TypeId>>> = HashMap::new();
            let mut order: Vec<&str> = Vec::new();
            for func in &hir.functions {
                if !func.name.starts_with('_') || func.name.contains('.') {
                    continue;
                }
                let sig: Vec<TypeId> = func.params.iter().filter(|p| p.name != "self").map(|p| p.ty).collect();
                let entry = sigs_by_name.entry(func.name.as_str()).or_default();
                if entry.is_empty() {
                    order.push(func.name.as_str());
                }
                entry.push(sig);
            }
            for name in order {
                let sigs = &sigs_by_name[name];
                if sigs.len() < 2 || sigs.iter().all(|s| s == &sigs[0]) {
                    // Unique, or all signatures identical: last-write-wins stays
                    // observably equivalent — leave the name alone.
                    continue;
                }
                let candidates = sigs
                    .iter()
                    .enumerate()
                    .map(|(k, sig)| (sig.clone(), format!("{name}$dup{k}")))
                    .collect();
                self.private_dup_overloads.insert(name.to_string(), candidates);
            }
        }

        let mut module = MirModule::new();
        module.name = hir.name.clone();
        module.type_registry = hir.types.clone();

        // Copy extern function names from HIR to MIR
        module.extern_fn_names = hir.extern_fn_names.clone();

        // Copy compile-time constant init values from HIR to MIR
        module.global_init_values = hir.global_init_values.clone();
        module.global_init_strings = hir.global_init_strings.clone();
        module.global_init_arrays = hir.global_init_arrays.clone();
        module.global_init_structs = hir.global_init_structs.clone();
        module.global_init_functions = hir.global_init_functions.clone();

        // Copy local globals set from HIR to MIR for codegen linkage decisions
        module.local_globals = hir.local_globals.clone();

        // Copy global variables from HIR to MIR
        // IMPORTANT: HIR globals HashMap is used for name resolution and contains:
        // 1. Actual global variables (let/var at module scope)
        // 2. Static variables
        // 3. Const variables
        // 4. ALL function names (both regular and extern) with their RETURN TYPE
        //
        // We need to filter out function names to avoid declaring them as globals.
        // Functions are handled separately via HIR functions list.
        // Build a set of function names to exclude
        let function_names: std::collections::HashSet<&str> = hir.functions.iter().map(|f| f.name.as_str()).collect();

        for (name, ty) in &hir.globals {
            // Skip if this name is a function defined in this module
            if function_names.contains(name.as_str()) {
                continue;
            }
            // Skip function names imported via `use` statements — these are only
            // used for type resolution and should not become data globals (which
            // would conflict with function import declarations in codegen).
            if hir.imported_function_names.contains(name) {
                continue;
            }

            let is_mutable = !hir.immutable_globals.contains(name);
            module.globals.push((name.clone(), *ty, is_mutable));
        }

        let mut dup_def_counters: HashMap<&str, usize> = HashMap::new();
        for func in &hir.functions {
            let mut mir_func = self.lower_function(func)?;
            // Emit colliding private-helper definitions under their mangled
            // names so every variant survives into codegen (instead of
            // last-write-wins overwriting f32/f64 siblings).
            if let Some(candidates) = self.private_dup_overloads.get(func.name.as_str()) {
                let k = dup_def_counters.entry(func.name.as_str()).or_insert(0);
                mir_func.name = candidates[*k].1.clone();
                *k += 1;
            }
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
                            diagnostic
                                .location
                                .as_ref()
                                .map(|l| format!(" in {}", l))
                                .unwrap_or_default(),
                            diagnostic.message,
                            diagnostic
                                .predicate
                                .as_ref()
                                .map(|p| format!(" (predicate: {})", p))
                                .unwrap_or_default()
                        );
                    }
                    crate::weaving::DiagnosticLevel::Warning => {
                        tracing::warn!(
                            "AOP weaving warning{}: {}{}",
                            diagnostic
                                .location
                                .as_ref()
                                .map(|l| format!(" in {}", l))
                                .unwrap_or_default(),
                            diagnostic.message,
                            diagnostic
                                .predicate
                                .as_ref()
                                .map(|p| format!(" (predicate: {})", p))
                                .unwrap_or_default()
                        );
                    }
                    crate::weaving::DiagnosticLevel::Info => {
                        tracing::info!(
                            "AOP weaving{}: {}",
                            diagnostic
                                .location
                                .as_ref()
                                .map(|l| format!(" in {}", l))
                                .unwrap_or_default(),
                            diagnostic.message
                        );
                    }
                }
            }

            // Fail compilation if there are errors
            let error_count = all_diagnostics
                .iter()
                .filter(|d| d.level == crate::weaving::DiagnosticLevel::Error)
                .count();
            if error_count > 0 {
                return Err(MirLowerError::AopWeavingFailed(format!(
                    "{} weaving error(s) occurred",
                    error_count
                )));
            }
        }

        // Build vtable_impls from hir.impls (trait impl metadata)
        // For each impl Trait for Struct, record (struct_name, vtable_sym, method_fn_names_in_slot_order)
        if let Some(trait_infos) = self.trait_infos {
            for hir_impl in &hir.impls {
                if let Some(ref trait_name) = hir_impl.trait_name {
                    if let Some(trait_info) = trait_infos.get(trait_name) {
                        let vtable_sym = format!("__vtable__{}__for__{}", hir_impl.type_name, trait_name);
                        // Build method function names in vtable slot order
                        let mut slot_fns: Vec<(u32, String)> = trait_info
                            .methods
                            .iter()
                            .filter_map(|(method_name, sig)| {
                                hir_impl
                                    .methods
                                    .get(method_name)
                                    .map(|fn_name| (sig.vtable_slot, fn_name.clone()))
                            })
                            .collect();
                        slot_fns.sort_by_key(|(slot, _)| *slot);
                        let method_fns: Vec<String> = slot_fns.into_iter().map(|(_, fn_name)| fn_name).collect();
                        module.vtable_impls.push((
                            hir_impl.type_id,
                            hir_impl.type_name.clone(),
                            vtable_sym,
                            method_fns,
                        ));
                    }
                }
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

        // Reset last expression value for this function
        self.last_expr_value = None;
        self.dead_append_array_locals = Self::dead_append_array_locals_for_body(&func.body);

        // Emit function entry path probe for coverage (#674)
        self.emit_function_entry_probe()?;

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

        // Emit deferred blocks at end of function body (implicit return path)
        self.emit_deferred_blocks(func.contract.as_ref())?;

        // Handle implicit returns and void function terminators
        let is_void = func.return_type == TypeId::VOID;
        let last_expr = self.last_expr_value;
        self.with_func(|mir_func, current_block| {
            if let Some(block) = mir_func.block_mut(current_block) {
                if matches!(block.terminator, Terminator::Unreachable) {
                    if is_void {
                        // Void function: return nothing
                        block.terminator = Terminator::Return(None);
                    } else if let Some(vreg) = last_expr {
                        // Non-void function with implicit return: use last expression value
                        block.terminator = Terminator::Return(Some(vreg));
                    }
                    // If no last_expr and not void, leave as Unreachable (will trap - indicates bug)
                }
            }
        })?;

        self.drop_unused_collection_write_results()?;

        // Explicit state transition: Lowering -> Idle
        self.end_function()
    }

    fn drop_unused_collection_write_results(&mut self) -> MirLowerResult<()> {
        self.with_func(|mir_func, _| {
            let mut used = HashSet::new();
            for block in &mir_func.blocks {
                for inst in &block.instructions {
                    for reg in inst.uses() {
                        used.insert(reg);
                    }
                }
                for reg in block.terminator.uses() {
                    used.insert(reg);
                }
            }

            for block in &mut mir_func.blocks {
                for inst in &mut block.instructions {
                    if let MirInst::Call { dest, target, .. } = inst {
                        if dest.is_some_and(|reg| !used.contains(&reg))
                            && Self::is_collection_write_result_discardable(target)
                        {
                            *dest = None;
                        }
                    }
                }
            }
        })
    }

    fn is_collection_write_result_discardable(target: &CallTarget) -> bool {
        matches!(
            target.name(),
            "rt_typed_bytes_u8_push"
                | "rt_typed_words_u32_push"
                | "rt_typed_words_u64_push"
                | "rt_typed_words_u32_push_known_at"
                | "rt_typed_words_u64_push_known_at"
                | "rt_typed_words_u32_push_known_data_at"
                | "rt_typed_words_u64_push_known_data_at"
                | "rt_typed_words_u32_store_known_data_at"
                | "rt_typed_words_u64_store_known_data_at"
                | "rt_typed_words_u32_set"
                | "rt_typed_words_u64_set"
        )
    }
}

impl<'a> Default for MirLowerer<'a> {
    fn default() -> Self {
        Self::new()
    }
}

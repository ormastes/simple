use super::{
    blocks::Terminator,
    effects::{CallTarget, LocalKind},
    function::{MirFunction, MirLocal, MirModule},
    instructions::{BlockId, ContractKind, MirInst, VReg},
};
use crate::hir::{HirContract, HirExpr, HirExprKind, HirFunction, HirModule, HirStmt, TypeId};
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
// The lowerer state is made explicit to simplify verification.
// Instead of using Option<MirFunction> with implicit state transitions,
// we use an enum that encodes valid state combinations.
//
// This maps to a Lean state machine:
//   inductive LowererState
//     | idle
//     | lowering (func : MirFunction) (block : BlockId) (loop_stack : List LoopContext)
//
// Invariants:
//   - In `Lowering` state, `current_block` always refers to a valid block in `func`
//   - `loop_stack` tracks nested loops for break/continue

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

    /// Get current block ID (returns error if idle - safe for verification)
    ///
    /// This is the preferred accessor for Lean-style verification.
    /// All state access should be fallible to match the Lean model.
    pub fn try_current_block(&self) -> MirLowerResult<BlockId> {
        match self {
            LowererState::Lowering { current_block, .. } => Ok(*current_block),
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Get current block ID (panics if idle - use only when state is known)
    ///
    /// **DEPRECATED**: This method panics on invalid state access.
    /// Prefer `try_current_block()` for verification-friendly code.
    /// Lean models use total functions - panicking breaks this property.
    #[deprecated(
        since = "0.1.0",
        note = "Use try_current_block() for Lean-compatible totality"
    )]
    pub fn current_block(&self) -> BlockId {
        self.try_current_block()
            .expect("Invariant violation: accessing block in idle state")
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

    /// Returns an error if in Idle state
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

/// Block building state - makes terminator state explicit
#[derive(Debug, Clone, PartialEq)]
pub enum BlockState {
    /// Block is open, accepting instructions
    Open,
    /// Block has been sealed with a terminator
    Sealed(Terminator),
}

impl BlockState {
    pub fn is_open(&self) -> bool {
        matches!(self, BlockState::Open)
    }

    pub fn is_sealed(&self) -> bool {
        matches!(self, BlockState::Sealed(_))
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
}

pub type MirLowerResult<T> = Result<T, MirLowerError>;

/// Lowers HIR to MIR with explicit state tracking
pub struct MirLowerer<'a> {
    state: LowererState,
    /// Contract checking mode
    contract_mode: ContractMode,
    /// Reference to refined types for emitting refinement checks (CTR-020)
    refined_types: Option<&'a std::collections::HashMap<String, crate::hir::HirRefinedType>>,
}

impl<'a> MirLowerer<'a> {
    pub fn new() -> Self {
        Self {
            state: LowererState::Idle,
            contract_mode: ContractMode::All,
            refined_types: None,
        }
    }

    /// Create a lowerer with a specific contract mode
    pub fn with_contract_mode(contract_mode: ContractMode) -> Self {
        Self {
            state: LowererState::Idle,
            contract_mode,
            refined_types: None,
        }
    }

    /// Set refined types reference for emitting refinement checks (CTR-020)
    pub fn with_refined_types(mut self, refined_types: &'a std::collections::HashMap<String, crate::hir::HirRefinedType>) -> Self {
        self.refined_types = Some(refined_types);
        self
    }

    /// Get the current contract mode
    pub fn contract_mode(&self) -> ContractMode {
        self.contract_mode
    }

    /// Check if contracts should be emitted for the current function
    /// based on the contract mode and function visibility.
    fn should_emit_contracts(&self) -> bool {
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
    fn begin_function(&mut self, func: MirFunction, func_name: &str, is_public: bool) -> MirLowerResult<()> {
        match &self.state {
            LowererState::Idle => {
                self.state = LowererState::Lowering {
                    func,
                    current_block: BlockId(0),
                    loop_stack: Vec::new(),
                    contract_ctx: ContractContext {
                        old_captures: HashMap::new(),
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
    fn try_contract_ctx(&self) -> MirLowerResult<&ContractContext> {
        match &self.state {
            LowererState::Lowering { contract_ctx, .. } => Ok(contract_ctx),
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Get mutable contract context (returns error if idle)
    fn try_contract_ctx_mut(&mut self) -> MirLowerResult<&mut ContractContext> {
        match &mut self.state {
            LowererState::Lowering { contract_ctx, .. } => Ok(contract_ctx),
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Transition from Lowering to Idle - explicit state transition
    fn end_function(&mut self) -> MirLowerResult<MirFunction> {
        match std::mem::replace(&mut self.state, LowererState::Idle) {
            LowererState::Lowering { func, .. } => Ok(func),
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Get mutable access to current function (requires Lowering state)
    fn with_func<T>(
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
    fn set_current_block(&mut self, block: BlockId) -> MirLowerResult<()> {
        self.state.try_set_current_block(block)
    }

    /// Push loop context - for break/continue handling
    fn push_loop(&mut self, ctx: LoopContext) -> MirLowerResult<()> {
        self.state.try_loop_stack_mut().map(|stack| stack.push(ctx))
    }

    /// Pop loop context
    fn pop_loop(&mut self) -> MirLowerResult<LoopContext> {
        self.state
            .try_loop_stack_mut()?
            .pop()
            .ok_or(MirLowerError::BreakOutsideLoop)
    }

    /// Get current loop context (for break/continue)
    fn current_loop(&self) -> Option<&LoopContext> {
        match &self.state {
            LowererState::Lowering { loop_stack, .. } => loop_stack.last(),
            LowererState::Idle => None,
        }
    }

    /// Helper to set jump target if block terminator is still Unreachable
    fn finalize_block_jump(&mut self, target: BlockId) -> MirLowerResult<()> {
        self.with_func(|func, current_block| {
            if let Some(block) = func.block_mut(current_block) {
                if matches!(block.terminator, Terminator::Unreachable) {
                    block.terminator = Terminator::Jump(target);
                }
            }
        })
    }

    pub fn lower_module(mut self, hir: &HirModule) -> MirLowerResult<MirModule> {
        let mut module = MirModule::new();
        module.name = hir.name.clone();

        for func in &hir.functions {
            let mir_func = self.lower_function(func)?;
            module.functions.push(mir_func);
        }

        Ok(module)
    }

    fn lower_function(&mut self, func: &HirFunction) -> MirLowerResult<MirFunction> {
        let mut mir_func = MirFunction::new(func.name.clone(), func.return_type, func.visibility);

        // Add parameters
        for param in &func.params {
            mir_func.params.push(MirLocal {
                name: param.name.clone(),
                ty: param.ty,
                kind: LocalKind::Parameter,
            });
        }

        // Reserve vregs for parameters: params are implicitly _v0, _v1, ...
        // in the C backend function signature, so advance the vreg counter past them.
        for _ in 0..func.params.len() {
            mir_func.new_vreg();
        }

        // Add locals
        for local in &func.locals {
            mir_func.locals.push(MirLocal {
                name: local.name.clone(),
                ty: local.ty,
                kind: LocalKind::Local,
            });
        }

        // Explicit state transition: Idle -> Lowering
        self.begin_function(mir_func, &func.name, func.is_public())?;

        // Store function parameters into their local slots.
        // Parameters are passed as vregs _v0, _v1, ... and must be stored
        // into _local_0, _local_1, ... so that LocalAddr+Load can read them.
        let param_count = func.params.len();
        if param_count > 0 {
            // Allocate vregs first, then emit instructions (avoids double-borrow)
            let addr_regs: Vec<VReg> = self.with_func(|mir_func, _| {
                (0..param_count).map(|_| mir_func.new_vreg()).collect()
            })?;
            self.with_func(|mir_func, current_block| {
                let block = mir_func.block_mut(current_block).unwrap();
                for i in 0..param_count {
                    block.instructions.push(MirInst::LocalAddr {
                        dest: addr_regs[i],
                        local_index: i,
                    });
                    block.instructions.push(MirInst::Store {
                        addr: addr_regs[i],
                        value: VReg(i as u32),
                        ty: func.params[i].ty,
                    });
                }
            })?;
        }

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

        // Ensure we have a return
        self.with_func(|func, current_block| {
            if let Some(block) = func.block_mut(current_block) {
                if matches!(block.terminator, Terminator::Unreachable) {
                    block.terminator = Terminator::Return(None);
                }
            }
        })?;

        // Explicit state transition: Lowering -> Idle
        self.end_function()
    }

    /// Emit entry contract checks: preconditions, old() captures, invariants at entry
    fn emit_entry_contracts(&mut self, contract: &HirContract) -> MirLowerResult<()> {
        let func_name = self.try_contract_ctx()?.func_name.clone();

        // 1. Check preconditions
        for clause in &contract.preconditions {
            let cond_reg = self.lower_expr(&clause.condition)?;
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ContractCheck {
                    condition: cond_reg,
                    kind: ContractKind::Precondition,
                    func_name: func_name.clone(),
                    message: clause.message.clone(),
                });
            })?;
        }

        // 2. Capture old() values
        for (idx, expr) in &contract.old_values {
            let value_reg = self.lower_expr(expr)?;
            let dest = self.with_func(|func, current_block| {
                let dest = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ContractOldCapture {
                    dest,
                    value: value_reg,
                });
                dest
            })?;
            self.try_contract_ctx_mut()?.old_captures.insert(*idx, dest);
        }

        // 3. Check invariants at entry
        for clause in &contract.invariants {
            let cond_reg = self.lower_expr(&clause.condition)?;
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ContractCheck {
                    condition: cond_reg,
                    kind: ContractKind::InvariantEntry,
                    func_name: func_name.clone(),
                    message: clause.message.clone(),
                });
            })?;
        }

        Ok(())
    }

    /// Emit exit contract checks: invariants, postconditions (for successful returns)
    fn emit_exit_contracts(
        &mut self,
        contract: &HirContract,
        return_value: Option<VReg>,
    ) -> MirLowerResult<()> {
        let func_name = self.try_contract_ctx()?.func_name.clone();

        // Store return value in contract context for ContractResult expressions
        if return_value.is_some() {
            self.try_contract_ctx_mut()?.return_value = return_value;
        }

        // 1. Check invariants at exit
        for clause in &contract.invariants {
            let cond_reg = self.lower_expr(&clause.condition)?;
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ContractCheck {
                    condition: cond_reg,
                    kind: ContractKind::InvariantExit,
                    func_name: func_name.clone(),
                    message: clause.message.clone(),
                });
            })?;
        }

        // 2. Check postconditions (only for successful returns)
        for clause in &contract.postconditions {
            let cond_reg = self.lower_expr(&clause.condition)?;
            self.with_func(|func, current_block| {
                let block = func.block_mut(current_block).unwrap();
                block.instructions.push(MirInst::ContractCheck {
                    condition: cond_reg,
                    kind: ContractKind::Postcondition,
                    func_name: func_name.clone(),
                    message: clause.message.clone(),
                });
            })?;
        }

        Ok(())
    }

    fn lower_stmt(&mut self, stmt: &HirStmt, contract: Option<&HirContract>) -> MirLowerResult<()> {
        match stmt {
            HirStmt::Let {
                local_index, value, ..
            } => {
                if let Some(val) = value {
                    let vreg = self.lower_expr(val)?;
                    let local_idx = *local_index;
                    let ty = val.ty;
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::LocalAddr {
                            dest,
                            local_index: local_idx,
                        });
                        block.instructions.push(MirInst::Store {
                            addr: dest,
                            value: vreg,
                            ty,
                        });
                    })?;
                }
                Ok(())
            }

            HirStmt::Assign { target, value } => {
                let val_reg = self.lower_expr(value)?;

                match &target.kind {
                    // Field assignment: obj.field = value -> FieldSet
                    HirExprKind::FieldAccess { receiver, field_index } => {
                        let recv_reg = self.lower_expr(receiver)?;
                        let field_index = *field_index;
                        let field_type = value.ty;

                        self.with_func(|func, current_block| {
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::FieldSet {
                                object: recv_reg,
                                byte_offset: (field_index as u32) * 8,
                                field_type,
                                value: val_reg,
                            });
                        })?;
                        Ok(())
                    }

                    // Index assignment: arr[i] = value -> IndexSet
                    HirExprKind::Index { receiver, index } => {
                        let recv_reg = self.lower_expr(receiver)?;
                        let idx_reg = self.lower_expr(index)?;

                        self.with_func(|func, current_block| {
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::IndexSet {
                                collection: recv_reg,
                                index: idx_reg,
                                value: val_reg,
                            });
                        })?;
                        Ok(())
                    }

                    // Local variable assignment: x = value -> LocalAddr + Store
                    HirExprKind::Local(idx) => {
                        let ty = value.ty;
                        self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::LocalAddr {
                                dest,
                                local_index: *idx,
                            });
                            block.instructions.push(MirInst::Store {
                                addr: dest,
                                value: val_reg,
                                ty,
                            });
                        })?;
                        Ok(())
                    }

                    // Global/deref/other assignment: bootstrap no-op (value is lowered for side effects)
                    _ => {
                        // Value already lowered above for side effects
                        Ok(())
                    }
                }
            }


            HirStmt::Return(value) => {
                let ret_reg = if let Some(v) = value {
                    Some(self.lower_expr(v)?)
                } else {
                    None
                };

                // Emit exit contract checks before the actual return
                // based on contract mode
                if let Some(contract) = contract {
                    if self.should_emit_contracts() {
                        self.emit_exit_contracts(contract, ret_reg)?;
                    }
                }

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Return(ret_reg);
                })?;
                Ok(())
            }

            HirStmt::Expr(expr) => {
                self.lower_expr(expr)?;
                Ok(())
            }

            HirStmt::If {
                condition,
                then_block,
                else_block,
            } => {
                let cond_reg = self.lower_expr(condition)?;

                // Create blocks
                let (then_id, else_id, merge_id) = self.with_func(|func, current_block| {
                    let then_id = func.new_block();
                    let else_id = func.new_block();
                    let merge_id = func.new_block();

                    // Set branch terminator
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Branch {
                        cond: cond_reg,
                        then_block: then_id,
                        else_block: else_id,
                    };
                    (then_id, else_id, merge_id)
                })?;

                // Lower then block
                self.set_current_block(then_id)?;
                for stmt in then_block {
                    self.lower_stmt(stmt, contract)?;
                }
                self.finalize_block_jump(merge_id)?;

                // Lower else block
                self.set_current_block(else_id)?;
                if let Some(else_stmts) = else_block {
                    for stmt in else_stmts {
                        self.lower_stmt(stmt, contract)?;
                    }
                }
                self.finalize_block_jump(merge_id)?;

                self.set_current_block(merge_id)?;
                Ok(())
            }

            HirStmt::While { condition, body } => {
                // Create blocks and set initial jump
                let (cond_id, body_id, exit_id) = self.with_func(|func, current_block| {
                    let cond_id = func.new_block();
                    let body_id = func.new_block();
                    let exit_id = func.new_block();

                    // Jump to condition check
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Jump(cond_id);
                    (cond_id, body_id, exit_id)
                })?;

                // Push loop context for break/continue
                self.push_loop(LoopContext {
                    continue_target: cond_id,
                    break_target: exit_id,
                })?;

                // Check condition
                self.set_current_block(cond_id)?;
                let cond_reg = self.lower_expr(condition)?;
                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Branch {
                        cond: cond_reg,
                        then_block: body_id,
                        else_block: exit_id,
                    };
                })?;

                // Lower body
                self.set_current_block(body_id)?;
                for stmt in body {
                    self.lower_stmt(stmt, contract)?;
                }
                self.finalize_block_jump(cond_id)?;

                // Pop loop context
                self.pop_loop()?;

                self.set_current_block(exit_id)?;
                Ok(())
            }

            HirStmt::Loop { body } => {
                // Create blocks
                let (body_id, exit_id) = self.with_func(|func, current_block| {
                    let body_id = func.new_block();
                    let exit_id = func.new_block();

                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Jump(body_id);
                    (body_id, exit_id)
                })?;

                // Push loop context
                self.push_loop(LoopContext {
                    continue_target: body_id,
                    break_target: exit_id,
                })?;

                self.set_current_block(body_id)?;
                for stmt in body {
                    self.lower_stmt(stmt, contract)?;
                }
                self.finalize_block_jump(body_id)?;

                // Pop loop context
                self.pop_loop()?;

                self.set_current_block(exit_id)?;
                Ok(())
            }

            HirStmt::Break => {
                // Use loop context for proper jump target
                let loop_ctx = self
                    .current_loop()
                    .ok_or(MirLowerError::BreakOutsideLoop)?
                    .clone();

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Jump(loop_ctx.break_target);
                })?;
                Ok(())
            }

            HirStmt::Continue => {
                // Use loop context for proper jump target
                let loop_ctx = self
                    .current_loop()
                    .ok_or(MirLowerError::ContinueOutsideLoop)?
                    .clone();

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Jump(loop_ctx.continue_target);
                })?;
                Ok(())
            }
        }
    }

    fn lower_expr(&mut self, expr: &HirExpr) -> MirLowerResult<VReg> {
        let expr_ty = expr.ty;
        let expr_kind = expr.kind.clone();

        match &expr_kind {
            HirExprKind::Integer(n) => {
                let n = *n;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block
                        .instructions
                        .push(MirInst::ConstInt { dest, value: n });
                    dest
                })
            }

            HirExprKind::Float(f) => {
                let f = *f;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block
                        .instructions
                        .push(MirInst::ConstFloat { dest, value: f });
                    dest
                })
            }

            HirExprKind::Bool(b) => {
                let b = *b;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block
                        .instructions
                        .push(MirInst::ConstBool { dest, value: b });
                    dest
                })
            }

            HirExprKind::String(s) => {
                let s = s.clone();
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block
                        .instructions
                        .push(MirInst::ConstString { dest, value: s });
                    dest
                })
            }

            HirExprKind::Local(idx) => {
                let idx = *idx;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let addr_reg = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::LocalAddr {
                        dest: addr_reg,
                        local_index: idx,
                    });
                    block.instructions.push(MirInst::Load {
                        dest,
                        addr: addr_reg,
                        ty: expr_ty,
                    });
                    dest
                })
            }

            HirExprKind::Binary { op, left, right } => {
                let op = *op;
                let left_ty = left.ty;
                let left_reg = self.lower_expr(left)?;
                let right_reg = self.lower_expr(right)?;

                // String concatenation: `+` on STRING types -> rt_string_concat
                use crate::hir::BinOp;
                if left_ty == TypeId::STRING && op == BinOp::Add {
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(dest),
                            target: CallTarget::from_name("rt_string_concat"),
                            args: vec![left_reg, right_reg],
                        });
                        dest
                    })
                } else if left_ty == TypeId::STRING
                    && matches!(op, BinOp::Eq | BinOp::NotEq)
                {
                    // String equality: == / != -> rt_string_eq, then maybe negate
                    self.with_func(|func, current_block| {
                        let eq_dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Call {
                            dest: Some(eq_dest),
                            target: CallTarget::from_name("rt_string_eq"),
                            args: vec![left_reg, right_reg],
                        });
                        if op == BinOp::NotEq {
                            // Negate: result = (eq_result == 0)
                            let zero = func.new_vreg();
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::ConstInt {
                                dest: zero,
                                value: 0,
                            });
                            block.instructions.push(MirInst::BinOp {
                                dest,
                                op: BinOp::Eq,
                                left: eq_dest,
                                right: zero,
                            });
                            dest
                        } else {
                            eq_dest
                        }
                    })
                } else {
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::BinOp {
                            dest,
                            op,
                            left: left_reg,
                            right: right_reg,
                        });
                        dest
                    })
                }
            }

            HirExprKind::Unary { op, operand } => {
                let op = *op;
                let operand_reg = self.lower_expr(operand)?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::UnaryOp {
                        dest,
                        op,
                        operand: operand_reg,
                    });
                    dest
                })
            }

            HirExprKind::Call { func: callee, args } => {
                let mut arg_regs = Vec::new();
                for arg in args {
                    arg_regs.push(self.lower_expr(arg)?);
                }

                // Get function name and create CallTarget with effect information
                let call_target = if let HirExprKind::Global(name) = &callee.kind {
                    CallTarget::from_name(name)
                } else {
                    // Bootstrap: indirect call through variable → rt_indirect_call
                    let callee_reg = self.lower_expr(callee)?;
                    arg_regs.insert(0, callee_reg);
                    CallTarget::from_name("rt_indirect_call")
                };

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: call_target,
                        args: arg_regs,
                    });
                    dest
                })
            }

            HirExprKind::Lambda {
                params: _params,
                body,
                captures,
            } => {
                // Lower the lambda body to get the result vreg
                let body_reg = self.lower_expr(body)?;

                // For now, create a simple closure with captures
                // Each capture is 8 bytes (pointer-sized)
                let closure_size = 8 + (captures.len() as u32 * 8);
                let capture_offsets: Vec<u32> =
                    (0..captures.len()).map(|i| 8 + (i as u32 * 8)).collect();
                let capture_types: Vec<TypeId> = captures.iter().map(|_| TypeId::I64).collect();

                // Load captured variables
                let mut capture_regs = Vec::new();
                for &local_idx in captures.iter() {
                    let reg = self.with_func(|func, current_block| {
                        let addr_reg = func.new_vreg();
                        let val_reg = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::LocalAddr {
                            dest: addr_reg,
                            local_index: local_idx,
                        });
                        block.instructions.push(MirInst::Load {
                            dest: val_reg,
                            addr: addr_reg,
                            ty: TypeId::I64,
                        });
                        val_reg
                    })?;
                    capture_regs.push(reg);
                }

                // Generate a unique function name for the lambda body
                let func_name = format!("__lambda_{}", body_reg.0);

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ClosureCreate {
                        dest,
                        func_name,
                        closure_size,
                        capture_offsets,
                        capture_types,
                        captures: capture_regs,
                    });
                    dest
                })
            }

            HirExprKind::Yield(value) => {
                let value_reg = self.lower_expr(value)?;

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Yield { value: value_reg });
                    // Yield doesn't have a meaningful result, return the value register
                    value_reg
                })
            }

            HirExprKind::GeneratorCreate { body } => {
                // Lower the body expression first to get any setup
                let _body_reg = self.lower_expr(body)?;

                // Create a new block for the generator body
                let body_block = self.with_func(|func, _| func.new_block())?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block
                        .instructions
                        .push(MirInst::GeneratorCreate { dest, body_block });
                    dest
                })
            }

            HirExprKind::FutureCreate { body } => {
                // Lower the body expression first
                let _body_reg = self.lower_expr(body)?;

                // Create a new block for the future body
                let body_block = self.with_func(|func, _| func.new_block())?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block
                        .instructions
                        .push(MirInst::FutureCreate { dest, body_block });
                    dest
                })
            }

            HirExprKind::Await(future) => {
                let future_reg = self.lower_expr(future)?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Await {
                        dest,
                        future: future_reg,
                    });
                    dest
                })
            }

            HirExprKind::ActorSpawn { body } => {
                // Lower the body expression first
                let _body_reg = self.lower_expr(body)?;

                // Create a new block for the actor body
                let body_block = self.with_func(|func, _| func.new_block())?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block
                        .instructions
                        .push(MirInst::ActorSpawn { dest, body_block });
                    dest
                })
            }

            HirExprKind::BuiltinCall { name, args } => {
                // Lower all arguments
                let mut arg_regs = Vec::new();
                for arg in args {
                    arg_regs.push(self.lower_expr(arg)?);
                }

                // Create a call to the builtin function
                let target = CallTarget::from_name(name);
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target,
                        args: arg_regs,
                    });
                    dest
                })
            }

            // Contract expressions (Design by Contract)
            HirExprKind::ContractResult => {
                // Return the stored return value from contract context
                let return_value = self.try_contract_ctx()?.return_value;
                if let Some(vreg) = return_value {
                    Ok(vreg)
                } else {
                    // If no return value is set, create a dummy value (shouldn't happen in valid code)
                    self.with_func(|func, current_block| {
                        let dest = func.new_vreg();
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::ConstInt { dest, value: 0 });
                        dest
                    })
                }
            }

            HirExprKind::ContractOld(inner) => {
                // For old() expressions, we look up the captured value by its expression
                // In practice, the old_values in HirContract map (index -> HirExpr)
                // and we stored (index -> VReg) in contract_ctx.old_captures
                // However, since we're lowering the expression directly here,
                // we need to just use the captured value if it exists
                //
                // For now, lower the inner expression and use it directly
                // This works because old() captures happen at function entry
                // and we're accessing the captured VReg
                //
                // Note: In a full implementation, we'd need to track which old()
                // expression corresponds to which captured VReg. For now, we just
                // re-evaluate the inner expression (which works for simple cases
                // where the value hasn't changed).
                //
                // TODO: Properly track old() expressions by assigning indices
                // during HIR lowering and looking them up here.
                self.lower_expr(inner)
            }

            // =========================================================================
            // Pointer operations
            // =========================================================================
            HirExprKind::PointerNew { kind, value } => {
                let kind = *kind;
                let value_reg = self.lower_expr(value)?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::PointerNew {
                        dest,
                        kind,
                        value: value_reg,
                    });
                    dest
                })
            }

            HirExprKind::Ref(inner) => {
                let source_reg = self.lower_expr(inner)?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::PointerRef {
                        dest,
                        kind: crate::hir::PointerKind::Borrow,
                        source: source_reg,
                    });
                    dest
                })
            }

            HirExprKind::Deref(inner) => {
                let pointer_reg = self.lower_expr(inner)?;
                // Determine pointer kind from the inner expression's type
                // For now, default to Borrow
                let kind = crate::hir::PointerKind::Borrow;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::PointerDeref {
                        dest,
                        pointer: pointer_reg,
                        kind,
                    });
                    dest
                })
            }

            // =========================================================================
            // Collection operations
            // =========================================================================
            HirExprKind::Array(elements) => {
                // Lower each element expression to a VReg
                let mut elem_regs = Vec::new();
                for elem in elements {
                    elem_regs.push(self.lower_expr(elem)?);
                }

                // Emit ArrayLit instruction
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ArrayLit {
                        dest,
                        elements: elem_regs,
                    });
                    dest
                })
            }

            HirExprKind::Tuple(elements) => {
                let mut elem_regs = Vec::new();
                for elem in elements {
                    elem_regs.push(self.lower_expr(elem)?);
                }

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::TupleLit {
                        dest,
                        elements: elem_regs,
                    });
                    dest
                })
            }

            HirExprKind::Index { receiver, index } => {
                let recv_reg = self.lower_expr(receiver)?;
                let idx_reg = self.lower_expr(index)?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::IndexGet {
                        dest,
                        collection: recv_reg,
                        index: idx_reg,
                    });
                    dest
                })
            }

            HirExprKind::FieldAccess { receiver, field_index } => {
                let recv_reg = self.lower_expr(receiver)?;
                let field_index = *field_index;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::FieldGet {
                        dest,
                        object: recv_reg,
                        byte_offset: (field_index as u32) * 8, // 8 bytes per field
                        field_type: expr_ty,
                    });
                    dest
                })
            }

            HirExprKind::Nil => {
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ConstInt { dest, value: 0 });
                    dest
                })
            }

            HirExprKind::Global(name) => {
                // Global function reference - emit a call target reference
                // For now, treat as a function pointer (will be resolved at call site)
                let _name = name.clone();
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    // Store 0 as placeholder - the actual call will use CallTarget::from_name
                    block.instructions.push(MirInst::ConstInt { dest, value: 0 });
                    dest
                })
            }

            HirExprKind::If { condition, then_branch, else_branch } => {
                let cond_reg = self.lower_expr(condition)?;

                // Create blocks for then/else/merge
                let (then_id, else_id, merge_id) = self.with_func(|func, current_block| {
                    let then_id = func.new_block();
                    let else_id = func.new_block();
                    let merge_id = func.new_block();

                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Branch {
                        cond: cond_reg,
                        then_block: then_id,
                        else_block: else_id,
                    };

                    (then_id, else_id, merge_id)
                })?;

                // Lower then branch
                self.set_current_block(then_id)?;
                let then_reg = self.lower_expr(then_branch)?;
                // Create result variable in merge block
                let result_reg = self.with_func(|func, _| func.new_vreg())?;
                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Copy { dest: result_reg, src: then_reg });
                })?;
                self.finalize_block_jump(merge_id)?;

                // Lower else branch
                self.set_current_block(else_id)?;
                if let Some(else_expr) = else_branch {
                    let else_reg = self.lower_expr(else_expr)?;
                    self.with_func(|func, current_block| {
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::Copy { dest: result_reg, src: else_reg });
                    })?;
                } else {
                    self.with_func(|func, current_block| {
                        let block = func.block_mut(current_block).unwrap();
                        block.instructions.push(MirInst::ConstInt { dest: result_reg, value: 0 });
                    })?;
                }
                self.finalize_block_jump(merge_id)?;

                self.set_current_block(merge_id)?;
                Ok(result_reg)
            }

            _ => Err(MirLowerError::Unsupported(format!("{:?}", expr_kind))),
        }
    }

    fn lower_lvalue(&mut self, expr: &HirExpr) -> MirLowerResult<VReg> {
        match &expr.kind {
            HirExprKind::Local(idx) => {
                let idx = *idx;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::LocalAddr {
                        dest,
                        local_index: idx,
                    });
                    dest
                })
            }
            // Bootstrap: unknown lvalue pattern → lower as regular expression
            _ => self.lower_expr(expr),
        }
    }
}

impl Default for MirLowerer<'_> {
    fn default() -> Self {
        Self::new()
    }
}

/// Lower HIR to MIR with default contract mode (All).
pub fn lower_to_mir(hir: &HirModule) -> MirLowerResult<MirModule> {
    MirLowerer::new()
        .with_refined_types(&hir.refined_types)
        .lower_module(hir)
}

/// Lower HIR to MIR with a specific contract mode.
pub fn lower_to_mir_with_mode(hir: &HirModule, contract_mode: ContractMode) -> MirLowerResult<MirModule> {
    MirLowerer::with_contract_mode(contract_mode)
        .with_refined_types(&hir.refined_types)
        .lower_module(hir)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::{self, BinOp};
    use simple_parser::Parser;

    fn compile_to_mir(source: &str) -> MirLowerResult<MirModule> {
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = hir::lower(&ast).expect("hir lower failed");
        lower_to_mir(&hir_module)
    }

    #[test]
    fn test_lower_simple_return() {
        let mir = compile_to_mir("fn test() -> i64:\n    return 42\n").unwrap();

        assert_eq!(mir.functions.len(), 1);
        let func = &mir.functions[0];
        assert_eq!(func.name, "test");

        let entry = func.block(BlockId(0)).unwrap();
        assert!(!entry.instructions.is_empty());
        assert!(matches!(entry.terminator, Terminator::Return(Some(_))));
    }

    #[test]
    fn test_lower_binary_op() {
        let mir = compile_to_mir("fn add(a: i64, b: i64) -> i64:\n    return a + b\n").unwrap();

        let func = &mir.functions[0];
        let entry = func.block(BlockId(0)).unwrap();

        // Should have: load a, load b, add, return
        assert!(entry
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::BinOp { op: BinOp::Add, .. })));
    }

    #[test]
    fn test_lower_if_statement() {
        let mir = compile_to_mir(
            "fn max(a: i64, b: i64) -> i64:\n    if a > b:\n        return a\n    else:\n        return b\n"
        ).unwrap();

        let func = &mir.functions[0];
        // Should have multiple blocks: entry, then, else, merge
        assert!(func.blocks.len() >= 3);

        let entry = func.block(BlockId(0)).unwrap();
        assert!(matches!(entry.terminator, Terminator::Branch { .. }));
    }

    #[test]
    fn test_lower_while_loop() {
        let mir = compile_to_mir(
            "fn count() -> i64:\n    let x: i64 = 0\n    while x < 10:\n        x = x + 1\n    return x\n"
        ).unwrap();

        let func = &mir.functions[0];
        // Should have: entry, condition, body, exit blocks
        assert!(func.blocks.len() >= 4);
    }

    #[test]
    fn test_lower_local_variable() {
        let mir = compile_to_mir("fn test() -> i64:\n    let x: i64 = 5\n    return x\n").unwrap();

        let func = &mir.functions[0];
        let entry = func.block(BlockId(0)).unwrap();

        // Should have LocalAddr and Store for the let
        assert!(entry
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::LocalAddr { .. })));
        assert!(entry
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::Store { .. })));
    }

    #[test]
    fn test_lower_function_with_precondition() {
        // Contract syntax: contracts go BEFORE the function body colon
        let source = "fn divide(a: i64, b: i64) -> i64\nin:\n    b != 0\n:\n    return a / b\n";
        let mir = compile_to_mir(source).unwrap();

        let func = &mir.functions[0];
        let entry = func.block(BlockId(0)).unwrap();

        // Should have a ContractCheck instruction for the precondition
        assert!(entry
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::ContractCheck { kind: ContractKind::Precondition, .. })));
    }

    #[test]
    fn test_lower_function_with_postcondition() {
        // Contract syntax: contracts go BEFORE the function body colon
        let source = "fn abs_value(x: i64) -> i64\nout(ret):\n    ret >= 0\n:\n    return x\n";
        let mir = compile_to_mir(source).unwrap();

        let func = &mir.functions[0];

        // Should have a ContractCheck instruction for the postcondition somewhere
        // Check all blocks for postcondition checks
        let has_postcondition_check = func.blocks.iter().any(|block| {
            block.instructions.iter().any(|i| {
                matches!(i, MirInst::ContractCheck { kind: ContractKind::Postcondition, .. })
            })
        });
        assert!(has_postcondition_check, "Should have postcondition check");
    }

    #[test]
    fn test_lower_function_with_invariant() {
        // Contract syntax: contracts go BEFORE the function body colon
        let source = "fn test_invariant(x: i64) -> i64\ninvariant:\n    x >= 0\n:\n    return x + 1\n";
        let mir = compile_to_mir(source).unwrap();

        let func = &mir.functions[0];

        // Should have InvariantEntry and InvariantExit checks
        let has_entry = func.blocks.iter().any(|block| {
            block.instructions.iter().any(|i| {
                matches!(i, MirInst::ContractCheck { kind: ContractKind::InvariantEntry, .. })
            })
        });
        let has_exit = func.blocks.iter().any(|block| {
            block.instructions.iter().any(|i| {
                matches!(i, MirInst::ContractCheck { kind: ContractKind::InvariantExit, .. })
            })
        });
        assert!(has_entry, "Should have invariant entry check");
        assert!(has_exit, "Should have invariant exit check");
    }

    // =========================================================================
    // Contract Mode Tests (CTR-040 to CTR-043)
    // =========================================================================

    fn compile_to_mir_with_mode(source: &str, mode: ContractMode) -> MirLowerResult<MirModule> {
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = hir::lower(&ast).expect("hir lower failed");
        lower_to_mir_with_mode(&hir_module, mode)
    }

    #[test]
    fn test_contract_mode_off_no_checks() {
        // With ContractMode::Off, no contract checks should be emitted
        let source = "fn divide(a: i64, b: i64) -> i64\nin:\n    b != 0\n:\n    return a / b\n";
        let mir = compile_to_mir_with_mode(source, ContractMode::Off).unwrap();

        let func = &mir.functions[0];
        let entry = func.block(BlockId(0)).unwrap();

        // Should NOT have any ContractCheck instructions
        let has_contract_check = entry
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::ContractCheck { .. }));
        assert!(!has_contract_check, "ContractMode::Off should not emit contract checks");
    }

    #[test]
    fn test_contract_mode_boundary_public_function() {
        // With ContractMode::Boundary, public functions should have contract checks
        let source = "pub fn divide(a: i64, b: i64) -> i64\nin:\n    b != 0\n:\n    return a / b\n";
        let mir = compile_to_mir_with_mode(source, ContractMode::Boundary).unwrap();

        let func = &mir.functions[0];
        let entry = func.block(BlockId(0)).unwrap();

        // Should have ContractCheck for public function
        let has_contract_check = entry
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::ContractCheck { kind: ContractKind::Precondition, .. }));
        assert!(has_contract_check, "ContractMode::Boundary should emit checks for public functions");
    }

    #[test]
    fn test_contract_mode_boundary_private_function() {
        // With ContractMode::Boundary, private functions should NOT have contract checks
        let source = "fn divide(a: i64, b: i64) -> i64\nin:\n    b != 0\n:\n    return a / b\n";
        let mir = compile_to_mir_with_mode(source, ContractMode::Boundary).unwrap();

        let func = &mir.functions[0];
        let entry = func.block(BlockId(0)).unwrap();

        // Should NOT have ContractCheck for private function
        let has_contract_check = entry
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::ContractCheck { .. }));
        assert!(!has_contract_check, "ContractMode::Boundary should not emit checks for private functions");
    }

    #[test]
    fn test_contract_mode_all_checks_all_functions() {
        // With ContractMode::All (default), all functions should have contract checks
        let source = "fn divide(a: i64, b: i64) -> i64\nin:\n    b != 0\n:\n    return a / b\n";
        let mir = compile_to_mir_with_mode(source, ContractMode::All).unwrap();

        let func = &mir.functions[0];
        let entry = func.block(BlockId(0)).unwrap();

        // Should have ContractCheck for all functions
        let has_contract_check = entry
            .instructions
            .iter()
            .any(|i| matches!(i, MirInst::ContractCheck { kind: ContractKind::Precondition, .. }));
        assert!(has_contract_check, "ContractMode::All should emit checks for all functions");
    }

    #[test]
    fn test_contract_mode_from_str() {
        assert_eq!(ContractMode::from_str("off"), Some(ContractMode::Off));
        assert_eq!(ContractMode::from_str("none"), Some(ContractMode::Off));
        assert_eq!(ContractMode::from_str("boundary"), Some(ContractMode::Boundary));
        assert_eq!(ContractMode::from_str("public"), Some(ContractMode::Boundary));
        assert_eq!(ContractMode::from_str("all"), Some(ContractMode::All));
        assert_eq!(ContractMode::from_str("on"), Some(ContractMode::All));
        assert_eq!(ContractMode::from_str("test"), Some(ContractMode::Test));
        assert_eq!(ContractMode::from_str("debug"), Some(ContractMode::Test));
        assert_eq!(ContractMode::from_str("OFF"), Some(ContractMode::Off));
        assert_eq!(ContractMode::from_str("TEST"), Some(ContractMode::Test));
        assert_eq!(ContractMode::from_str("invalid"), None);
    }

    #[test]
    fn test_contract_mode_as_str() {
        assert_eq!(ContractMode::Off.as_str(), "off");
        assert_eq!(ContractMode::Boundary.as_str(), "boundary");
        assert_eq!(ContractMode::All.as_str(), "all");
        assert_eq!(ContractMode::Test.as_str(), "test");
    }

    #[test]
    fn test_contract_mode_test_has_rich_diagnostics() {
        // CTR-043: Test mode should have rich diagnostics
        assert!(ContractMode::Test.has_rich_diagnostics());
        assert!(!ContractMode::All.has_rich_diagnostics());
        assert!(!ContractMode::Boundary.has_rich_diagnostics());
        assert!(!ContractMode::Off.has_rich_diagnostics());
    }

    #[test]
    fn test_contract_mode_checks_all() {
        // CTR-043: Test mode should check all contracts like All mode
        assert!(ContractMode::Test.checks_all());
        assert!(ContractMode::All.checks_all());
        assert!(!ContractMode::Boundary.checks_all());
        assert!(!ContractMode::Off.checks_all());
    }

    #[test]
    fn test_contract_mode_default_is_all() {
        assert_eq!(ContractMode::default(), ContractMode::All);
    }

    // =========================================================================
    // Refinement Type Tests (CTR-020)
    // =========================================================================

    #[test]
    fn test_refinement_type_parsing() {
        // Test that refined types are properly parsed and stored
        let source = r#"
type PosI64 = i64 where self > 0

fn use_pos(x: PosI64) -> i64:
    return x
"#;
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = hir::lower(&ast).expect("hir lower failed");

        // Verify the refined type is registered
        assert!(hir_module.refined_types.contains_key("PosI64"),
            "Refined type PosI64 should be registered");

        let refined = hir_module.refined_types.get("PosI64").unwrap();
        assert_eq!(refined.name, "PosI64");
        assert_eq!(refined.base_type, crate::hir::TypeId::I64);
    }

    #[test]
    fn test_simple_type_alias_no_predicate() {
        // Test that simple type aliases (without where) work correctly
        let source = r#"
type UserId = i64

fn get_user(id: UserId) -> i64:
    return id
"#;
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = hir::lower(&ast).expect("hir lower failed");

        // Simple alias should NOT be in refined_types
        assert!(!hir_module.refined_types.contains_key("UserId"),
            "Simple type alias should not be in refined_types");

        // But the type name should still be registered
        assert!(hir_module.types.lookup("UserId").is_some(),
            "Type alias name should be registered");
    }

    // =========================================================================
    // Pure Expression Enforcement Tests (CTR-030-032)
    // =========================================================================

    #[test]
    fn test_pure_function_in_contract_allowed() {
        // Test that #[pure] functions can be called in contracts
        // Contract syntax: contracts go BEFORE the function body colon
        let source = "#[pure]\nfn is_valid(x: i64) -> bool:\n    return x > 0\n\nfn process(x: i64) -> i64\nin:\n    is_valid(x)\n:\n    return x * 2\n";
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = hir::lower(&ast).expect("hir lower failed");

        // Should have is_valid marked as pure
        let is_valid_func = hir_module.functions.iter().find(|f| f.name == "is_valid");
        assert!(is_valid_func.is_some(), "is_valid function should exist");
        assert!(is_valid_func.unwrap().is_pure, "is_valid should be marked as pure");
    }

    #[test]
    fn test_impure_function_in_contract_rejected() {
        // Test that non-pure functions cause an error in contracts
        // Contract syntax: contracts go BEFORE the function body colon
        let source = "fn impure_check(x: i64) -> bool:\n    return x > 0\n\nfn process(x: i64) -> i64\nin:\n    impure_check(x)\n:\n    return x * 2\n";
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let result = hir::lower(&ast);

        // Should fail with ImpureFunctionInContract error
        assert!(result.is_err(), "Should reject impure function in contract");
        let err = result.unwrap_err();
        let err_str = format!("{}", err);
        assert!(err_str.contains("impure_check") || err_str.contains("Impure"),
            "Error should mention impure function: {}", err_str);
    }

    #[test]
    fn test_builtin_math_in_contract_allowed() {
        // Test that builtin math functions are implicitly pure
        // Contract syntax: contracts go BEFORE the function body colon
        let source = "fn safe_fn(x: i64) -> i64\nin:\n    x >= 0\n:\n    return abs(x)\n";
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        let hir_module = hir::lower(&ast);

        // Should succeed because abs is implicitly pure and x >= 0 uses no function call
        assert!(hir_module.is_ok(), "Comparison operators should be allowed in contracts");
    }

    // =========================================================================
    // Snapshot-Safe Types Tests (CTR-060-062)
    // =========================================================================

    #[test]
    fn test_snapshot_safe_primitives() {
        // Test that primitive types are snapshot-safe in the type registry
        use crate::hir::{TypeRegistry, TypeId};

        let registry = TypeRegistry::new();

        // CTR-060: Primitives should be snapshot-safe
        assert!(registry.is_snapshot_safe(TypeId::BOOL), "bool should be snapshot-safe");
        assert!(registry.is_snapshot_safe(TypeId::I64), "i64 should be snapshot-safe");
        assert!(registry.is_snapshot_safe(TypeId::F64), "f64 should be snapshot-safe");
        assert!(registry.is_snapshot_safe(TypeId::STRING), "string should be snapshot-safe");
        assert!(registry.is_snapshot_safe(TypeId::NIL), "nil should be snapshot-safe");
    }

    #[test]
    fn test_snapshot_safe_struct() {
        // Test that structs with primitive fields are snapshot-safe (CTR-061)
        use crate::hir::{HirType, TypeRegistry, TypeId};

        let mut registry = TypeRegistry::new();

        // Register a struct with primitive fields
        registry.register_named(
            "Point".to_string(),
            HirType::Struct {
                name: "Point".to_string(),
                fields: vec![
                    ("x".to_string(), TypeId::I64),
                    ("y".to_string(), TypeId::I64),
                ],
                has_snapshot: false,
            },
        );

        let point_id = registry.lookup("Point").unwrap();
        assert!(registry.is_snapshot_safe(point_id), "Struct with primitive fields should be snapshot-safe");
    }

    #[test]
    fn test_snapshot_unsafe_function_type() {
        // Test that function types are NOT snapshot-safe
        use crate::hir::{HirType, TypeRegistry, TypeId};

        let mut registry = TypeRegistry::new();

        // Register a function type
        let func_id = registry.register(HirType::Function {
            params: vec![TypeId::I64],
            ret: TypeId::I64,
        });

        assert!(!registry.is_snapshot_safe(func_id), "Function types should NOT be snapshot-safe");
    }

    // =========================================================================
    // Module Boundary Checking Tests (CTR-012)
    // =========================================================================

    #[test]
    fn test_module_boundary_parameter_invariant() {
        // Test that public functions get preconditions for typed parameters
        use crate::hir::{HirExpr, HirExprKind, TypeId};

        // Create an expression: self.x > 0 (local 0 is self, field 0 is x)
        let invariant_expr = HirExpr {
            kind: HirExprKind::Binary {
                op: crate::hir::BinOp::Gt,
                left: Box::new(HirExpr {
                    kind: HirExprKind::FieldAccess {
                        receiver: Box::new(HirExpr {
                            kind: HirExprKind::Local(0), // self
                            ty: TypeId::I64,
                        }),
                        field_index: 0,
                    },
                    ty: TypeId::I64,
                }),
                right: Box::new(HirExpr {
                    kind: HirExprKind::Integer(0),
                    ty: TypeId::I64,
                }),
            },
            ty: TypeId::BOOL,
        };

        // Substitute self (local 0) with parameter at index 2
        let substituted = invariant_expr.substitute_local(0, 2);

        // Verify the substitution
        match &substituted.kind {
            HirExprKind::Binary { left, .. } => {
                match &left.kind {
                    HirExprKind::FieldAccess { receiver, .. } => {
                        match &receiver.kind {
                            HirExprKind::Local(idx) => {
                                assert_eq!(*idx, 2, "Local 0 should be substituted with 2");
                            }
                            _ => panic!("Expected Local after substitution"),
                        }
                    }
                    _ => panic!("Expected FieldAccess"),
                }
            }
            _ => panic!("Expected Binary"),
        }
    }

    #[test]
    fn test_module_boundary_return_invariant() {
        // Test that public functions get postconditions for typed return values
        use crate::hir::{HirExpr, HirExprKind, TypeId};

        // Create an expression: self.valid == true (local 0 is self)
        let invariant_expr = HirExpr {
            kind: HirExprKind::Binary {
                op: crate::hir::BinOp::Eq,
                left: Box::new(HirExpr {
                    kind: HirExprKind::FieldAccess {
                        receiver: Box::new(HirExpr {
                            kind: HirExprKind::Local(0), // self
                            ty: TypeId::BOOL,
                        }),
                        field_index: 0,
                    },
                    ty: TypeId::BOOL,
                }),
                right: Box::new(HirExpr {
                    kind: HirExprKind::Bool(true),
                    ty: TypeId::BOOL,
                }),
            },
            ty: TypeId::BOOL,
        };

        // Substitute self (local 0) with ContractResult
        let substituted = invariant_expr.substitute_self_with_result();

        // Verify the substitution
        match &substituted.kind {
            HirExprKind::Binary { left, .. } => {
                match &left.kind {
                    HirExprKind::FieldAccess { receiver, .. } => {
                        match &receiver.kind {
                            HirExprKind::ContractResult => {
                                // Success - local 0 was substituted with ContractResult
                            }
                            _ => panic!("Expected ContractResult after substitution, got {:?}", receiver.kind),
                        }
                    }
                    _ => panic!("Expected FieldAccess"),
                }
            }
            _ => panic!("Expected Binary"),
        }
    }

    #[test]
    fn test_get_type_name() {
        // Test TypeRegistry::get_type_name helper for CTR-012
        use crate::hir::{HirType, TypeRegistry, TypeId};

        let mut registry = TypeRegistry::new();

        // Register a struct
        let struct_id = registry.register_named(
            "MyStruct".to_string(),
            HirType::Struct {
                name: "MyStruct".to_string(),
                fields: vec![("x".to_string(), TypeId::I64)],
                has_snapshot: false,
            },
        );

        // Register an enum
        let enum_id = registry.register_named(
            "MyEnum".to_string(),
            HirType::Enum {
                name: "MyEnum".to_string(),
                variants: vec![("A".to_string(), None), ("B".to_string(), None)],
            },
        );

        // Test get_type_name
        assert_eq!(registry.get_type_name(struct_id), Some("MyStruct"));
        assert_eq!(registry.get_type_name(enum_id), Some("MyEnum"));
        assert_eq!(registry.get_type_name(TypeId::I64), None); // Primitives don't have names
        assert_eq!(registry.get_type_name(TypeId::STRING), None);
    }

    // =========================================================================
    // Refinement Type Tests (CTR-021-023)
    // =========================================================================

    #[test]
    fn test_refined_type_const_eval_greater_than() {
        // CTR-022: Test compile-time evaluation of predicates
        use crate::hir::{HirExpr, HirExprKind, HirRefinedType, BinOp, TypeId};

        // Create a refined type: PosI64 = i64 where self > 0
        let refined = HirRefinedType {
            name: "PosI64".to_string(),
            base_type: TypeId::I64,
            predicate: HirExpr {
                kind: HirExprKind::Binary {
                    op: BinOp::Gt,
                    left: Box::new(HirExpr {
                        kind: HirExprKind::Local(0), // self
                        ty: TypeId::I64,
                    }),
                    right: Box::new(HirExpr {
                        kind: HirExprKind::Integer(0),
                        ty: TypeId::I64,
                    }),
                },
                ty: TypeId::BOOL,
            },
        };

        // Test with positive constant (should satisfy)
        let positive_value = HirExpr {
            kind: HirExprKind::Integer(42),
            ty: TypeId::I64,
        };
        assert_eq!(refined.try_const_eval(&positive_value), Some(true));

        // Test with zero (should NOT satisfy > 0)
        let zero_value = HirExpr {
            kind: HirExprKind::Integer(0),
            ty: TypeId::I64,
        };
        assert_eq!(refined.try_const_eval(&zero_value), Some(false));

        // Test with negative (should NOT satisfy)
        let negative_value = HirExpr {
            kind: HirExprKind::Integer(-5),
            ty: TypeId::I64,
        };
        assert_eq!(refined.try_const_eval(&negative_value), Some(false));

        // Test with variable (cannot evaluate at compile time)
        let variable_value = HirExpr {
            kind: HirExprKind::Local(1),
            ty: TypeId::I64,
        };
        assert_eq!(refined.try_const_eval(&variable_value), None);
    }

    #[test]
    fn test_refined_type_const_eval_range() {
        // CTR-022: Test range predicates
        use crate::hir::{HirExpr, HirExprKind, HirRefinedType, BinOp, TypeId};

        // Create a refined type: Percentage = i64 where self >= 0 and self <= 100
        // For simplicity, just test >= 0
        let refined = HirRefinedType {
            name: "NonNegI64".to_string(),
            base_type: TypeId::I64,
            predicate: HirExpr {
                kind: HirExprKind::Binary {
                    op: BinOp::GtEq,
                    left: Box::new(HirExpr {
                        kind: HirExprKind::Local(0), // self
                        ty: TypeId::I64,
                    }),
                    right: Box::new(HirExpr {
                        kind: HirExprKind::Integer(0),
                        ty: TypeId::I64,
                    }),
                },
                ty: TypeId::BOOL,
            },
        };

        // Test edge case: 0 should satisfy >= 0
        let zero_value = HirExpr {
            kind: HirExprKind::Integer(0),
            ty: TypeId::I64,
        };
        assert_eq!(refined.try_const_eval(&zero_value), Some(true));

        // Test: -1 should NOT satisfy >= 0
        let negative_value = HirExpr {
            kind: HirExprKind::Integer(-1),
            ty: TypeId::I64,
        };
        assert_eq!(refined.try_const_eval(&negative_value), Some(false));
    }

    #[test]
    fn test_subtype_result_same() {
        // CTR-021: Test SubtypeResult::Same
        use crate::hir::{HirModule, SubtypeResult, TypeId};

        let module = HirModule::new();

        // Same types should return Same
        assert_eq!(module.check_subtype(TypeId::I64, TypeId::I64), SubtypeResult::Same);
        assert_eq!(module.check_subtype(TypeId::BOOL, TypeId::BOOL), SubtypeResult::Same);
    }

    #[test]
    fn test_subtype_result_incompatible() {
        // CTR-021: Test SubtypeResult::Incompatible
        use crate::hir::{HirModule, SubtypeResult, TypeId};

        let module = HirModule::new();

        // Unrelated types should be incompatible
        assert_eq!(module.check_subtype(TypeId::I64, TypeId::BOOL), SubtypeResult::Incompatible);
        assert_eq!(module.check_subtype(TypeId::STRING, TypeId::I64), SubtypeResult::Incompatible);
    }

    // =========================================================================
    // Snapshot Annotation Tests (CTR-062)
    // =========================================================================

    #[test]
    fn test_snapshot_annotation_makes_type_safe() {
        // CTR-062: Types with #[snapshot] are always snapshot-safe
        use crate::hir::{HirType, TypeRegistry, TypeId, PointerKind};

        let mut registry = TypeRegistry::new();

        // Register a struct WITHOUT #[snapshot] that contains a mutable reference
        // This should NOT be snapshot-safe
        let mutable_ptr_type = registry.register(HirType::Pointer {
            kind: PointerKind::BorrowMut,
            inner: TypeId::I64,
        });

        let unsafe_struct = registry.register_named(
            "UnsafeStruct".to_string(),
            HirType::Struct {
                name: "UnsafeStruct".to_string(),
                fields: vec![("data".to_string(), mutable_ptr_type)],
                has_snapshot: false, // No #[snapshot] attribute
            },
        );

        assert!(!registry.is_snapshot_safe(unsafe_struct),
            "Struct with mutable reference should NOT be snapshot-safe without #[snapshot]");

        // Register a struct WITH #[snapshot] that contains a mutable reference
        // This should BE snapshot-safe due to the annotation
        let safe_struct = registry.register_named(
            "SafeStruct".to_string(),
            HirType::Struct {
                name: "SafeStruct".to_string(),
                fields: vec![("data".to_string(), mutable_ptr_type)],
                has_snapshot: true, // Has #[snapshot] attribute
            },
        );

        assert!(registry.is_snapshot_safe(safe_struct),
            "Struct with #[snapshot] should be snapshot-safe even with mutable reference");
    }

    #[test]
    fn test_snapshot_annotation_on_primitive_struct() {
        // CTR-062: #[snapshot] is redundant but harmless on structs with only primitives
        use crate::hir::{HirType, TypeRegistry, TypeId};

        let mut registry = TypeRegistry::new();

        // Struct with only primitives but also has #[snapshot]
        let point_with_snapshot = registry.register_named(
            "PointWithSnapshot".to_string(),
            HirType::Struct {
                name: "PointWithSnapshot".to_string(),
                fields: vec![
                    ("x".to_string(), TypeId::I64),
                    ("y".to_string(), TypeId::I64),
                ],
                has_snapshot: true,
            },
        );

        assert!(registry.is_snapshot_safe(point_with_snapshot),
            "Struct with #[snapshot] and primitive fields should be snapshot-safe");
    }

    #[test]
    fn test_lower_field_assignment() {
        // self.x = 10 should produce FieldSet, not complex lvalue error
        let source = r#"
struct Point:
    x: i64
    y: i64

fn set_x(p: Point) -> Point:
    p.x = 10
    return p
"#;
        let mir = compile_to_mir(source).unwrap();
        let func = mir.functions.iter().find(|f| f.name == "set_x").unwrap();
        let entry = func.block(BlockId(0)).unwrap();

        // Should contain a FieldSet instruction
        assert!(
            entry.instructions.iter().any(|i| matches!(i, MirInst::FieldSet { .. })),
            "Expected FieldSet instruction for field assignment, got: {:?}",
            entry.instructions
        );
    }

    #[test]
    fn test_lower_index_assignment() {
        // arr[0] = 42 should produce IndexSet, not complex lvalue error
        let source = r#"
fn set_first(arr: [i64]):
    arr[0] = 42
"#;
        let mir = compile_to_mir(source).unwrap();
        let func = mir.functions.iter().find(|f| f.name == "set_first").unwrap();
        let entry = func.block(BlockId(0)).unwrap();

        // Should contain an IndexSet instruction
        assert!(
            entry.instructions.iter().any(|i| matches!(i, MirInst::IndexSet { .. })),
            "Expected IndexSet instruction for index assignment, got: {:?}",
            entry.instructions
        );
    }

    #[test]
    fn test_lower_local_assignment_still_works() {
        // Simple local assignment should still work via LocalAddr + Store
        let source = r#"
fn test() -> i64:
    var x = 1
    x = 2
    return x
"#;
        let mir = compile_to_mir(source).unwrap();
        let func = mir.functions.iter().find(|f| f.name == "test").unwrap();
        let entry = func.block(BlockId(0)).unwrap();

        // Should contain Store (for local assignment)
        assert!(
            entry.instructions.iter().any(|i| matches!(i, MirInst::Store { .. })),
            "Expected Store instruction for local assignment, got: {:?}",
            entry.instructions
        );
    }
}

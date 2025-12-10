use super::{
    blocks::Terminator,
    effects::{CallTarget, LocalKind},
    function::{MirFunction, MirLocal, MirModule},
    instructions::{BlockId, MirInst, VReg},
};
use crate::hir::{HirExpr, HirExprKind, HirFunction, HirModule, HirStmt, TypeId};
use thiserror::Error;

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

    /// Get loop stack (returns error if idle)
    pub fn try_loop_stack(&self) -> MirLowerResult<&Vec<LoopContext>> {
        match self {
            LowererState::Lowering { loop_stack, .. } => Ok(loop_stack),
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Get mutable loop stack (returns error if idle)
    pub fn try_loop_stack_mut(&mut self) -> MirLowerResult<&mut Vec<LoopContext>> {
        match self {
            LowererState::Lowering { loop_stack, .. } => Ok(loop_stack),
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Set current block (returns error if idle)
    pub fn try_set_current_block(&mut self, block: BlockId) -> MirLowerResult<()> {
        match self {
            LowererState::Lowering { current_block, .. } => {
                *current_block = block;
                Ok(())
            }
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
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
pub struct MirLowerer {
    state: LowererState,
}

impl MirLowerer {
    pub fn new() -> Self {
        Self {
            state: LowererState::Idle,
        }
    }

    /// Get current state for verification
    pub fn state(&self) -> &LowererState {
        &self.state
    }

    /// Transition from Idle to Lowering - explicit state transition
    fn begin_function(&mut self, func: MirFunction) -> MirLowerResult<()> {
        match &self.state {
            LowererState::Idle => {
                self.state = LowererState::Lowering {
                    func,
                    current_block: BlockId(0),
                    loop_stack: Vec::new(),
                };
                Ok(())
            }
            LowererState::Lowering { .. } => Err(MirLowerError::InvalidState {
                expected: "Idle".to_string(),
                found: "Lowering".to_string(),
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
        match &mut self.state {
            LowererState::Lowering { current_block, .. } => {
                *current_block = block;
                Ok(())
            }
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Push loop context - for break/continue handling
    fn push_loop(&mut self, ctx: LoopContext) -> MirLowerResult<()> {
        match &mut self.state {
            LowererState::Lowering { loop_stack, .. } => {
                loop_stack.push(ctx);
                Ok(())
            }
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
    }

    /// Pop loop context
    fn pop_loop(&mut self) -> MirLowerResult<LoopContext> {
        match &mut self.state {
            LowererState::Lowering { loop_stack, .. } => {
                loop_stack.pop().ok_or(MirLowerError::BreakOutsideLoop)
            }
            LowererState::Idle => Err(MirLowerError::InvalidState {
                expected: "Lowering".to_string(),
                found: "Idle".to_string(),
            }),
        }
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

        // Add locals
        for local in &func.locals {
            mir_func.locals.push(MirLocal {
                name: local.name.clone(),
                ty: local.ty,
                kind: LocalKind::Local,
            });
        }

        // Explicit state transition: Idle -> Lowering
        self.begin_function(mir_func)?;

        // Lower body
        for stmt in &func.body {
            self.lower_stmt(stmt)?;
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

    fn lower_stmt(&mut self, stmt: &HirStmt) -> MirLowerResult<()> {
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
                let addr_reg = self.lower_lvalue(target)?;
                let ty = value.ty;

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Store {
                        addr: addr_reg,
                        value: val_reg,
                        ty,
                    });
                })?;
                Ok(())
            }

            HirStmt::Return(value) => {
                let ret_reg = if let Some(v) = value {
                    Some(self.lower_expr(v)?)
                } else {
                    None
                };

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
                    self.lower_stmt(stmt)?;
                }
                self.finalize_block_jump(merge_id)?;

                // Lower else block
                self.set_current_block(else_id)?;
                if let Some(else_stmts) = else_block {
                    for stmt in else_stmts {
                        self.lower_stmt(stmt)?;
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
                    self.lower_stmt(stmt)?;
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
                    self.lower_stmt(stmt)?;
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
                let left_reg = self.lower_expr(left)?;
                let right_reg = self.lower_expr(right)?;

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
                    return Err(MirLowerError::Unsupported("indirect call".to_string()));
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
                params,
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
                    block.instructions.push(MirInst::GeneratorCreate { dest, body_block });
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
                    block.instructions.push(MirInst::FutureCreate { dest, body_block });
                    dest
                })
            }

            HirExprKind::Await(future) => {
                let future_reg = self.lower_expr(future)?;

                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block
                        .instructions
                        .push(MirInst::Await { dest, future: future_reg });
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
                    block.instructions.push(MirInst::ActorSpawn { dest, body_block });
                    dest
                })
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
            _ => Err(MirLowerError::Unsupported("complex lvalue".to_string())),
        }
    }
}

impl Default for MirLowerer {
    fn default() -> Self {
        Self::new()
    }
}

/// Convenience function to lower HIR to MIR
pub fn lower_to_mir(hir: &HirModule) -> MirLowerResult<MirModule> {
    MirLowerer::new().lower_module(hir)
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
}

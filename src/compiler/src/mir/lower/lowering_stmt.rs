//! Statement lowering for MIR
//!
//! This module contains methods for lowering HIR statements to MIR instructions,
//! including control flow (if, while, loop, break, continue) and assignments.

use super::lowering_core::{LoopContext, MirLowerResult, MirLowerer};
use crate::hir::{HirContract, HirExpr, HirExprKind, HirStmt, HirType};
use crate::mir::blocks::Terminator;
use crate::mir::instructions::MirInst;

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_stmt(&mut self, stmt: &HirStmt, contract: Option<&HirContract>) -> MirLowerResult<()> {
        match stmt {
            HirStmt::Let {
                local_index,
                ty: declared_ty,
                value,
            } => {
                if let Some(val) = value {
                    let vreg = self.lower_expr(val)?;
                    let local_idx = *local_index;
                    let value_ty = val.ty;

                    // Wrap value in union if assigning to a union type
                    let vreg = self.emit_union_wrap_if_needed(*declared_ty, value_ty, vreg)?;

                    // Emit unit bound check if assigning to a unit type with constraints
                    self.emit_unit_bound_check(*declared_ty, vreg)?;

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
                            ty: *declared_ty,
                        });
                    })?;
                }
                Ok(())
            }

            HirStmt::Assign { target, value } => {
                let val_reg = self.lower_expr(value)?;
                let addr_reg = self.lower_lvalue(target)?;
                let ty = value.ty;

                // Emit unit bound check if assigning to a unit type with constraints
                self.emit_unit_bound_check(ty, val_reg)?;

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

                // Emit contract checks before the actual return based on contract mode
                if let Some(contract) = contract {
                    if self.should_emit_contracts() {
                        // Detect if this is a Result::Err return to call the appropriate contract handler
                        let is_error_return = value
                            .as_ref()
                            .map(|v| self.is_result_err_construction(v))
                            .unwrap_or(false);

                        if is_error_return && !contract.error_postconditions.is_empty() {
                            // This is an error return - emit error postconditions
                            if let Some(ret) = ret_reg {
                                self.emit_error_contracts(contract, ret)?;
                            }
                        } else {
                            // This is a success return - emit normal postconditions
                            self.emit_exit_contracts(contract, ret_reg)?;
                        }
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

                // Emit decision probe for coverage (before branch)
                // Line/column require span tracking in HIR expressions
                // Currently using placeholder values (0, 0) for decision probes
                self.emit_decision_probe(cond_reg, 0, 0)?;

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

                // Emit decision probe for while condition coverage
                // Line/column require span tracking in HIR expressions
                self.emit_decision_probe(cond_reg, 0, 0)?;

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
                    .ok_or(super::lowering_core::MirLowerError::BreakOutsideLoop)?
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
                    .ok_or(super::lowering_core::MirLowerError::ContinueOutsideLoop)?
                    .clone();

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Jump(loop_ctx.continue_target);
                })?;
                Ok(())
            }
        }
    }

    /// Check if an expression constructs a Result::Err variant
    ///
    /// This is used to determine whether to emit error postconditions or
    /// normal postconditions when processing a return statement.
    ///
    /// Detection strategies:
    /// 1. Check if it's a Call to a Global("Err") function
    /// 2. Check if the type is a Result enum and look at the construction pattern
    fn is_result_err_construction(&self, expr: &HirExpr) -> bool {
        // Strategy 1: Check if it's a direct call to Err()
        if let HirExprKind::Call { func, args: _ } = &expr.kind {
            if let HirExprKind::Global(name) = &func.kind {
                if name == "Err" {
                    return true;
                }
            }
        }

        // Strategy 2: Check if the type is Result and look up variant info
        if let Some(registry) = self.type_registry {
            if let Some(hir_type) = registry.get(expr.ty) {
                if let HirType::Enum { name, variants: _ } = hir_type {
                    // If the type is named "Result", check the expression pattern
                    if name == "Result" {
                        // For StructInit, check if the type name contains "Err"
                        if let HirExprKind::StructInit { ty, fields: _ } = &expr.kind {
                            if let Some(struct_type) = registry.get(*ty) {
                                if let HirType::Struct { name: struct_name, .. } = struct_type {
                                    return struct_name.contains("Err");
                                }
                            }
                        }
                    }
                }
            }
        }

        false
    }
}

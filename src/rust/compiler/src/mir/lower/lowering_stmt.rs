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
                let ty = value.ty;

                // Emit unit bound check if assigning to a unit type with constraints
                self.emit_unit_bound_check(ty, val_reg)?;

                // Handle different assignment targets
                match &target.kind {
                    // Field assignment: obj.field = value -> FieldSet
                    HirExprKind::FieldAccess { receiver, field_index } => {
                        let receiver_reg = self.lower_expr(receiver)?;
                        let field_index = *field_index;
                        let byte_offset = (field_index as u32) * 8;

                        self.with_func(|func, current_block| {
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::FieldSet {
                                object: receiver_reg,
                                byte_offset,
                                field_type: ty,
                                value: val_reg,
                            });
                        })?;
                    }

                    // Index assignment: arr[i] = value -> rt_array_set call
                    HirExprKind::Index { receiver, index } => {
                        let receiver_reg = self.lower_expr(receiver)?;
                        let index_reg = self.lower_expr(index)?;

                        // Use rt_array_set for array/dict index assignment
                        let target = crate::mir::CallTarget::from_name("rt_array_set");
                        self.with_func(|func, current_block| {
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::Call {
                                dest: None,
                                target,
                                args: vec![receiver_reg, index_reg, val_reg],
                            });
                        })?;
                    }

                    // Property setter: obj.field = value (when field access became MethodCall)
                    // This happens when type information is lost or for dynamic property access
                    HirExprKind::MethodCall { receiver, method, args, .. } if args.is_empty() => {
                        let receiver_reg = self.lower_expr(receiver)?;

                        // Create a string constant for the field name
                        let field_name_reg = self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::ConstString {
                                dest,
                                value: method.clone(),
                            });
                            dest
                        })?;

                        // Use rt_field_set for dynamic field assignment
                        let target = crate::mir::CallTarget::from_name("rt_field_set");
                        self.with_func(|func, current_block| {
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::Call {
                                dest: None,
                                target,
                                args: vec![receiver_reg, field_name_reg, val_reg],
                            });
                        })?;
                    }

                    // Local variable assignment: use address + store pattern
                    _ => {
                        let addr_reg = self.lower_lvalue(target)?;
                        self.with_func(|func, current_block| {
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::Store {
                                addr: addr_reg,
                                value: val_reg,
                                ty,
                            });
                        })?;
                    }
                }

                Ok(())
            }

            HirStmt::Return(value) => {
                let ret_reg = if let Some(v) = value {
                    let reg = self.lower_expr(v)?;
                    Some(reg)
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

                // Emit drop instructions for all locals before returning
                // This ensures proper cleanup in LIFO order (Rust-level memory safety)
                self.emit_function_drops()?;

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Return(ret_reg);
                })?;
                Ok(())
            }

            HirStmt::Expr(expr) => {
                let vreg = self.lower_expr(expr)?;
                // Track the last expression value for implicit returns
                self.last_expr_value = Some(vreg);
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

                // Save last_expr_value before branches (for proper value merging)
                let saved_last_expr = self.last_expr_value;

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
                self.last_expr_value = saved_last_expr;
                for stmt in then_block {
                    self.lower_stmt(stmt, contract)?;
                }
                let then_value = self.last_expr_value;
                self.finalize_block_jump(merge_id)?;

                // Lower else block
                self.set_current_block(else_id)?;
                self.last_expr_value = saved_last_expr;
                if let Some(else_stmts) = else_block {
                    for stmt in else_stmts {
                        self.lower_stmt(stmt, contract)?;
                    }
                }
                let else_value = self.last_expr_value;
                self.finalize_block_jump(merge_id)?;

                // Handle value merging for if/else as expression
                // If both branches produce different values, we need to merge them
                // using a temporary local to ensure proper SSA domination
                self.set_current_block(merge_id)?;

                match (then_value, else_value) {
                    (Some(tv), Some(ev)) if tv != ev => {
                        // Both branches produced different values - need to merge
                        // Add a temporary local to hold the merged value
                        use crate::hir::TypeId;
                        use crate::mir::effects::LocalKind;
                        use crate::mir::function::MirLocal;

                        let temp_local_index = self.with_func(|func, _| {
                            let index = func.params.len() + func.locals.len();
                            func.locals.push(MirLocal {
                                name: format!("__if_merge_{}", index),
                                ty: TypeId::I64, // Use i64 as generic merge type
                                kind: LocalKind::Local,
                                is_ghost: false,
                            });
                            index
                        })?;

                        // Go back to then block and add store before jump
                        self.set_current_block(then_id)?;
                        self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            // Insert store before the terminator
                            block.instructions.push(MirInst::LocalAddr {
                                dest,
                                local_index: temp_local_index,
                            });
                            block.instructions.push(MirInst::Store {
                                addr: dest,
                                value: tv,
                                ty: TypeId::I64,
                            });
                        })?;

                        // Go back to else block and add store before jump
                        self.set_current_block(else_id)?;
                        self.with_func(|func, current_block| {
                            let dest = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            // Insert store before the terminator
                            block.instructions.push(MirInst::LocalAddr {
                                dest,
                                local_index: temp_local_index,
                            });
                            block.instructions.push(MirInst::Store {
                                addr: dest,
                                value: ev,
                                ty: TypeId::I64,
                            });
                        })?;

                        // Back to merge block - load the merged value
                        self.set_current_block(merge_id)?;
                        let merged_value = self.with_func(|func, current_block| {
                            let addr = func.new_vreg();
                            let value = func.new_vreg();
                            let block = func.block_mut(current_block).unwrap();
                            block.instructions.push(MirInst::LocalAddr {
                                dest: addr,
                                local_index: temp_local_index,
                            });
                            block.instructions.push(MirInst::Load {
                                dest: value,
                                addr,
                                ty: TypeId::I64,
                            });
                            value
                        })?;
                        self.last_expr_value = Some(merged_value);
                    }
                    (Some(v), _) | (_, Some(v)) => {
                        // Only one branch produced a value (or same value)
                        // This case is rare but handle it gracefully
                        self.last_expr_value = Some(v);
                    }
                    (None, None) => {
                        // Neither branch produced a value - restore saved
                        self.last_expr_value = saved_last_expr;
                    }
                }

                Ok(())
            }

            HirStmt::While { condition, body, .. } => {
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

            HirStmt::Assert { condition, message } => {
                // Lower the assertion condition
                let cond_reg = self.lower_expr(condition)?;

                // Emit decision probe for assert condition coverage (#674)
                self.emit_decision_probe(cond_reg, 0, 0)?;

                // Get function name for error message (best effort)
                let func_name = self
                    .try_contract_ctx()
                    .map(|ctx| ctx.func_name.clone())
                    .unwrap_or_else(|_| "<unknown>".to_string());

                // Emit contract check instruction with Assertion kind
                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ContractCheck {
                        condition: cond_reg,
                        kind: crate::mir::instructions::ContractKind::Assertion,
                        func_name,
                        message: message.clone(),
                    });
                })?;
                Ok(())
            }

            HirStmt::For {
                pattern,
                iterable,
                body,
                ..
            } => {
                // For loops use index-based iteration over collections
                // 1. Evaluate iterable once
                // 2. Get length
                // 3. Loop: check index < len, get element, execute body, increment index

                // Lower the iterable expression
                let collection_reg = self.lower_expr(iterable)?;

                // Create a local for the loop variable if it doesn't exist
                let pattern_local_index = self.with_func(|func, _| {
                    let num_params = func.params.len();
                    // First check params
                    for (i, param) in func.params.iter().enumerate() {
                        if param.name == *pattern {
                            return i;
                        }
                    }
                    // Then check locals
                    for (i, local) in func.locals.iter().enumerate() {
                        if local.name == *pattern {
                            return num_params + i;
                        }
                    }
                    // Not found - create a new local for the loop variable
                    let index = num_params + func.locals.len();
                    func.locals.push(crate::mir::function::MirLocal {
                        name: pattern.clone(),
                        ty: crate::hir::TypeId::ANY, // Type will be inferred from collection element type
                        kind: crate::mir::effects::LocalKind::Local,
                        is_ghost: false,
                    });
                    index
                })?;

                // Get collection length via rt_array_len call
                let len_reg = self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: crate::mir::CallTarget::from_name("rt_array_len"),
                        args: vec![collection_reg],
                    });
                    dest
                })?;

                // Create index register, initialize to 0
                let index_reg = self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ConstInt { dest, value: 0 });
                    dest
                })?;

                // We need a mutable index, so use a local slot for it
                // Allocate a stack slot for the index
                let index_addr_reg = self.with_func(|func, current_block| {
                    // Add a synthetic local for the index counter
                    let index_local_idx = func.params.len() + func.locals.len();
                    func.locals.push(crate::mir::function::MirLocal {
                        name: format!("__for_index_{}", pattern),
                        ty: crate::hir::TypeId::I64,
                        kind: crate::mir::effects::LocalKind::Local,
                        is_ghost: false,
                    });

                    let addr = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::LocalAddr {
                        dest: addr,
                        local_index: index_local_idx,
                    });
                    block.instructions.push(MirInst::Store {
                        addr,
                        value: index_reg,
                        ty: crate::hir::TypeId::I64,
                    });
                    (addr, index_local_idx)
                })?;
                let (index_addr, index_local_idx) = index_addr_reg;

                // Create blocks
                let (header_id, body_id, exit_id) = self.with_func(|func, current_block| {
                    let header_id = func.new_block();
                    let body_id = func.new_block();
                    let exit_id = func.new_block();

                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Jump(header_id);
                    (header_id, body_id, exit_id)
                })?;

                self.push_loop(LoopContext {
                    continue_target: header_id,
                    break_target: exit_id,
                })?;

                // Header: load index, compare with len, branch
                self.set_current_block(header_id)?;
                let cond_reg = self.with_func(|func, current_block| {
                    // Allocate all vregs first
                    let addr = func.new_vreg();
                    let current_idx = func.new_vreg();
                    let cond = func.new_vreg();

                    // Now get the block and emit instructions
                    let block = func.block_mut(current_block).unwrap();

                    // Load current index
                    block.instructions.push(MirInst::LocalAddr {
                        dest: addr,
                        local_index: index_local_idx,
                    });
                    block.instructions.push(MirInst::Load {
                        dest: current_idx,
                        addr,
                        ty: crate::hir::TypeId::I64,
                    });

                    // Compare index < len
                    block.instructions.push(MirInst::BinOp {
                        dest: cond,
                        op: crate::hir::BinOp::Lt,
                        left: current_idx,
                        right: len_reg,
                    });
                    cond
                })?;

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.terminator = Terminator::Branch {
                        cond: cond_reg,
                        then_block: body_id,
                        else_block: exit_id,
                    };
                })?;

                // Body: get element, store to loop var, execute body, increment index
                self.set_current_block(body_id)?;

                // Load current index and get element
                self.with_func(|func, current_block| {
                    // Allocate all vregs first
                    let addr = func.new_vreg();
                    let current_idx = func.new_vreg();
                    let element = func.new_vreg();
                    let var_addr = func.new_vreg();

                    // Now get the block and emit instructions
                    let block = func.block_mut(current_block).unwrap();

                    // Load current index
                    block.instructions.push(MirInst::LocalAddr {
                        dest: addr,
                        local_index: index_local_idx,
                    });
                    block.instructions.push(MirInst::Load {
                        dest: current_idx,
                        addr,
                        ty: crate::hir::TypeId::I64,
                    });

                    // Get element via IndexGet (which calls rt_index_get internally)
                    block.instructions.push(MirInst::IndexGet {
                        dest: element,
                        collection: collection_reg,
                        index: current_idx,
                    });

                    // Store element to loop variable's local
                    block.instructions.push(MirInst::LocalAddr {
                        dest: var_addr,
                        local_index: pattern_local_index,
                    });
                    block.instructions.push(MirInst::Store {
                        addr: var_addr,
                        value: element,
                        ty: iterable.ty, // Use element type
                    });
                })?;

                // Execute body statements
                for stmt in body {
                    self.lower_stmt(stmt, contract)?;
                }

                // Increment index
                self.with_func(|func, current_block| {
                    // Allocate all vregs first
                    let addr = func.new_vreg();
                    let current_idx = func.new_vreg();
                    let one = func.new_vreg();
                    let new_idx = func.new_vreg();

                    // Now get the block and emit instructions
                    let block = func.block_mut(current_block).unwrap();

                    // Load current index
                    block.instructions.push(MirInst::LocalAddr {
                        dest: addr,
                        local_index: index_local_idx,
                    });
                    block.instructions.push(MirInst::Load {
                        dest: current_idx,
                        addr,
                        ty: crate::hir::TypeId::I64,
                    });

                    // Increment
                    block.instructions.push(MirInst::ConstInt { dest: one, value: 1 });
                    block.instructions.push(MirInst::BinOp {
                        dest: new_idx,
                        op: crate::hir::BinOp::Add,
                        left: current_idx,
                        right: one,
                    });

                    // Store back
                    block.instructions.push(MirInst::Store {
                        addr,
                        value: new_idx,
                        ty: crate::hir::TypeId::I64,
                    });
                })?;

                self.finalize_block_jump(header_id)?;

                self.pop_loop()?;
                self.set_current_block(exit_id)?;
                Ok(())
            }

            HirStmt::Assume { condition, message } => {
                // Assume is a verification statement similar to assert
                // At runtime, we treat it as an assertion
                let cond_reg = self.lower_expr(condition)?;

                // Emit decision probe for assume condition coverage (#674)
                self.emit_decision_probe(cond_reg, 0, 0)?;

                let func_name = self
                    .try_contract_ctx()
                    .map(|ctx| ctx.func_name.clone())
                    .unwrap_or_else(|_| "<unknown>".to_string());

                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ContractCheck {
                        condition: cond_reg,
                        kind: crate::mir::instructions::ContractKind::Assertion,
                        func_name,
                        message: message.clone(),
                    });
                })?;
                Ok(())
            }

            HirStmt::Admit { condition, message } => {
                // Admit is a verification-only statement that admits a fact without proof
                // At runtime, this is a no-op (we trust the admitted fact)
                let _ = condition;
                let _ = message;
                Ok(())
            }

            HirStmt::ProofHint { hint: _ } => {
                // Proof hints are verification-only statements that provide tactic hints to Lean
                // At runtime, this is a no-op
                Ok(())
            }

            HirStmt::Calc { steps: _ } => {
                // Calculational proofs are verification-only statements for Lean calc blocks
                // At runtime, this is a no-op
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
                if let HirType::Enum { name, variants: _, .. } = hir_type {
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

    /// Emit drop instructions for all locals in the current function.
    /// Drops are emitted in LIFO order (last declared first) to ensure proper
    /// cleanup ordering, matching Rust's drop semantics.
    ///
    /// This is called before return statements to ensure all locals are properly
    /// cleaned up. For scope-level drops (e.g., block exit), use emit_scope_drops.
    pub(super) fn emit_function_drops(&mut self) -> MirLowerResult<()> {
        // First, collect information about which locals need dropping
        let locals_to_drop: Vec<(usize, crate::hir::TypeId)> = self.with_func(|func, _| {
            func.locals
                .iter()
                .enumerate()
                .rev() // LIFO order
                .filter_map(|(idx, local)| {
                    // Skip ghost variables (verification-only)
                    if local.is_ghost {
                        return None;
                    }
                    // Skip parameters (not owned by this function)
                    if local.kind.is_parameter() {
                        return None;
                    }
                    Some((idx, local.ty))
                })
                .collect()
        })?;

        // Now emit drop instructions for each local
        for (local_index, ty) in locals_to_drop {
            self.with_func(|func, current_block| {
                let addr_vreg = func.new_vreg();
                let value_vreg = func.new_vreg();
                let block = func.block_mut(current_block).unwrap();

                // Get address of local
                block.instructions.push(MirInst::LocalAddr {
                    dest: addr_vreg,
                    local_index,
                });

                // Load the value to drop
                block.instructions.push(MirInst::Load {
                    dest: value_vreg,
                    addr: addr_vreg,
                    ty,
                });

                // Emit the drop instruction
                block.instructions.push(MirInst::Drop { value: value_vreg, ty });
            })?;
        }

        Ok(())
    }

    /// Emit EndScope marker for a local going out of scope.
    /// This provides lifetime information for static analysis but is a no-op at runtime.
    pub(super) fn emit_end_scope(&mut self, local_index: usize) -> MirLowerResult<()> {
        self.with_func(|func, current_block| {
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::EndScope { local_index });
        })
    }
}

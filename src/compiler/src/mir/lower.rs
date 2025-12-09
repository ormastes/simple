use crate::hir::{HirModule, HirFunction, HirStmt, HirExpr, HirExprKind, TypeId, BinOp, UnaryOp};
use super::types::*;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum MirLowerError {
    #[error("Unsupported HIR construct: {0}")]
    Unsupported(String),
}

pub type MirLowerResult<T> = Result<T, MirLowerError>;

/// Lowers HIR to MIR
pub struct MirLowerer {
    current_func: Option<MirFunction>,
    current_block: BlockId,
}

impl MirLowerer {
    pub fn new() -> Self {
        Self {
            current_func: None,
            current_block: BlockId(0),
        }
    }

    /// Helper to set jump target if block terminator is still Unreachable
    fn finalize_block_jump(&mut self, target: BlockId) {
        let func = self.current_func.as_mut().unwrap();
        if let Some(block) = func.block_mut(self.current_block) {
            if matches!(block.terminator, Terminator::Unreachable) {
                block.terminator = Terminator::Jump(target);
            }
        }
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
        let mut mir_func = MirFunction::new(
            func.name.clone(),
            func.return_type,
            func.is_public,
        );

        // Add parameters
        for param in &func.params {
            mir_func.params.push(MirLocal {
                name: param.name.clone(),
                ty: param.ty,
                is_arg: true,
            });
        }

        // Add locals
        for local in &func.locals {
            mir_func.locals.push(MirLocal {
                name: local.name.clone(),
                ty: local.ty,
                is_arg: false,
            });
        }

        self.current_func = Some(mir_func);
        self.current_block = BlockId(0);

        // Lower body
        for stmt in &func.body {
            self.lower_stmt(stmt)?;
        }

        // Ensure we have a return
        let func_mut = self.current_func.as_mut().unwrap();
        if let Some(block) = func_mut.block_mut(self.current_block) {
            if matches!(block.terminator, Terminator::Unreachable) {
                block.terminator = Terminator::Return(None);
            }
        }

        Ok(self.current_func.take().unwrap())
    }

    fn lower_stmt(&mut self, stmt: &HirStmt) -> MirLowerResult<()> {
        match stmt {
            HirStmt::Let { local_index, value, .. } => {
                if let Some(val) = value {
                    let vreg = self.lower_expr(val)?;
                    let func = self.current_func.as_mut().unwrap();
                    let dest = func.new_vreg();
                    let block = func.block_mut(self.current_block).unwrap();
                    block.instructions.push(MirInst::LocalAddr { dest, local_index: *local_index });
                    block.instructions.push(MirInst::Store {
                        addr: dest,
                        value: vreg,
                        ty: val.ty
                    });
                }
                Ok(())
            }

            HirStmt::Assign { target, value } => {
                let val_reg = self.lower_expr(value)?;
                let addr_reg = self.lower_lvalue(target)?;

                let func = self.current_func.as_mut().unwrap();
                let block = func.block_mut(self.current_block).unwrap();
                block.instructions.push(MirInst::Store {
                    addr: addr_reg,
                    value: val_reg,
                    ty: value.ty
                });
                Ok(())
            }

            HirStmt::Return(value) => {
                let ret_reg = if let Some(v) = value {
                    Some(self.lower_expr(v)?)
                } else {
                    None
                };

                let func = self.current_func.as_mut().unwrap();
                let block = func.block_mut(self.current_block).unwrap();
                block.terminator = Terminator::Return(ret_reg);
                Ok(())
            }

            HirStmt::Expr(expr) => {
                self.lower_expr(expr)?;
                Ok(())
            }

            HirStmt::If { condition, then_block, else_block } => {
                let cond_reg = self.lower_expr(condition)?;

                let func = self.current_func.as_mut().unwrap();
                let then_id = func.new_block();
                let else_id = func.new_block();
                let merge_id = func.new_block();

                // Set branch terminator
                let block = func.block_mut(self.current_block).unwrap();
                block.terminator = Terminator::Branch {
                    cond: cond_reg,
                    then_block: then_id,
                    else_block: else_id,
                };

                // Lower then block
                self.current_block = then_id;
                for stmt in then_block {
                    self.lower_stmt(stmt)?;
                }
                self.finalize_block_jump(merge_id);

                // Lower else block
                self.current_block = else_id;
                if let Some(else_stmts) = else_block {
                    for stmt in else_stmts {
                        self.lower_stmt(stmt)?;
                    }
                }
                self.finalize_block_jump(merge_id);

                self.current_block = merge_id;
                Ok(())
            }

            HirStmt::While { condition, body } => {
                let func = self.current_func.as_mut().unwrap();
                let cond_id = func.new_block();
                let body_id = func.new_block();
                let exit_id = func.new_block();

                // Jump to condition check
                let block = func.block_mut(self.current_block).unwrap();
                block.terminator = Terminator::Jump(cond_id);

                // Check condition
                self.current_block = cond_id;
                let cond_reg = self.lower_expr(condition)?;
                let func = self.current_func.as_mut().unwrap();
                let block = func.block_mut(self.current_block).unwrap();
                block.terminator = Terminator::Branch {
                    cond: cond_reg,
                    then_block: body_id,
                    else_block: exit_id,
                };

                // Lower body
                self.current_block = body_id;
                for stmt in body {
                    self.lower_stmt(stmt)?;
                }
                self.finalize_block_jump(cond_id);

                self.current_block = exit_id;
                Ok(())
            }

            HirStmt::Loop { body } => {
                let func = self.current_func.as_mut().unwrap();
                let body_id = func.new_block();
                let exit_id = func.new_block();

                let block = func.block_mut(self.current_block).unwrap();
                block.terminator = Terminator::Jump(body_id);

                self.current_block = body_id;
                for stmt in body {
                    self.lower_stmt(stmt)?;
                }
                self.finalize_block_jump(body_id);

                self.current_block = exit_id;
                Ok(())
            }

            HirStmt::Break => {
                // Would need loop context to know where to jump
                Err(MirLowerError::Unsupported("break outside tracked loop".to_string()))
            }

            HirStmt::Continue => {
                Err(MirLowerError::Unsupported("continue outside tracked loop".to_string()))
            }
        }
    }

    fn lower_expr(&mut self, expr: &HirExpr) -> MirLowerResult<VReg> {
        let func = self.current_func.as_mut().unwrap();
        let dest = func.new_vreg();

        match &expr.kind {
            HirExprKind::Integer(n) => {
                let block = func.block_mut(self.current_block).unwrap();
                block.instructions.push(MirInst::ConstInt { dest, value: *n });
            }

            HirExprKind::Float(f) => {
                let block = func.block_mut(self.current_block).unwrap();
                block.instructions.push(MirInst::ConstFloat { dest, value: *f });
            }

            HirExprKind::Bool(b) => {
                let block = func.block_mut(self.current_block).unwrap();
                block.instructions.push(MirInst::ConstBool { dest, value: *b });
            }

            HirExprKind::Local(idx) => {
                let addr_reg = func.new_vreg();
                let block = func.block_mut(self.current_block).unwrap();
                block.instructions.push(MirInst::LocalAddr { dest: addr_reg, local_index: *idx });
                block.instructions.push(MirInst::Load { dest, addr: addr_reg, ty: expr.ty });
            }

            HirExprKind::Binary { op, left, right } => {
                // Need to borrow check carefully here
                let left_reg = self.lower_expr(left)?;
                let right_reg = self.lower_expr(right)?;

                let func = self.current_func.as_mut().unwrap();
                let block = func.block_mut(self.current_block).unwrap();
                block.instructions.push(MirInst::BinOp {
                    dest,
                    op: *op,
                    left: left_reg,
                    right: right_reg,
                });
            }

            HirExprKind::Unary { op, operand } => {
                let operand_reg = self.lower_expr(operand)?;

                let func = self.current_func.as_mut().unwrap();
                let block = func.block_mut(self.current_block).unwrap();
                block.instructions.push(MirInst::UnaryOp {
                    dest,
                    op: *op,
                    operand: operand_reg,
                });
            }

            HirExprKind::Call { func: callee, args } => {
                let mut arg_regs = Vec::new();
                for arg in args {
                    arg_regs.push(self.lower_expr(arg)?);
                }

                // Get function name
                let func_name = if let HirExprKind::Global(name) = &callee.kind {
                    name.clone()
                } else {
                    return Err(MirLowerError::Unsupported("indirect call".to_string()));
                };

                let func = self.current_func.as_mut().unwrap();
                let block = func.block_mut(self.current_block).unwrap();
                block.instructions.push(MirInst::Call {
                    dest: Some(dest),
                    func: func_name,
                    args: arg_regs,
                });
            }

            _ => {
                return Err(MirLowerError::Unsupported(format!("{:?}", expr.kind)));
            }
        }

        Ok(dest)
    }

    fn lower_lvalue(&mut self, expr: &HirExpr) -> MirLowerResult<VReg> {
        let func = self.current_func.as_mut().unwrap();
        let dest = func.new_vreg();

        match &expr.kind {
            HirExprKind::Local(idx) => {
                let block = func.block_mut(self.current_block).unwrap();
                block.instructions.push(MirInst::LocalAddr { dest, local_index: *idx });
                Ok(dest)
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
    use crate::hir;
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
        assert!(entry.instructions.iter().any(|i| matches!(i, MirInst::BinOp { op: BinOp::Add, .. })));
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
        let mir = compile_to_mir(
            "fn test() -> i64:\n    let x: i64 = 5\n    return x\n"
        ).unwrap();

        let func = &mir.functions[0];
        let entry = func.block(BlockId(0)).unwrap();

        // Should have LocalAddr and Store for the let
        assert!(entry.instructions.iter().any(|i| matches!(i, MirInst::LocalAddr { .. })));
        assert!(entry.instructions.iter().any(|i| matches!(i, MirInst::Store { .. })));
    }
}

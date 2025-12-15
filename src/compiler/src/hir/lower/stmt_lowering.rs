use simple_parser::{self as ast, Node};

use super::context::FunctionContext;
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;
use super::super::types::*;

impl Lowerer {
    pub(super) fn lower_block(
        &mut self,
        block: &ast::Block,
        ctx: &mut FunctionContext,
    ) -> LowerResult<Vec<HirStmt>> {
        let mut stmts = Vec::new();
        for node in &block.statements {
            stmts.extend(self.lower_node(node, ctx)?);
        }
        Ok(stmts)
    }

    fn lower_node(&mut self, node: &Node, ctx: &mut FunctionContext) -> LowerResult<Vec<HirStmt>> {
        match node {
            Node::Let(let_stmt) => {
                let ty = if let Some(t) = &let_stmt.ty {
                    self.resolve_type(t)?
                } else if let Some(val) = &let_stmt.value {
                    self.infer_type(val, ctx)?
                } else {
                    return Err(LowerError::CannotInferType);
                };

                let value = if let Some(v) = &let_stmt.value {
                    Some(self.lower_expr(v, ctx)?)
                } else {
                    None
                };

                let name = Self::extract_pattern_name(&let_stmt.pattern)
                    .ok_or_else(|| LowerError::Unsupported("complex pattern in let".to_string()))?;

                let local_index = ctx.add_local(name, ty, let_stmt.mutability);

                Ok(vec![HirStmt::Let {
                    local_index,
                    ty,
                    value,
                }])
            }

            Node::Assignment(assign) => {
                let target = self.lower_expr(&assign.target, ctx)?;
                let value = self.lower_expr(&assign.value, ctx)?;
                Ok(vec![HirStmt::Assign { target, value }])
            }

            Node::Return(ret) => {
                let value = if let Some(v) = &ret.value {
                    Some(self.lower_expr(v, ctx)?)
                } else {
                    None
                };
                Ok(vec![HirStmt::Return(value)])
            }

            Node::If(if_stmt) => {
                let condition = self.lower_expr(&if_stmt.condition, ctx)?;
                let then_block = self.lower_block(&if_stmt.then_block, ctx)?;

                let mut else_block = if let Some(eb) = &if_stmt.else_block {
                    Some(self.lower_block(eb, ctx)?)
                } else {
                    None
                };

                for (elif_cond, elif_body) in if_stmt.elif_branches.iter().rev() {
                    let elif_condition = self.lower_expr(elif_cond, ctx)?;
                    let elif_then = self.lower_block(elif_body, ctx)?;

                    else_block = Some(vec![HirStmt::If {
                        condition: elif_condition,
                        then_block: elif_then,
                        else_block,
                    }]);
                }

                Ok(vec![HirStmt::If {
                    condition,
                    then_block,
                    else_block,
                }])
            }

            Node::While(while_stmt) => {
                let condition = self.lower_expr(&while_stmt.condition, ctx)?;
                let body = self.lower_block(&while_stmt.body, ctx)?;
                Ok(vec![HirStmt::While { condition, body }])
            }

            Node::Loop(loop_stmt) => {
                let body = self.lower_block(&loop_stmt.body, ctx)?;
                Ok(vec![HirStmt::Loop { body }])
            }

            Node::Break(_) => Ok(vec![HirStmt::Break]),
            Node::Continue(_) => Ok(vec![HirStmt::Continue]),

            Node::Expression(expr) => {
                let hir_expr = self.lower_expr(expr, ctx)?;
                Ok(vec![HirStmt::Expr(hir_expr)])
            }

            _ => Err(LowerError::Unsupported(format!("{:?}", node))),
        }
    }
}

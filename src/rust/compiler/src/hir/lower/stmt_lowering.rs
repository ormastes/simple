use simple_parser::{self as ast, ast::ContractClause, Node};

use super::super::lifetime::{ReferenceOrigin, ScopeKind};
use super::super::types::*;
use super::context::FunctionContext;
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;

impl Lowerer {
    /// Lower a list of contract clauses to HIR contract clauses
    fn lower_contract_clauses(
        &mut self,
        clauses: &[ContractClause],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Vec<HirContractClause>> {
        let mut result = Vec::new();
        for clause in clauses {
            let condition = self.lower_expr(&clause.condition, ctx)?;
            result.push(HirContractClause {
                condition,
                message: clause.message.clone(),
            });
        }
        Ok(result)
    }

    /// Check if an AST expression is a move expression
    fn is_move_expr(expr: &ast::Expr) -> bool {
        matches!(
            expr,
            ast::Expr::Unary {
                op: ast::UnaryOp::Move,
                ..
            }
        )
    }

    pub(super) fn lower_block(&mut self, block: &ast::Block, ctx: &mut FunctionContext) -> LowerResult<Vec<HirStmt>> {
        // Enter block scope for lifetime tracking
        let span = block.statements.first().and_then(|n| match n {
            Node::Let(l) => Some(l.span),
            Node::Assignment(a) => Some(a.span),
            Node::Return(r) => Some(r.span),
            _ => None,
        });
        self.lifetime_context.enter_scope(ScopeKind::Block, span);

        let mut stmts = Vec::new();
        for node in &block.statements {
            stmts.extend(self.lower_node(node, ctx)?);
        }

        // Exit block scope
        self.lifetime_context.exit_scope();

        Ok(stmts)
    }

    fn lower_node(&mut self, node: &Node, ctx: &mut FunctionContext) -> LowerResult<Vec<HirStmt>> {
        match node {
            Node::Let(let_stmt) => {
                // Lower the value first (if present) to get the actual TypeId
                // This avoids the issue where infer_type and lower_expr create
                // different TypeIds for the same type (e.g., array types)
                let value = if let Some(v) = &let_stmt.value {
                    Some(self.lower_expr(v, ctx)?)
                } else {
                    None
                };

                // Use explicit type annotation if provided, otherwise use the
                // type from the lowered value to ensure TypeId consistency
                let ty = if let Some(t) = &let_stmt.ty {
                    self.resolve_type(t)?
                } else if let Some(ref v) = value {
                    v.ty
                } else {
                    return Err(LowerError::CannotInferType);
                };

                let name =
                    Self::extract_pattern_name(&let_stmt.pattern).ok_or_else(|| LowerError::LetBindingFailed {
                        pattern: format!("{:?}", let_stmt.pattern),
                    })?;

                // W1003: Check for mutable binding with shared pointer type
                self.check_mutable_shared_binding(&name, ty, let_stmt.mutability, let_stmt.span);

                // W1002: Check for implicit unique pointer copy (unless explicit move)
                if let Some(ref v) = value {
                    // Check if the original AST expression is a move expression
                    let is_explicit_move = if let Some(ast_value) = &let_stmt.value {
                        Self::is_move_expr(ast_value)
                    } else {
                        false
                    };
                    self.check_unique_copy(v, let_stmt.span, is_explicit_move);
                }

                // Register variable with lifetime context for tracking
                let current_lifetime = self.lifetime_context.current_lifetime();
                let origin = ReferenceOrigin::Local {
                    name: name.clone(),
                    scope: current_lifetime,
                };
                self.lifetime_context.register_variable(&name, origin);

                let local_index = ctx.add_local(name, ty, let_stmt.mutability);

                Ok(vec![HirStmt::Let { local_index, ty, value }])
            }

            Node::Assignment(assign) => {
                let target = self.lower_expr(&assign.target, ctx)?;
                let value = self.lower_expr(&assign.value, ctx)?;

                // E1052: Check for self mutation in immutable fn method
                self.check_self_mutation_in_fn_method(&target, ctx)?;

                // W1001: Check for shared pointer mutation
                self.check_shared_mutation(&target, assign.span);

                // W1006: Check for mutation without proper capability
                let has_mut = self.expr_has_mut_capability(&target, ctx);
                self.check_mutation_capability(&target, assign.span, has_mut);

                // E2006: Check for storage escape (assigning short-lived ref to longer-lived location)
                // If target is a field access and value is a local reference, check lifetimes
                if let HirExprKind::FieldAccess { receiver, .. } = &target.kind {
                    if self.is_reference_type(value.ty) {
                        // Get target's lifetime (from receiver)
                        if let HirExprKind::Local(target_idx) = &receiver.kind {
                            if let Some(target_local) = ctx.get_local(*target_idx) {
                                let target_origin =
                                    self.lifetime_context.get_variable_origin(&target_local.name).cloned();

                                // Get value's lifetime
                                if let HirExprKind::Local(value_idx) = &value.kind {
                                    if let Some(value_local) = ctx.get_local(*value_idx) {
                                        let value_origin =
                                            self.lifetime_context.get_variable_origin(&value_local.name).cloned();

                                        if let (Some(t_origin), Some(v_origin)) = (target_origin, value_origin) {
                                            let target_lt = t_origin.lifetime();
                                            let value_lt = v_origin.lifetime();
                                            // Check if value lifetime is shorter than target
                                            self.lifetime_context.check_storage(value_lt, target_lt, assign.span);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                Ok(vec![HirStmt::Assign { target, value }])
            }

            Node::Return(ret) => {
                let value = if let Some(v) = &ret.value {
                    let expr = self.lower_expr(v, ctx)?;

                    // Check for returning local reference (E2005)
                    // If the return expression is a variable reference, check its origin
                    if let HirExprKind::Local(idx) = &expr.kind {
                        if let Some(local) = ctx.get_local(*idx) {
                            // Clone the origin to avoid borrow checker issues
                            let origin = self.lifetime_context.get_variable_origin(&local.name).cloned();
                            if let Some(origin) = origin {
                                // Check if this is a reference type being returned
                                if self.is_reference_type(expr.ty) {
                                    self.lifetime_context.check_return(&origin, ret.span);
                                }
                            }
                        }
                    }

                    Some(expr)
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
                let invariants = self.lower_contract_clauses(&while_stmt.invariants, ctx)?;
                Ok(vec![HirStmt::While {
                    condition,
                    body,
                    invariants,
                }])
            }

            Node::For(for_stmt) => {
                // Extract pattern name (simple case: single identifier)
                let pattern = Self::extract_pattern_name(&for_stmt.pattern).unwrap_or_else(|| "item".to_string());
                let iterable = self.lower_expr(&for_stmt.iterable, ctx)?;
                let body = self.lower_block(&for_stmt.body, ctx)?;
                let invariants = self.lower_contract_clauses(&for_stmt.invariants, ctx)?;
                Ok(vec![HirStmt::For {
                    pattern,
                    iterable,
                    body,
                    invariants,
                }])
            }

            Node::Loop(loop_stmt) => {
                let body = self.lower_block(&loop_stmt.body, ctx)?;
                Ok(vec![HirStmt::Loop { body }])
            }

            Node::Break(_) => Ok(vec![HirStmt::Break]),
            Node::Continue(_) => Ok(vec![HirStmt::Continue]),

            Node::Assert(assert_stmt) => {
                let condition = self.lower_expr(&assert_stmt.condition, ctx)?;
                Ok(vec![HirStmt::Assert {
                    condition,
                    message: assert_stmt.message.clone(),
                }])
            }

            Node::Assume(assume_stmt) => {
                let condition = self.lower_expr(&assume_stmt.condition, ctx)?;
                Ok(vec![HirStmt::Assume {
                    condition,
                    message: assume_stmt.message.clone(),
                }])
            }

            Node::Admit(admit_stmt) => {
                let condition = self.lower_expr(&admit_stmt.condition, ctx)?;
                Ok(vec![HirStmt::Admit {
                    condition,
                    message: admit_stmt.message.clone(),
                }])
            }

            Node::ProofHint(proof_hint_stmt) => {
                // VER-020: Proof hint for Lean
                // At runtime, this is erased (no-op)
                // In verification mode, it provides tactic hints to Lean
                Ok(vec![HirStmt::ProofHint {
                    hint: proof_hint_stmt.hint.clone(),
                }])
            }

            Node::Calc(calc_stmt) => {
                // VER-021: Calculational proof block for Lean
                // At runtime, this is erased (no-op)
                // In verification mode, it generates a Lean calc proof
                let mut steps = Vec::new();
                for step in &calc_stmt.steps {
                    let expr = self.lower_expr(&step.expr, ctx)?;
                    steps.push(crate::hir::types::HirCalcStep {
                        expr,
                        justification: step.justification.clone(),
                    });
                }
                Ok(vec![HirStmt::Calc { steps }])
            }

            Node::Expression(expr) => {
                let hir_expr = self.lower_expr(expr, ctx)?;
                Ok(vec![HirStmt::Expr(hir_expr)])
            }

            _ => Err(LowerError::Unsupported(format!("{:?}", node))),
        }
    }
}

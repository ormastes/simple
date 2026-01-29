use simple_parser::{self as ast, ast::ContractClause, ast::Expr, ast::MatchStmt, ast::Mutability, ast::Pattern, Node};

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
                // Check for tuple pattern destructuring: val (a, b) = expr
                // Also handle Pattern::Typed wrapping a tuple pattern
                let inner_pattern = match &let_stmt.pattern {
                    Pattern::Typed { pattern, .. } => pattern.as_ref(),
                    p => p,
                };
                if let Pattern::Tuple(patterns) = inner_pattern {
                    return self.lower_tuple_destructuring(patterns, let_stmt, ctx);
                }

                // Lower the value first (if present) to get the actual TypeId
                // This avoids the issue where infer_type and lower_expr create
                // different TypeIds for the same type (e.g., array types)
                let value = if let Some(v) = &let_stmt.value {
                    let lowered = self.lower_expr(v, ctx)?;
                    Some(lowered)
                } else {
                    None
                };

                // Extract type annotation from either let_stmt.ty OR Pattern::Typed
                // In Simple syntax, `var x: T = v` puts the type in Pattern::Typed
                let pattern_type = Self::extract_pattern_type(&let_stmt.pattern);

                // Use explicit type annotation if provided, otherwise use the
                // type from the lowered value to ensure TypeId consistency
                let ty = if let Some(t) = &let_stmt.ty {
                    // Type on the let statement itself
                    self.resolve_type(t)?
                } else if let Some(ref pt) = pattern_type {
                    // Type annotation on the pattern (var x: T = v)
                    self.resolve_type(pt)?
                } else if let Some(ref v) = value {
                    // Infer from value
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
                let iterable = self.lower_expr(&for_stmt.iterable, ctx)?;

                // Infer the element type from the iterable type
                // Handles: Arrays [T] → T, Strings → u8, Tuples → common type
                // Ranges and custom iterators fallback to i64
                let element_ty = self
                    .module
                    .types
                    .get_iterable_element(iterable.ty)
                    .unwrap_or(crate::hir::TypeId::ANY);

                // Check if this is a tuple pattern for destructuring
                if let Pattern::Tuple(patterns) = &for_stmt.pattern {
                    // Tuple destructuring in for loop: for (x, y) in items:
                    // Lower to: for __tuple_temp in items: { val x = __tuple_temp[0]; val y = __tuple_temp[1]; ... }
                    let temp_name = "__for_tuple_temp".to_string();
                    let temp_idx = ctx.add_local(temp_name.clone(), element_ty, Mutability::Immutable);

                    // Get tuple element types if available
                    let element_types = if let Some(HirType::Tuple(types)) = self.module.types.get(element_ty) {
                        Some(types.clone())
                    } else {
                        None
                    };

                    // Create let bindings for each tuple element
                    let mut destructure_stmts = Vec::new();
                    for (i, pattern) in patterns.iter().enumerate() {
                        let elem_ty = element_types
                            .as_ref()
                            .and_then(|types| types.get(i).copied())
                            .unwrap_or(TypeId::ANY);

                        // Create an index expression: __for_tuple_temp[i]
                        let index_expr = HirExpr {
                            kind: HirExprKind::Index {
                                receiver: Box::new(HirExpr {
                                    kind: HirExprKind::Local(temp_idx),
                                    ty: element_ty,
                                }),
                                index: Box::new(HirExpr {
                                    kind: HirExprKind::Integer(i as i64),
                                    ty: TypeId::I64,
                                }),
                            },
                            ty: elem_ty,
                        };

                        // Extract variable name from pattern
                        if let Some(name) = Self::extract_pattern_name(pattern) {
                            let local_idx = ctx.add_local(name, elem_ty, Mutability::Immutable);
                            destructure_stmts.push(HirStmt::Let {
                                local_index: local_idx,
                                ty: elem_ty,
                                value: Some(index_expr),
                            });
                        }
                        // Wildcards are ignored
                    }

                    // Lower the body with destructured variables in scope
                    let mut body = self.lower_block(&for_stmt.body, ctx)?;

                    // Prepend destructure statements to body
                    let mut new_body = destructure_stmts;
                    new_body.append(&mut body);

                    let invariants = self.lower_contract_clauses(&for_stmt.invariants, ctx)?;
                    Ok(vec![HirStmt::For {
                        pattern: temp_name,
                        iterable,
                        body: new_body,
                        invariants,
                    }])
                } else {
                    // Simple pattern (single identifier)
                    let pattern = Self::extract_pattern_name(&for_stmt.pattern).unwrap_or_else(|| "item".to_string());

                    // Add the loop variable to the context BEFORE lowering the body
                    ctx.add_local(pattern.clone(), element_ty, Mutability::Immutable);

                    let body = self.lower_block(&for_stmt.body, ctx)?;
                    let invariants = self.lower_contract_clauses(&for_stmt.invariants, ctx)?;
                    Ok(vec![HirStmt::For {
                        pattern,
                        iterable,
                        body,
                        invariants,
                    }])
                }
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
                // Intercept BDD/SSpec calls at statement level so we can emit
                // start/body/end sequences (describe, it, expect, etc.)
                if let Some(stmts) = self.try_lower_bdd_statement(expr, ctx)? {
                    return Ok(stmts);
                }
                let hir_expr = self.lower_expr(expr, ctx)?;
                Ok(vec![HirStmt::Expr(hir_expr)])
            }

            Node::Match(match_stmt) => {
                // Lower match statement to a chain of If-Else statements
                self.lower_match_stmt(match_stmt, ctx)
            }

            Node::Pass(_) => {
                // Pass is a no-op statement, returns empty statement list
                Ok(vec![])
            }

            Node::Function(f) => {
                // Nested function definition in statement position
                // For now, skip with a warning - nested functions are not yet supported in native compilation
                eprintln!(
                    "[WARNING] Nested function '{}' is not yet supported in native compilation, skipping",
                    f.name
                );
                Ok(vec![])
            }

            // Import statements are resolved at the module level (module_pass.rs).
            // When they appear inside a function body (e.g. SSpec test files wrapped
            // into main), they are a no-op at code generation time.
            Node::UseStmt(_)
            | Node::MultiUse(_)
            | Node::CommonUseStmt(_)
            | Node::ExportUseStmt(_)
            | Node::AutoImportStmt(_) => Ok(vec![]),

            _ => panic!("unimplemented HIR statement lowering for: {:?}", node),
        }
    }

    /// Lower a match statement to a chain of If-Else statements
    fn lower_match_stmt(&mut self, match_stmt: &MatchStmt, ctx: &mut FunctionContext) -> LowerResult<Vec<HirStmt>> {
        // Lower the subject expression once
        let subject_hir = self.lower_expr(&match_stmt.subject, ctx)?;
        let subject_ty = subject_hir.ty;

        // Create a temporary local to hold the subject value
        let subject_idx = ctx.locals.len();
        ctx.add_local("$match_subject".to_string(), subject_ty, Mutability::Immutable);

        // Store the subject value
        let store_stmt = HirStmt::Let {
            local_index: subject_idx,
            ty: subject_ty,
            value: Some(subject_hir),
        };

        // Build the chain of If-Else statements from the arms
        let if_chain = self.lower_match_arms_stmt(subject_idx, subject_ty, &match_stmt.arms, ctx)?;

        let mut result = vec![store_stmt];
        result.extend(if_chain);
        Ok(result)
    }

    /// Lower match arms to a chain of If-Else statements
    fn lower_match_arms_stmt(
        &mut self,
        subject_idx: usize,
        subject_ty: TypeId,
        arms: &[ast::MatchArm],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Vec<HirStmt>> {
        if arms.is_empty() {
            return Ok(Vec::new());
        }

        let arm = &arms[0];
        let remaining_arms = &arms[1..];

        // Check if this is a wildcard pattern (always matches)
        // But: if subject is an enum and the identifier matches a variant name,
        // treat it as an enum pattern, not a binding.
        if matches!(&arm.pattern, Pattern::Wildcard) {
            return self.lower_block(&arm.body, ctx);
        }
        if let Pattern::Identifier(name) = &arm.pattern {
            let is_enum_variant = if let Some(HirType::Enum {
                variants,
                name: enum_name,
                ..
            }) = self.module.types.get(subject_ty)
            {
                variants.iter().any(|(vn, _)| vn == name)
            } else {
                false
            };
            if !is_enum_variant {
                // Plain binding pattern - always matches
                return self.lower_block(&arm.body, ctx);
            }
            // Otherwise fall through to treat as enum pattern
        }

        // Generate the condition for this pattern
        let condition = self.lower_pattern_condition_stmt(subject_idx, subject_ty, &arm.pattern, ctx)?;

        // Extract pattern bindings and add them to context
        // This needs to happen after pattern condition but before guard/body
        let bindings = self.extract_pattern_bindings(&arm.pattern, subject_ty);
        for (name, ty) in &bindings {
            ctx.add_local(name.clone(), *ty, Mutability::Immutable);
        }

        // Handle guard expression if present (bindings are now in scope)
        let final_condition = if let Some(guard) = &arm.guard {
            let guard_hir = self.lower_expr(guard, ctx)?;
            HirExpr {
                kind: HirExprKind::Binary {
                    op: BinOp::And,
                    left: Box::new(condition),
                    right: Box::new(guard_hir),
                },
                ty: TypeId::BOOL,
            }
        } else {
            condition
        };

        // Generate payload extraction statements for enum bindings
        let mut binding_stmts = Vec::new();
        if let Pattern::Enum {
            payload: Some(payload_patterns),
            ..
        } = &arm.pattern
        {
            // Extract payload from enum subject, then bind to locals
            let payload_expr = HirExpr {
                kind: HirExprKind::BuiltinCall {
                    name: "rt_enum_payload".to_string(),
                    args: vec![HirExpr {
                        kind: HirExprKind::Local(subject_idx),
                        ty: subject_ty,
                    }],
                },
                ty: TypeId::ANY,
            };

            for (i, p) in payload_patterns.iter().enumerate() {
                if let Pattern::Identifier(name) | Pattern::MutIdentifier(name) = p {
                    if let Some(local_idx) = ctx.local_map.get(name) {
                        let local_idx = *local_idx;
                        // For single-payload enums, use payload directly
                        // For multi-payload, would need tuple indexing
                        let value = if payload_patterns.len() == 1 {
                            payload_expr.clone()
                        } else {
                            // Multi-field: index into tuple payload
                            HirExpr {
                                kind: HirExprKind::Index {
                                    receiver: Box::new(payload_expr.clone()),
                                    index: Box::new(HirExpr {
                                        kind: HirExprKind::Integer(i as i64),
                                        ty: TypeId::I64,
                                    }),
                                },
                                ty: TypeId::ANY,
                            }
                        };
                        binding_stmts.push(HirStmt::Let {
                            local_index: local_idx,
                            ty: TypeId::ANY,
                            value: Some(value),
                        });
                    }
                }
            }
        }

        // Lower the arm body with bindings in scope
        let mut then_block = Vec::new();
        then_block.extend(binding_stmts);
        then_block.extend(self.lower_block(&arm.body, ctx)?);

        // Restore context (remove pattern bindings from name scope only)
        // Keep locals in ctx.locals so they get proper indices in the final function.
        // Truncating would cause local_index references in HIR stmts to be out of bounds.
        for (name, _) in &bindings {
            ctx.local_map.remove(name);
        }

        // Recursively build the else branch from remaining arms
        let else_block = self.lower_match_arms_stmt(subject_idx, subject_ty, remaining_arms, ctx)?;

        // Build an If statement
        let if_stmt = HirStmt::If {
            condition: final_condition,
            then_block,
            else_block: if else_block.is_empty() { None } else { Some(else_block) },
        };

        Ok(vec![if_stmt])
    }

    /// Generate a condition expression for pattern matching
    fn lower_pattern_condition_stmt(
        &mut self,
        subject_idx: usize,
        subject_ty: TypeId,
        pattern: &Pattern,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let subject_ref = HirExpr {
            kind: HirExprKind::Local(subject_idx),
            ty: subject_ty,
        };

        match pattern {
            Pattern::Wildcard => {
                // Always matches
                Ok(HirExpr {
                    kind: HirExprKind::Bool(true),
                    ty: TypeId::BOOL,
                })
            }
            Pattern::Identifier(name) => {
                // Check if this identifier is an enum variant of the subject type
                let enum_info = if let Some(HirType::Enum {
                    variants,
                    name: enum_name,
                    ..
                }) = self.module.types.get(subject_ty)
                {
                    if variants.iter().any(|(vn, _)| vn == name) {
                        Some(enum_name.clone())
                    } else {
                        None
                    }
                } else {
                    None
                };

                if let Some(_enum_name) = enum_info {
                    // Treat as enum variant pattern using rt_enum_check_discriminant
                    let expected_disc: i64 = {
                        use std::collections::hash_map::DefaultHasher;
                        use std::hash::{Hash, Hasher};
                        let mut hasher = DefaultHasher::new();
                        name.hash(&mut hasher);
                        (hasher.finish() & 0xFFFFFFFF) as i64
                    };

                    let expected_val = HirExpr {
                        kind: HirExprKind::Integer(expected_disc),
                        ty: TypeId::I64,
                    };

                    Ok(HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: "rt_enum_check_discriminant".to_string(),
                            args: vec![subject_ref, expected_val],
                        },
                        ty: TypeId::BOOL,
                    })
                } else {
                    // Plain binding - always matches
                    Ok(HirExpr {
                        kind: HirExprKind::Bool(true),
                        ty: TypeId::BOOL,
                    })
                }
            }
            Pattern::Literal(lit_expr) => {
                // Compare subject == literal
                let lit_hir = self.lower_expr(lit_expr, ctx)?;

                // Check if subject is a string type - use rt_string_eq for string comparison
                let is_string =
                    subject_ty == TypeId::STRING || matches!(self.module.types.get(subject_ty), Some(HirType::String));

                if is_string {
                    // Use builtin string equality for string comparison
                    Ok(HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: "rt_string_eq".to_string(),
                            args: vec![subject_ref, lit_hir],
                        },
                        ty: TypeId::BOOL,
                    })
                } else {
                    // Use standard comparison for other types
                    Ok(HirExpr {
                        kind: HirExprKind::Binary {
                            op: BinOp::Eq,
                            left: Box::new(subject_ref),
                            right: Box::new(lit_hir),
                        },
                        ty: TypeId::BOOL,
                    })
                }
            }
            Pattern::Or(patterns) => {
                // Any of the patterns match: p1 || p2 || p3 ...
                if patterns.is_empty() {
                    return Ok(HirExpr {
                        kind: HirExprKind::Bool(false),
                        ty: TypeId::BOOL,
                    });
                }

                let mut result = self.lower_pattern_condition_stmt(subject_idx, subject_ty, &patterns[0], ctx)?;
                for p in &patterns[1..] {
                    let p_cond = self.lower_pattern_condition_stmt(subject_idx, subject_ty, p, ctx)?;
                    result = HirExpr {
                        kind: HirExprKind::Binary {
                            op: BinOp::Or,
                            left: Box::new(result),
                            right: Box::new(p_cond),
                        },
                        ty: TypeId::BOOL,
                    };
                }
                Ok(result)
            }
            Pattern::Range { start, end, inclusive } => {
                // subject >= start && subject <= end (or < end if not inclusive)
                let start_hir = self.lower_expr(start, ctx)?;
                let end_hir = self.lower_expr(end, ctx)?;

                let gte_start = HirExpr {
                    kind: HirExprKind::Binary {
                        op: BinOp::GtEq,
                        left: Box::new(subject_ref.clone()),
                        right: Box::new(start_hir),
                    },
                    ty: TypeId::BOOL,
                };

                let end_op = if *inclusive { BinOp::LtEq } else { BinOp::Lt };
                let lte_end = HirExpr {
                    kind: HirExprKind::Binary {
                        op: end_op,
                        left: Box::new(subject_ref),
                        right: Box::new(end_hir),
                    },
                    ty: TypeId::BOOL,
                };

                Ok(HirExpr {
                    kind: HirExprKind::Binary {
                        op: BinOp::And,
                        left: Box::new(gte_start),
                        right: Box::new(lte_end),
                    },
                    ty: TypeId::BOOL,
                })
            }
            Pattern::Enum { name: _, variant, .. } => {
                // Special handling for None - check both nil and enum None
                if variant == "None" {
                    return Ok(HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: "rt_is_none".to_string(),
                            args: vec![subject_ref],
                        },
                        ty: TypeId::BOOL,
                    });
                }
                // Special handling for Some - check not-none
                if variant == "Some" {
                    return Ok(HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: "rt_is_some".to_string(),
                            args: vec![subject_ref],
                        },
                        ty: TypeId::BOOL,
                    });
                }

                // Use rt_enum_check_discriminant(subject, expected_disc) -> bool
                // All enums use hashed variant name discriminants consistently
                let expected_disc: i64 = {
                    use std::collections::hash_map::DefaultHasher;
                    use std::hash::{Hash, Hasher};
                    let mut hasher = DefaultHasher::new();
                    variant.hash(&mut hasher);
                    (hasher.finish() & 0xFFFFFFFF) as i64
                };

                let expected_val = HirExpr {
                    kind: HirExprKind::Integer(expected_disc),
                    ty: TypeId::I64,
                };

                Ok(HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: "rt_enum_check_discriminant".to_string(),
                        args: vec![subject_ref, expected_val],
                    },
                    ty: TypeId::BOOL,
                })
            }
            _ => {
                eprintln!("[WARN] unimplemented pattern-to-expr lowering for: {:?}", pattern);
                Ok(HirExpr {
                    kind: HirExprKind::Bool(false),
                    ty: TypeId::BOOL,
                })
            }
        }
    }

    /// Lower a tuple destructuring let binding: val (a, b) = expr
    ///
    /// This is lowered to:
    /// 1. Evaluate the tuple expression and store in a temp
    /// 2. For each pattern element, create a let binding that indexes into the tuple
    fn lower_tuple_destructuring(
        &mut self,
        patterns: &[Pattern],
        let_stmt: &ast::LetStmt,
        ctx: &mut FunctionContext,
    ) -> LowerResult<Vec<HirStmt>> {
        // Lower the value expression
        let value = if let Some(v) = &let_stmt.value {
            self.lower_expr(v, ctx)?
        } else {
            return Err(LowerError::CannotInferType);
        };

        let tuple_ty = value.ty;

        // Create a temp variable to hold the tuple value
        let temp_idx = ctx.add_local("__tuple_temp".to_string(), tuple_ty, Mutability::Immutable);

        let mut stmts = vec![HirStmt::Let {
            local_index: temp_idx,
            ty: tuple_ty,
            value: Some(value),
        }];

        // Get tuple element types if available
        let element_types = if let Some(HirType::Tuple(types)) = self.module.types.get(tuple_ty) {
            Some(types.clone())
        } else {
            None
        };

        // For each pattern element, create a let binding
        for (i, pattern) in patterns.iter().enumerate() {
            // Get the element type (if known) or use ANY
            let elem_ty = element_types
                .as_ref()
                .and_then(|types| types.get(i).copied())
                .unwrap_or(TypeId::ANY);

            // Create an index expression: __tuple_temp[i]
            let index_expr = HirExpr {
                kind: HirExprKind::Index {
                    receiver: Box::new(HirExpr {
                        kind: HirExprKind::Local(temp_idx),
                        ty: tuple_ty,
                    }),
                    index: Box::new(HirExpr {
                        kind: HirExprKind::Integer(i as i64),
                        ty: TypeId::I64,
                    }),
                },
                ty: elem_ty,
            };

            // Extract variable name from pattern
            if let Some(name) = Self::extract_pattern_name(pattern) {
                let local_idx = ctx.add_local(name, elem_ty, let_stmt.mutability);
                stmts.push(HirStmt::Let {
                    local_index: local_idx,
                    ty: elem_ty,
                    value: Some(index_expr),
                });
            }
            // Wildcards are ignored
        }

        Ok(stmts)
    }

    /// Try to lower a BDD/SSpec call expression as a statement sequence.
    /// Returns Some(stmts) if the expression is a BDD call, None otherwise.
    ///
    /// Handles: describe, context, it, test, expect, before_each, after_each
    fn try_lower_bdd_statement(
        &mut self,
        expr: &Expr,
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<Vec<HirStmt>>> {
        let (name, args) = match expr {
            Expr::Call { callee, args } => {
                if let Expr::Identifier(name) = callee.as_ref() {
                    (name.as_str(), args)
                } else {
                    return Ok(None);
                }
            }
            _ => return Ok(None),
        };

        match name {
            "describe" | "context" => {
                // describe "name": body
                // → rt_bdd_describe_start_rv(name), <body>, rt_bdd_describe_end()
                let mut stmts = Vec::new();

                // Lower the name argument (first arg)
                let name_hir = if !args.is_empty() {
                    self.lower_expr(&args[0].value, ctx)?
                } else {
                    HirExpr { kind: HirExprKind::String("unnamed".to_string()), ty: TypeId::STRING }
                };

                // Emit rt_bdd_describe_start_rv(name)
                stmts.push(HirStmt::Expr(HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: "rt_bdd_describe_start_rv".to_string(),
                        args: vec![name_hir],
                    },
                    ty: TypeId::NIL,
                }));

                // Lower body (second arg: Lambda { body: DoBlock([...]) })
                if args.len() > 1 {
                    self.lower_bdd_body(&args[1].value, &mut stmts, ctx)?;
                }

                // Emit rt_bdd_describe_end()
                stmts.push(HirStmt::Expr(HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: "rt_bdd_describe_end".to_string(),
                        args: vec![],
                    },
                    ty: TypeId::NIL,
                }));

                Ok(Some(stmts))
            }

            "it" | "test" | "example" | "specify" => {
                // it "name": body
                // → rt_bdd_it_start_rv(name), <body>, rt_bdd_it_end(passed)
                let mut stmts = Vec::new();

                let name_hir = if !args.is_empty() {
                    self.lower_expr(&args[0].value, ctx)?
                } else {
                    HirExpr { kind: HirExprKind::String("unnamed".to_string()), ty: TypeId::STRING }
                };

                // Emit rt_bdd_it_start_rv(name)
                stmts.push(HirStmt::Expr(HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: "rt_bdd_it_start_rv".to_string(),
                        args: vec![name_hir],
                    },
                    ty: TypeId::NIL,
                }));

                // Lower body
                if args.len() > 1 {
                    self.lower_bdd_body(&args[1].value, &mut stmts, ctx)?;
                }

                // Emit rt_bdd_it_end(1) - passed=1, failure is detected by expect
                stmts.push(HirStmt::Expr(HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: "rt_bdd_it_end".to_string(),
                        args: vec![HirExpr { kind: HirExprKind::Integer(1), ty: TypeId::I64 }],
                    },
                    ty: TypeId::NIL,
                }));

                Ok(Some(stmts))
            }

            "expect" => {
                // expect expr  → rt_bdd_expect_truthy_rv(expr)
                // expect a == b → rt_bdd_expect_eq_rv(a, b)
                if args.is_empty() {
                    return Ok(None);
                }
                let arg_expr = &args[0].value;

                // Check for equality comparison: expect a == b
                if let Expr::Binary { op, left, right } = arg_expr {
                    if matches!(op, simple_parser::BinOp::Eq) {
                        let left_hir = self.lower_expr(left, ctx)?;
                        let right_hir = self.lower_expr(right, ctx)?;
                        return Ok(Some(vec![HirStmt::Expr(HirExpr {
                            kind: HirExprKind::BuiltinCall {
                                name: "rt_bdd_expect_eq_rv".to_string(),
                                args: vec![left_hir, right_hir],
                            },
                            ty: TypeId::NIL,
                        })]));
                    }
                }

                // General case: expect <expr>
                let expr_hir = self.lower_expr(arg_expr, ctx)?;
                Ok(Some(vec![HirStmt::Expr(HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: "rt_bdd_expect_truthy_rv".to_string(),
                        args: vec![expr_hir],
                    },
                    ty: TypeId::NIL,
                })]))
            }

            "before_each" => {
                // For now, just execute the block inline (simplified)
                if args.len() > 0 {
                    let mut stmts = Vec::new();
                    self.lower_bdd_body(&args[0].value, &mut stmts, ctx)?;
                    if !stmts.is_empty() {
                        return Ok(Some(stmts));
                    }
                }
                Ok(None)
            }

            "after_each" => {
                // For now, skip after_each (simplified)
                Ok(Some(vec![]))
            }

            _ => Ok(None),
        }
    }

    /// Extract and lower the body of a BDD block (describe/it/before_each).
    /// The body is typically a Lambda { body: DoBlock([nodes]) } from colon-block syntax.
    fn lower_bdd_body(
        &mut self,
        body_expr: &Expr,
        stmts: &mut Vec<HirStmt>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<()> {
        // Colon-block: Lambda { params: [], body: DoBlock([...]) }
        if let Expr::Lambda { body, .. } = body_expr {
            if let Expr::DoBlock(body_stmts) = body.as_ref() {
                for stmt in body_stmts {
                    let lowered = self.lower_node(stmt, ctx)?;
                    stmts.extend(lowered);
                }
                return Ok(());
            }
        }
        // Direct DoBlock (shouldn't happen but handle it)
        if let Expr::DoBlock(body_stmts) = body_expr {
            for stmt in body_stmts {
                let lowered = self.lower_node(stmt, ctx)?;
                stmts.extend(lowered);
            }
            return Ok(());
        }
        // Fallback: lower as expression
        let body_hir = self.lower_expr(body_expr, ctx)?;
        stmts.push(HirStmt::Expr(body_hir));
        Ok(())
    }
}

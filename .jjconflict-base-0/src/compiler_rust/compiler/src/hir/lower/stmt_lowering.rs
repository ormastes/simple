use simple_parser::{
    self as ast, ast::ContractClause, ast::Expr, ast::MatchStmt, ast::Mutability, ast::Pattern, ast::SkipBody, Node,
};

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

    fn lower_elif_chain(
        &mut self,
        branches: &[(Option<Pattern>, Expr, ast::Block)],
        mut else_block: Option<Vec<HirStmt>>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<Vec<HirStmt>>> {
        for (pattern, condition, body) in branches.iter().rev() {
            if let Some(pattern) = pattern {
                // `elif val v = expr.?:` has the same ExistsCheck-unwrap
                // requirement as the main `if val v = expr.?:` path above (S70
                // root cause for native-smoke-matrix `option_nil_check`) — see
                // the comment on the `Node::If` let_pattern branch.
                let condition_expr = match condition {
                    Expr::ExistsCheck(inner) => inner.as_ref(),
                    other => other,
                };
                let subject = self.lower_expr(condition_expr, ctx)?;
                let subject_ty = subject.ty;
                let subject_idx = ctx.locals.len();
                ctx.add_local("$if_let_subject_elif".to_string(), subject_ty, Mutability::Immutable);
                let store = HirStmt::Let {
                    local_index: subject_idx,
                    ty: subject_ty,
                    value: Some(subject),
                };
                let condition = self.if_let_pattern_condition(subject_idx, subject_ty, pattern, ctx)?;
                let bindings = self.extract_pattern_bindings(pattern, subject_ty);
                let mutability = if matches!(pattern, Pattern::MutIdentifier(_)) {
                    Mutability::Mutable
                } else {
                    Mutability::Immutable
                };
                for (name, ty) in &bindings {
                    ctx.add_local(name.clone(), *ty, mutability);
                }
                let mut then_block = self.build_pattern_binding_stmts(pattern, subject_idx, subject_ty, &bindings, ctx);
                then_block.extend(self.lower_block(body, ctx)?);
                for (name, _) in &bindings {
                    ctx.local_map.remove(name);
                }
                else_block = Some(vec![
                    store,
                    HirStmt::If {
                        condition,
                        then_block,
                        else_block,
                    },
                ]);
            } else {
                let condition = self.lower_expr(condition, ctx)?;
                let then_block = self.lower_block(body, ctx)?;
                else_block = Some(vec![HirStmt::If {
                    condition,
                    then_block,
                    else_block,
                }]);
            }
        }
        Ok(else_block)
    }

    pub(super) fn lower_node(&mut self, node: &Node, ctx: &mut FunctionContext) -> LowerResult<Vec<HirStmt>> {
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
                let mut value = if let Some(v) = &let_stmt.value {
                    let lowered = self.lower_expr(v, ctx)?;
                    Some(lowered)
                } else {
                    None
                };
                if matches!(inner_pattern, Pattern::Wildcard) {
                    return Ok(value.map(HirStmt::Expr).into_iter().collect());
                }

                // Extract type annotation from either let_stmt.ty OR Pattern::Typed
                // In Simple syntax, `var x: T = v` puts the type in Pattern::Typed
                let pattern_type = Self::extract_pattern_type(&let_stmt.pattern);

                // Use explicit type annotation if provided, otherwise use the
                // type from the lowered value to ensure TypeId consistency
                let has_explicit_type = let_stmt.ty.is_some() || pattern_type.is_some();
                let mut ty = if let Some(t) = &let_stmt.ty {
                    // Type on the let statement itself
                    self.resolve_type(t)?
                } else if let Some(pt) = pattern_type {
                    // Type annotation on the pattern (var x: T = v)
                    self.resolve_type(pt)?
                } else if let Some(ref v) = value {
                    // Infer from value
                    v.ty
                } else if self.lenient_types {
                    TypeId::ANY
                } else {
                    return Err(LowerError::CannotInferType);
                };

                let name = Self::extract_pattern_name(&let_stmt.pattern).unwrap_or_else(|| {
                    if self.lenient_types {
                        // In lenient mode, generate a dummy name for complex patterns (e.g., Wildcard)
                        format!("_discard_{}", ctx.locals.len())
                    } else {
                        String::new()
                    }
                });
                if name.is_empty() {
                    return Err(LowerError::LetBindingFailed {
                        pattern: format!("{:?}", let_stmt.pattern),
                    });
                }

                let is_untyped_empty_array_binding = !has_explicit_type
                    && value
                        .as_ref()
                        .is_some_and(|expr| matches!(&expr.kind, HirExprKind::Array(items) if items.is_empty()));
                if is_untyped_empty_array_binding {
                    let any_array_ty = self.module.types.register(HirType::Array {
                        element: TypeId::ANY,
                        size: Some(0),
                    });
                    if let Some(expr) = value.as_mut() {
                        expr.ty = any_array_ty;
                    }
                    ty = any_array_ty;
                }

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
                if is_untyped_empty_array_binding {
                    self.untyped_empty_array_locals.insert(local_index);
                }

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
                if let Some(pattern) = &if_stmt.let_pattern {
                    // if val Some(x) = expr: / if var Ok(v) = expr:
                    // Lower as pattern match (same mechanism as match arms)

                    // 1. Lower subject (the condition expr is the value to match).
                    // `if val v = expr.?:` parses `expr.?` as `Expr::ExistsCheck`
                    // (a standalone presence-check operator that normally yields a
                    // bool). Combined with a `val` binding the intent is "bind v to
                    // the unwrapped value of expr if present" — the same idiom as
                    // the bare `if val v = expr:` form. Unwrap one ExistsCheck layer
                    // here so the subject is `expr` itself (Option-typed), not the
                    // bool presence check; otherwise `v` gets bound to the
                    // ExistsCheck's bool result instead of the unwrapped value
                    // (S70 root cause for native-smoke-matrix `option_nil_check`:
                    // `if val v = x.?: return v` returned 1 (true, boxed) instead
                    // of the unwrapped 7).
                    let condition_expr = match &if_stmt.condition {
                        Expr::ExistsCheck(inner) => inner.as_ref(),
                        other => other,
                    };
                    let subject_hir = self.lower_expr(condition_expr, ctx)?;
                    let subject_ty = subject_hir.ty;

                    // 2. Create temp local for subject value
                    let subject_idx = ctx.locals.len();
                    ctx.add_local("$if_let_subject".to_string(), subject_ty, Mutability::Immutable);

                    let store_stmt = HirStmt::Let {
                        local_index: subject_idx,
                        ty: subject_ty,
                        value: Some(subject_hir),
                    };

                    // 3. Generate pattern condition (rt_is_some for Some, etc.)
                    let condition = self.if_let_pattern_condition(subject_idx, subject_ty, pattern, ctx)?;

                    // 4. Extract + register bindings
                    let bindings = self.extract_pattern_bindings(pattern, subject_ty);
                    let is_mut = if_stmt
                        .let_pattern
                        .as_ref()
                        .is_some_and(|p| matches!(p, Pattern::MutIdentifier(_)));
                    let mutability = if is_mut {
                        Mutability::Mutable
                    } else {
                        Mutability::Immutable
                    };
                    for (name, ty) in &bindings {
                        ctx.add_local(name.clone(), *ty, mutability);
                    }

                    // 5. Generate payload extraction stmts through the same owner
                    // used by match arms, including multi-field array typing.
                    let binding_stmts =
                        self.build_pattern_binding_stmts(pattern, subject_idx, subject_ty, &bindings, ctx);

                    // 6. Lower then_block with bindings in scope
                    let mut then_block = Vec::new();
                    then_block.extend(binding_stmts);
                    then_block.extend(self.lower_block(&if_stmt.then_block, ctx)?);

                    // 7. Clean up bindings from scope
                    for (name, _) in &bindings {
                        ctx.local_map.remove(name);
                    }

                    // 8. Handle else block (elif branches + else)
                    let else_block = if let Some(eb) = &if_stmt.else_block {
                        Some(self.lower_block(eb, ctx)?)
                    } else {
                        None
                    };

                    let else_block = self.lower_elif_chain(&if_stmt.elif_branches, else_block, ctx)?;

                    let mut result = vec![store_stmt];
                    result.push(HirStmt::If {
                        condition,
                        then_block,
                        else_block,
                    });
                    Ok(result)
                } else {
                    // Regular if (no pattern)
                    let condition = self.lower_expr(&if_stmt.condition, ctx)?;
                    let then_block = self.lower_block(&if_stmt.then_block, ctx)?;

                    let else_block = if let Some(eb) = &if_stmt.else_block {
                        Some(self.lower_block(eb, ctx)?)
                    } else {
                        None
                    };

                    let else_block = self.lower_elif_chain(&if_stmt.elif_branches, else_block, ctx)?;

                    Ok(vec![HirStmt::If {
                        condition,
                        then_block,
                        else_block,
                    }])
                }
            }

            Node::While(while_stmt) => {
                let condition = self.lower_expr(&while_stmt.condition, ctx)?;
                let body = self.lower_block(&while_stmt.body, ctx)?;
                let invariants = self.lower_contract_clauses(&while_stmt.invariants, ctx)?;
                Ok(vec![HirStmt::While {
                    condition,
                    body,
                    simd_requested: while_stmt.simd_requested,
                    invariants,
                }])
            }

            Node::For(for_stmt) => {
                let iterable = self.lower_expr(&for_stmt.iterable, ctx)?;

                // Infer the element type from the iterable type
                // Handles: Arrays [T] → T, Strings → u8, Tuples → common type
                // Ranges and custom iterators fallback to i64
                let element_ty = self.module.types.get_iterable_element(iterable.ty).unwrap_or_else(|| {
                    // For range BuiltinCalls (rt_range / rt_range_inclusive),
                    // the element type is the integer type of the start/end args.
                    // Without this, loop vars get TypeId::ANY, which skips BoxInt
                    // in rt_value_to_string lowering, producing <value:0xN> in native.
                    if let crate::hir::HirExprKind::BuiltinCall { ref name, ref args } = iterable.kind {
                        if name == "rt_range" || name == "rt_range_inclusive" {
                            if let Some(start) = args.first() {
                                match start.ty {
                                    crate::hir::TypeId::I8
                                    | crate::hir::TypeId::I16
                                    | crate::hir::TypeId::I32
                                    | crate::hir::TypeId::I64
                                    | crate::hir::TypeId::U8
                                    | crate::hir::TypeId::U16
                                    | crate::hir::TypeId::U32
                                    | crate::hir::TypeId::U64 => return start.ty,
                                    _ => {}
                                }
                            }
                            return crate::hir::TypeId::I64;
                        }
                    }
                    crate::hir::TypeId::ANY
                });

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
                        pattern_local: Some(temp_idx),
                        iterable,
                        body: new_body,
                        simd_requested: for_stmt.simd_requested,
                        invariants,
                    }])
                } else {
                    // Simple pattern (single identifier)
                    let pattern = Self::extract_pattern_name(&for_stmt.pattern).unwrap_or_else(|| "item".to_string());

                    // Add the loop variable to the context BEFORE lowering the body
                    let pattern_idx = ctx.add_local(pattern.clone(), element_ty, Mutability::Immutable);

                    let body = self.lower_block(&for_stmt.body, ctx)?;
                    let invariants = self.lower_contract_clauses(&for_stmt.invariants, ctx)?;
                    Ok(vec![HirStmt::For {
                        pattern,
                        pattern_local: Some(pattern_idx),
                        iterable,
                        body,
                        simd_requested: for_stmt.simd_requested,
                        invariants,
                    }])
                }
            }

            Node::Loop(loop_stmt) => {
                let body = self.lower_block(&loop_stmt.body, ctx)?;
                Ok(vec![HirStmt::Loop {
                    body,
                    simd_requested: loop_stmt.simd_requested,
                }])
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
                if matches!(expr, Expr::String(_) | Expr::TypedString(_, _)) {
                    return Ok(vec![]);
                }
                if let Some(stmts) = self.try_lower_host_gpu_lane_statement(expr, ctx)? {
                    return Ok(stmts);
                }
                // Intercept BDD/SPipe calls at statement level so we can emit
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

            Node::Skip(skip_stmt) => {
                // Skip can be standalone (no-op) or block form (for test framework)
                match &skip_stmt.body {
                    SkipBody::Standalone => {
                        // Standalone skip is a no-op
                        Ok(vec![])
                    }
                    SkipBody::Block(block) => {
                        // Block form: lower the block contents
                        // This is used by the test framework to mark skipped test bodies
                        self.lower_block(block, ctx)
                    }
                }
            }

            Node::Function(_f) => {
                // Nested function definitions are ignored in native lowering for now.
                Ok(vec![])
            }

            // Module-level imports are resolved in module_pass.rs. Function-scope
            // imports still need to materialize their symbols before subsequent
            // statements are lowered, then emit no runtime statement.
            Node::UseStmt(use_stmt) => {
                self.load_imported_types(&use_stmt.path, &use_stmt.target)?;
                Ok(vec![])
            }
            Node::MultiUse(_)
            | Node::CommonUseStmt(_)
            | Node::ExportUseStmt(_)
            | Node::StructuredExportStmt(_)
            | Node::AutoImportStmt(_) => Ok(vec![]),

            // Guard statement: ? condition -> result
            // Desugars to: if condition: return result
            Node::Guard(guard_stmt) => {
                let result_hir = self.lower_expr(&guard_stmt.result, ctx)?;

                match &guard_stmt.condition {
                    Some(cond) => {
                        // ? condition -> result
                        let cond_hir = self.lower_expr(cond, ctx)?;
                        Ok(vec![HirStmt::If {
                            condition: cond_hir,
                            then_block: vec![HirStmt::Return(Some(result_hir))],
                            else_block: None,
                        }])
                    }
                    None => {
                        // ? else -> result (unconditional early return)
                        Ok(vec![HirStmt::Return(Some(result_hir))])
                    }
                }
            }

            // Defer statement: defer: body or defer expr
            // Note: Full implementation requires scope tracking for LIFO execution at exit points.
            // For now, we add the HIR variant and will implement full codegen in Phase 2.
            Node::Defer(defer_stmt) => {
                let body_stmts = match &defer_stmt.body {
                    simple_parser::ast::DeferBody::Expr(e) => {
                        vec![HirStmt::Expr(self.lower_expr(e, ctx)?)]
                    }
                    simple_parser::ast::DeferBody::Block(b) => self.lower_block(b, ctx)?,
                };
                Ok(vec![HirStmt::Defer { body: body_stmts }])
            }

            Node::ErrDefer(errdefer_stmt) => {
                let body_stmts = match &errdefer_stmt.body {
                    simple_parser::ast::DeferBody::Expr(e) => {
                        vec![HirStmt::Expr(self.lower_expr(e, ctx)?)]
                    }
                    simple_parser::ast::DeferBody::Block(b) => self.lower_block(b, ctx)?,
                };
                // Reuse HirStmt::Defer for now — errdefer semantics (error-conditional)
                // will be distinguished in MIR lowering phase.
                Ok(vec![HirStmt::Defer { body: body_stmts }])
            }

            // With statement: with resource as name: body
            // Desugars to: __enter__/__exit__ protocol
            Node::With(with_stmt) => {
                let resource_hir = self.lower_expr(&with_stmt.resource, ctx)?;
                let resource_ty = resource_hir.ty;

                // Create temp for resource
                let temp_idx = ctx.locals.len();
                ctx.add_local("$with_resource".to_string(), resource_ty, Mutability::Immutable);

                // Call __enter__
                let enter_call = HirExpr {
                    kind: HirExprKind::MethodCall {
                        receiver: Box::new(HirExpr {
                            kind: HirExprKind::Local(temp_idx),
                            ty: resource_ty,
                        }),
                        method: "__enter__".to_string(),
                        args: vec![],
                        dispatch: DispatchMode::Dynamic,
                    },
                    ty: resource_ty, // __enter__ returns self or similar type
                };

                let mut stmts = vec![HirStmt::Let {
                    local_index: temp_idx,
                    ty: resource_ty,
                    value: Some(resource_hir),
                }];

                // Optional binding: with resource as name
                if let Some(name) = &with_stmt.name {
                    let name_idx = ctx.locals.len();
                    ctx.add_local(name.clone(), resource_ty, Mutability::Immutable);
                    stmts.push(HirStmt::Let {
                        local_index: name_idx,
                        ty: resource_ty,
                        value: Some(enter_call),
                    });
                } else {
                    // No binding, just call __enter__ for side effects
                    stmts.push(HirStmt::Expr(enter_call));
                }

                // Lower body
                let mut body_stmts = self.lower_block(&with_stmt.body, ctx)?;

                // Call __exit__(None) - pass None for exception (no exception handling yet)
                let exit_call = HirExpr {
                    kind: HirExprKind::MethodCall {
                        receiver: Box::new(HirExpr {
                            kind: HirExprKind::Local(temp_idx),
                            ty: resource_ty,
                        }),
                        method: "__exit__".to_string(),
                        args: vec![HirExpr {
                            kind: HirExprKind::Nil,
                            ty: TypeId::NIL,
                        }],
                        dispatch: DispatchMode::Dynamic,
                    },
                    ty: TypeId::VOID,
                };
                body_stmts.push(HirStmt::Expr(exit_call));

                stmts.extend(body_stmts);
                Ok(stmts)
            }

            Node::InlineAsm(asm_stmt) => {
                if asm_stmt.constraints.is_empty() && asm_stmt.target_match.is_empty() && asm_stmt.clobbers.is_empty() {
                    Ok(vec![HirStmt::InlineAsm {
                        instructions: asm_stmt.instructions.clone(),
                        volatile: asm_stmt.volatile,
                    }])
                } else {
                    if std::env::var("SIMPLE_DEBUG_ASM").as_deref() == Ok("1") {
                        eprintln!(
                            "[asm] skipping operand-bound or target-matched asm block at {:?}",
                            asm_stmt.span
                        );
                    }
                    Ok(vec![])
                }
            }

            // Context statement: context obj: body
            // Requires expression-level context tracking - mark as unsupported for native codegen
            Node::Context(_) if !self.lenient_types => Err(LowerError::Unsupported(
                "Context statements require interpreter mode. Native codegen support is planned.".to_string(),
            )),

            Node::Extern(e) => {
                let ret_ty = self.resolve_type_opt(&e.return_type)?;
                self.globals.insert(e.name.clone(), ret_ty);
                self.extern_fn_names.insert(e.name.clone());
                Ok(vec![])
            }

            Node::ExternClass(ec) => {
                let type_id = self.module.types.register_named(
                    ec.name.clone(),
                    crate::hir::types::HirType::ExternClass { name: ec.name.clone() },
                );
                self.globals.insert(ec.name.clone(), type_id);
                Ok(vec![])
            }

            // Type definitions that legitimately appear inside function bodies
            // in spec/test code (e.g. `class Point:` defined inside an `it`
            // block). These are hoisted to module scope by
            // `nested_def_hoist::module_with_hoisted_defs` before HIR lowering
            // begins, so by the time we reach the body the definition is
            // already registered. Emit no statement here.
            Node::Class(_)
            | Node::Struct(_)
            | Node::Enum(_)
            | Node::Trait(_)
            | Node::Impl(_)
            | Node::Mixin(_)
            | Node::TypeAlias(_)
            | Node::Extern(_)
            | Node::ExternClass(_)
            | Node::ClassAlias(_) => Ok(vec![]),

            // Other module-level definitions that have no in-body lowering.
            Node::Function(_)
            | Node::InterfaceBinding(_)
            | Node::Actor(_)
            | Node::FunctionAlias(_)
            | Node::Const(_)
            | Node::Static(_)
            | Node::LeanBlock(_)
            | Node::Macro(_)
            | Node::Unit(_)
            | Node::UnitFamily(_)
            | Node::CompoundUnit(_)
            | Node::HandlePool(_)
            | Node::LiteralFunction(_)
            | Node::ModDecl(_)
            | Node::RequiresCapabilities(_)
            | Node::AopAdvice(_)
            | Node::DiBinding(_)
            | Node::ArchitectureRule(_)
            | Node::MockDecl(_)
                if !self.lenient_types =>
            {
                Err(LowerError::Unsupported(format!(
                    "Definition type {:?} cannot appear as a statement in function body",
                    node
                )))
            }

            Node::Bitfield(bf) => {
                self.register_bitfield(bf)?;
                Ok(vec![])
            }

            // In lenient mode, skip unsupported/definition nodes as no-ops
            _ => Ok(vec![]),
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

    /// Build payload-extraction `Let` statements for enum pattern bindings in a
    /// match arm. Shared by statement-position (`lower_match_arms_stmt`) and
    /// expression-position (`lower_match_arms`) match lowering — the latter
    /// previously emitted NO extraction, leaving payload bindings nil in
    /// compiled code. Or-patterns (`case Copy(x) | Move(x)`) are normalized to
    /// their first alternative: every alternative must bind the same names,
    /// the same invariant `collect_pattern_bindings` relies on.
    pub(crate) fn build_pattern_binding_stmts(
        &mut self,
        arm_pattern: &Pattern,
        subject_idx: usize,
        subject_ty: TypeId,
        bindings: &[(String, TypeId)],
        ctx: &mut FunctionContext,
    ) -> Vec<HirStmt> {
        let binding_pattern: &Pattern = match arm_pattern {
            Pattern::Or(alternatives) => alternatives.first().unwrap_or(arm_pattern),
            other => other,
        };
        let mut binding_stmts = Vec::new();
        if let Pattern::Identifier(name) | Pattern::MutIdentifier(name) = binding_pattern {
            if bindings.iter().any(|(binding, _)| binding == name) {
                let Some(&local_index) = ctx.local_map.get(name) else {
                    return binding_stmts;
                };
                binding_stmts.push(HirStmt::Let {
                    local_index,
                    ty: subject_ty,
                    value: Some(HirExpr {
                        kind: HirExprKind::Local(subject_idx),
                        ty: subject_ty,
                    }),
                });
            }
            return binding_stmts;
        }
        if let Pattern::Enum {
            payload: Some(payload_patterns),
            variant: enum_variant,
            name: enum_name,
            ..
        } = binding_pattern
        {
            // Build a map from binding name to its resolved type
            // (computed by extract_pattern_bindings using enum variant field types)
            let binding_type_map: std::collections::HashMap<String, TypeId> = bindings.iter().cloned().collect();
            // Multi-field enum payloads are represented by a runtime array. Keep
            // that representation in HIR so MIR uses rt_array_get with a raw
            // integer index instead of the opaque rt_index_get dispatcher.
            let payload_array_ty = (payload_patterns.len() > 1).then(|| {
                self.module.types.register(HirType::Array {
                    element: TypeId::ANY,
                    size: Some(payload_patterns.len()),
                })
            });

            // Detect positional class/struct pattern: Pattern::Enum{name:"_", variant:"ClassName"}
            // over a class instance. The parser emits class-name patterns this way because it
            // cannot distinguish enum variants from class names at parse time.
            // For these, we use FieldAccess (positional field index) instead of rt_enum_payload.
            //
            // This heuristic must only fire for the *unqualified* form (`name == "_"`).
            // A qualified pattern like `EnumType.Variant(pe)` carries the real enum type
            // name and is unambiguously an enum variant — even when the variant name
            // happens to collide with a struct/class type of the same name (e.g.
            // `enum StmtKind: Expr(Expr)` matched as `case StmtKind.Expr(pe)`). Without
            // this guard, the variant-name lookup below finds the struct `Expr` and
            // mis-lowers the payload binding as a struct FieldAccess at offset 0 (reading
            // the enum header) instead of `rt_enum_payload`, producing a corrupt payload
            // pointer that SIGSEGVs on first field access. See
            // doc/08_tracking/bug/stage4_codegen_compact_form_hazards_2026-07-02.md.
            let class_struct_fields: Option<Vec<(String, TypeId)>> = if enum_name == "_" {
                self.module.types.lookup(enum_variant.as_str()).and_then(|tid| {
                    if let Some(HirType::Struct { fields, .. }) = self.module.types.get(tid) {
                        Some(fields.clone())
                    } else {
                        None
                    }
                })
            } else {
                None
            };

            for (i, p) in payload_patterns.iter().enumerate() {
                if let Pattern::Identifier(name) | Pattern::MutIdentifier(name) = p {
                    if let Some(local_idx) = ctx.local_map.get(name) {
                        let local_idx = *local_idx;
                        // Use the binding's resolved type (from enum variant definition)
                        // instead of ANY, so MIR lowering can insert proper unboxing
                        let binding_ty = binding_type_map.get(name).copied().unwrap_or(TypeId::ANY);

                        let value = if let Some(ref struct_fields) = class_struct_fields {
                            // Positional class/struct pattern: bind payload[i] to field i
                            // in declaration order via FieldAccess (byte-offset load).
                            //
                            // Class/struct instances in the compiled path are allocated
                            // via rt_alloc as plain flat memory with 8-byte-aligned fields
                            // at sequential offsets 0, 8, 16, … — NOT as RuntimeObjects.
                            // FieldAccess { field_index: i } lowers to FieldGet with
                            // byte_offset = i * 8, which is the correct layout.
                            //
                            // Use the struct's own field type for the expression so that
                            // the MIR lowering/codegen applies the right load width and
                            // avoids spurious boxing/unboxing.  The Let ty is set to the
                            // same field type (not ANY) so that downstream type consumers
                            // (e.g. string interpolation) know the value's true type.
                            //
                            // IMPORTANT: the local was added by `extract_pattern_bindings`
                            // with type ANY (because that helper only resolves enum variant
                            // field types, not class fields).  The MIR lowering reads
                            // `local.ty` (not `HirStmt::Let.ty`) to determine
                            // effective_declared_ty, so we must patch the local's type now
                            // to match the concrete field type, otherwise the MIR Store
                            // uses ANY and the value is mis-formatted at runtime.
                            let field_ty = struct_fields.get(i).map(|(_, ty)| *ty).unwrap_or(TypeId::ANY);
                            // Patch the local's type to the concrete field type.
                            if field_ty != TypeId::ANY {
                                if let Some(local) = ctx.locals.get_mut(local_idx) {
                                    local.ty = field_ty;
                                }
                            }
                            HirExpr {
                                kind: HirExprKind::FieldAccess {
                                    receiver: Box::new(HirExpr {
                                        kind: HirExprKind::Local(subject_idx),
                                        ty: subject_ty,
                                    }),
                                    field_index: i,
                                },
                                ty: field_ty,
                            }
                        } else {
                            // Enum variant payload extraction (original path).
                            // Extract payload from enum subject, then bind to locals.
                            // For multi-field variants, `rt_enum_payload` returns the
                            // wrapper *array* (heap pointer) — its type is opaque (ANY),
                            // not `binding_ty`. Otherwise `lower_builtin_call_expr` would
                            // see the binding's scalar type, apply `UnboxInt` to the
                            // heap pointer, and produce garbage. See
                            // doc/08_tracking/bug/enum_field_i64_zero_destructure_2026-04-28.md.
                            let payload_expr_ty = payload_array_ty.unwrap_or(binding_ty);
                            let payload_expr = HirExpr {
                                kind: HirExprKind::BuiltinCall {
                                    name: "rt_enum_payload".to_string(),
                                    args: vec![HirExpr {
                                        kind: HirExprKind::Local(subject_idx),
                                        ty: subject_ty,
                                    }],
                                },
                                ty: payload_expr_ty,
                            };

                            if payload_patterns.len() == 1 {
                                payload_expr
                            } else {
                                // Multi-field: index into tuple payload
                                HirExpr {
                                    kind: HirExprKind::Index {
                                        receiver: Box::new(payload_expr),
                                        index: Box::new(HirExpr {
                                            kind: HirExprKind::Integer(i as i64),
                                            ty: TypeId::I64,
                                        }),
                                    },
                                    ty: binding_ty,
                                }
                            }
                        };

                        // Use the value's own type for the Let declaration.
                        // For class patterns, value.ty is the struct's field type (e.g.
                        // TypeId::I64), NOT the binding_type_map entry (which is ANY for
                        // class patterns since collect_pattern_bindings only resolves enum
                        // variant field types). Using the value type ensures the MIR Store
                        // and subsequent uses see the correct concrete type rather than ANY,
                        // preventing misformatting (e.g. i64 field printed as float zero).
                        let let_ty = if class_struct_fields.is_some() {
                            value.ty
                        } else {
                            binding_ty
                        };
                        binding_stmts.push(HirStmt::Let {
                            local_index: local_idx,
                            ty: let_ty,
                            value: Some(value),
                        });
                    }
                } else if let Pattern::Enum {
                    name: nested_enum_name,
                    variant: nested_variant_name,
                    payload: Some(nested_patterns),
                } = p
                {
                    // Nested struct pattern inside an enum payload:
                    // `case Shape.Circle(Point(x, y)):`. The parser cannot
                    // distinguish an enum-variant pattern from a struct
                    // pattern written with call syntax at parse time, so
                    // `Point(x, y)` parses as `Pattern::Enum { name: "_",
                    // variant: "Point", payload: Some([Identifier("x"),
                    // Identifier("y")]) }` (see parser_patterns.rs) — the same
                    // ambiguity already handled for *top-level* arm patterns
                    // via `class_struct_fields` above. Until now this nested
                    // position had no handling at all — only the plain
                    // `Identifier`/`MutIdentifier` case above emitted a
                    // binding statement. `collect_pattern_bindings` DOES
                    // recurse into nested `Pattern::Enum` payload patterns and
                    // registers locals for `x`/`y`, but with no initializer
                    // emitted here those locals kept whatever zeroed value
                    // was already on the stack — the arm was selected
                    // correctly but bound `x = 0, y = 0`. See
                    // doc/08_tracking/bug/seed_interp_nested_struct_pattern_in_enum_payload_binds_zeros_2026-07-16.md.
                    let struct_info = (nested_enum_name == "_")
                        .then(|| self.module.types.lookup(nested_variant_name))
                        .flatten()
                        .and_then(|tid| match self.module.types.get(tid) {
                            Some(HirType::Struct { fields, .. }) => Some((tid, fields.clone())),
                            _ => None,
                        });
                    if let Some((struct_ty, struct_fields)) = struct_info {
                        // Extract this payload slot (same rt_enum_payload
                        // call as the Identifier case above, indexed into the
                        // multi-field wrapper array when the outer variant
                        // carries more than one payload item), but typed as
                        // the nested struct so FieldAccess below reads the
                        // struct's own sequential 8-byte-per-field layout
                        // instead of being (un)boxed as a scalar.
                        let base_payload_expr = HirExpr {
                            kind: HirExprKind::BuiltinCall {
                                name: "rt_enum_payload".to_string(),
                                args: vec![HirExpr {
                                    kind: HirExprKind::Local(subject_idx),
                                    ty: subject_ty,
                                }],
                            },
                            ty: if payload_patterns.len() == 1 {
                                struct_ty
                            } else {
                                payload_array_ty.unwrap_or(TypeId::ANY)
                            },
                        };
                        let struct_payload_expr = if payload_patterns.len() == 1 {
                            base_payload_expr
                        } else {
                            HirExpr {
                                kind: HirExprKind::Index {
                                    receiver: Box::new(base_payload_expr),
                                    index: Box::new(HirExpr {
                                        kind: HirExprKind::Integer(i as i64),
                                        ty: TypeId::I64,
                                    }),
                                },
                                ty: struct_ty,
                            }
                        };

                        // Struct fields are matched positionally (`Point(x, y)`
                        // binds x -> field 0, y -> field 1 in declaration
                        // order) — the parser discards field names even for
                        // the named-field spelling `Point(x: a, y: b)`, so
                        // there is no name to look up here, only position.
                        for (field_index, field_pattern) in nested_patterns.iter().enumerate() {
                            let (Pattern::Identifier(bound_name) | Pattern::MutIdentifier(bound_name)) =
                                field_pattern
                            else {
                                continue;
                            };
                            let Some(&local_idx) = ctx.local_map.get(bound_name) else {
                                continue;
                            };
                            let Some(&(_, field_ty)) = struct_fields.get(field_index) else {
                                continue;
                            };
                            if field_ty != TypeId::ANY {
                                if let Some(local) = ctx.locals.get_mut(local_idx) {
                                    local.ty = field_ty;
                                }
                            }
                            let value = HirExpr {
                                kind: HirExprKind::FieldAccess {
                                    receiver: Box::new(struct_payload_expr.clone()),
                                    field_index,
                                },
                                ty: field_ty,
                            };
                            binding_stmts.push(HirStmt::Let {
                                local_index: local_idx,
                                ty: field_ty,
                                value: Some(value),
                            });
                        }
                    }
                }
            }
        }
        binding_stmts
    }

    pub(crate) fn lower_match_guard(
        &mut self,
        condition: HirExpr,
        guard: Option<&Expr>,
        mut binding_stmts: Vec<HirStmt>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<(HirExpr, Vec<HirStmt>)> {
        let Some(guard) = guard else {
            return Ok((condition, binding_stmts));
        };
        let guard_hir = self.lower_expr(guard, ctx)?;
        if binding_stmts.is_empty() {
            return Ok((
                HirExpr {
                    kind: HirExprKind::Binary {
                        op: BinOp::And,
                        left: Box::new(condition),
                        right: Box::new(guard_hir),
                    },
                    ty: TypeId::BOOL,
                },
                binding_stmts,
            ));
        }

        binding_stmts.push(HirStmt::Expr(guard_hir));
        let guarded_condition = HirExpr {
            kind: HirExprKind::If {
                condition: Box::new(condition),
                then_branch: Box::new(HirExpr {
                    kind: HirExprKind::Block(binding_stmts),
                    ty: TypeId::BOOL,
                }),
                else_branch: Some(Box::new(HirExpr {
                    kind: HirExprKind::Bool(false),
                    ty: TypeId::BOOL,
                })),
            },
            ty: TypeId::BOOL,
        };
        Ok((guarded_condition, Vec::new()))
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
        if matches!(&arm.pattern, Pattern::Wildcard) {
            return self.lower_block(&arm.body, ctx);
        }

        // Generate the condition for this pattern
        let condition = self.lower_pattern_condition_stmt(subject_idx, subject_ty, &arm.pattern, ctx)?;

        // Extract pattern bindings and add them to context
        // This needs to happen after pattern condition but before guard/body
        let bindings = self.extract_pattern_bindings(&arm.pattern, subject_ty);
        let previous_bindings = self.register_match_bindings(&arm.pattern, &bindings, ctx);

        // Generate payload extraction statements for enum bindings (shared with
        // expression-position match arm lowering in expr/control.rs).
        let binding_stmts = self.build_pattern_binding_stmts(&arm.pattern, subject_idx, subject_ty, &bindings, ctx);

        let (final_condition, binding_stmts) =
            self.lower_match_guard(condition, arm.guard.as_ref(), binding_stmts, ctx)?;

        // Lower the arm body with bindings in scope
        let mut then_block = Vec::new();
        then_block.extend(binding_stmts);
        then_block.extend(self.lower_block(&arm.body, ctx)?);

        // Restore context (remove pattern bindings from name scope only)
        // Keep locals in ctx.locals so they get proper indices in the final function.
        // Truncating would cause local_index references in HIR stmts to be out of bounds.
        self.restore_match_bindings(previous_bindings, ctx);

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

    /// Generate the branch condition for an `if val` / `if var` (and their
    /// `elif` forms) binding.
    ///
    /// A plain-identifier binding (`if val x = opt:`) is a nil/Some check, not
    /// an unconditional match: it must mirror the pure-Simple parser desugar
    /// `val x = EXPR; if x != nil: ...`. The shared
    /// [`Self::lower_pattern_condition_stmt`] returns `Bool(true)` for a plain
    /// identifier — correct for a `match` catch-all arm, but wrong here (it made
    /// `if val x = none_option:` always take the then-branch and bind nil).
    /// Constructor patterns (`Some(x)`, `Ok(v)`, …) still go through the shared
    /// pattern-condition logic (rt_is_some / discriminant checks).
    fn if_let_pattern_condition(
        &mut self,
        subject_idx: usize,
        subject_ty: TypeId,
        pattern: &Pattern,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        if matches!(pattern, Pattern::Identifier(_) | Pattern::MutIdentifier(_)) {
            return Ok(HirExpr {
                kind: HirExprKind::Binary {
                    op: BinOp::NotEq,
                    left: Box::new(HirExpr {
                        kind: HirExprKind::Local(subject_idx),
                        ty: subject_ty,
                    }),
                    right: Box::new(HirExpr {
                        kind: HirExprKind::Nil,
                        ty: TypeId::NIL,
                    }),
                },
                ty: TypeId::BOOL,
            });
        }
        self.lower_pattern_condition_stmt(subject_idx, subject_ty, pattern, ctx)
    }

    /// Generate a condition expression for pattern matching
    pub(crate) fn lower_pattern_condition_stmt(
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
                if self.subject_enum_has_variant(subject_ty, name) {
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
            Pattern::MutIdentifier(_) | Pattern::MoveIdentifier(_) | Pattern::Rest => Ok(HirExpr {
                kind: HirExprKind::Bool(true),
                ty: TypeId::BOOL,
            }),
            Pattern::Typed { pattern, .. } => self.lower_pattern_condition_stmt(subject_idx, subject_ty, pattern, ctx),
            Pattern::Tuple(_elements) => Ok(HirExpr {
                kind: HirExprKind::Bool(true),
                ty: TypeId::BOOL,
            }),
            Pattern::Array(_elements) => Ok(HirExpr {
                kind: HirExprKind::Bool(true),
                ty: TypeId::BOOL,
            }),
            Pattern::Struct { .. } => Ok(HirExpr {
                kind: HirExprKind::Bool(true),
                ty: TypeId::BOOL,
            }),
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

                // Positional class/struct pattern: `case ClassName(a, b, c)` where the
                // parser emits Pattern::Enum{name:"_", variant:"ClassName", ...} because
                // it cannot distinguish enum variants from class names at parse time.
                // When `variant` resolves to a known Struct (class) type the discriminant
                // check must NOT fire — it would call rt_enum_check_discriminant on an
                // object pointer and always return false (silent no-match).
                // The type system already guarantees the object is of that class at the
                // call site, so the condition is always true unless the subject enum
                // itself owns this variant name.
                let subject_enum_owns_variant = matches!(
                    self.module.types.get(subject_ty),
                    Some(HirType::Enum { variants, .. })
                        if variants.iter().any(|(name, _)| name == variant)
                );
                let is_class_pattern = !subject_enum_owns_variant
                    && self.module.types.lookup(variant.as_str()).map_or(false, |tid| {
                        matches!(self.module.types.get(tid), Some(HirType::Struct { .. }))
                    });
                if is_class_pattern {
                    return Ok(HirExpr {
                        kind: HirExprKind::Bool(true),
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
            // Fallback: treat unsupported patterns as a tautology so lowering can proceed.
            // This keeps the pipeline moving for complex patterns not yet handled here.
            _ => Ok(HirExpr {
                kind: HirExprKind::Bool(true),
                ty: TypeId::BOOL,
            }),
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

    /// Try to lower a statement-position host/GPU lane marker.
    /// Returns Some(stmts) only for `target.later(...) gpu|host \:` shape.
    ///
    /// Expression-position marker calls remain regular calls for now.
    fn try_lower_host_gpu_lane_statement(
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

        let lane_code = match name {
            "host" => 1,
            "gpu" => 2,
            _ => return Ok(None),
        };
        if args.len() != 2 || !matches!(args.last().map(|arg| &arg.value), Some(Expr::Lambda { .. })) {
            return Ok(None);
        }

        let payload_size = match &args[0].value {
            Expr::MethodCall {
                method,
                args: later_args,
                ..
            } if method == "later" => Self::host_gpu_lane_payload_size(later_args),
            _ => return Ok(None),
        };

        let mut stmts = Vec::new();
        stmts.push(HirStmt::Expr(self.lower_expr(&args[0].value, ctx)?));

        stmts.push(Self::host_gpu_lane_event_stmt(lane_code, 1));
        if lane_code == 2 {
            stmts.push(HirStmt::Expr(HirExpr {
                kind: HirExprKind::BuiltinCall {
                    name: "rt_host_gpu_queue_emit".to_string(),
                    args: vec![
                        Self::i64_hir(lane_code),
                        Self::i64_hir(1),
                        Self::i64_hir(payload_size),
                        Self::i64_hir(0),
                    ],
                },
                ty: TypeId::I64,
            }));
        }
        self.lower_bdd_body(&args[args.len() - 1].value, &mut stmts, ctx)?;
        stmts.push(Self::host_gpu_lane_event_stmt(lane_code, 2));

        Ok(Some(stmts))
    }

    fn host_gpu_lane_payload_size(later_args: &[ast::Argument]) -> i64 {
        for arg in later_args {
            let is_max_packet = arg.name.as_deref() == Some("max_packet") || arg.label.as_deref() == Some("max_packet");
            if is_max_packet {
                if let Expr::Integer(value) = &arg.value {
                    return (*value).max(0);
                }
            }
        }
        if later_args.len() == 1 {
            if let Expr::Integer(value) = &later_args[0].value {
                return (*value).max(0);
            }
        }
        0
    }

    fn host_gpu_lane_event_stmt(lane_code: i64, phase_code: i64) -> HirStmt {
        HirStmt::Expr(HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: "rt_host_gpu_lane_event".to_string(),
                args: vec![Self::i64_hir(lane_code), Self::i64_hir(phase_code)],
            },
            ty: TypeId::I64,
        })
    }

    fn i64_hir(value: i64) -> HirExpr {
        HirExpr {
            kind: HirExprKind::Integer(value),
            ty: TypeId::I64,
        }
    }

    /// Try to lower a BDD/SPipe call expression as a statement sequence.
    /// Returns Some(stmts) if the expression is a BDD call, None otherwise.
    ///
    /// Handles: describe, context, it, test, expect, before_each, after_each
    fn try_lower_bdd_statement(&mut self, expr: &Expr, ctx: &mut FunctionContext) -> LowerResult<Option<Vec<HirStmt>>> {
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
                    HirExpr {
                        kind: HirExprKind::String("unnamed".to_string()),
                        ty: TypeId::STRING,
                    }
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
                    HirExpr {
                        kind: HirExprKind::String("unnamed".to_string()),
                        ty: TypeId::STRING,
                    }
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
                        args: vec![HirExpr {
                            kind: HirExprKind::Integer(1),
                            ty: TypeId::I64,
                        }],
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
                if !args.is_empty() {
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

#[cfg(test)]
mod host_gpu_lane_statement_tests {
    use super::super::lower;
    use crate::hir::types::{HirExprKind, HirModule, HirStmt};
    use simple_parser::Parser;

    fn lower_source(source: &str) -> crate::hir::lower::LowerResult<HirModule> {
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        lower(&ast)
    }

    fn builtin_name(stmt: &HirStmt) -> Option<&str> {
        match stmt {
            HirStmt::Expr(expr) => match &expr.kind {
                HirExprKind::BuiltinCall { name, .. } => Some(name.as_str()),
                _ => None,
            },
            _ => None,
        }
    }

    fn builtin_args<'a>(stmt: &'a HirStmt, target_name: &str) -> Option<&'a [crate::hir::types::HirExpr]> {
        match stmt {
            HirStmt::Expr(expr) => match &expr.kind {
                HirExprKind::BuiltinCall { name, args } if name == target_name => Some(args.as_slice()),
                _ => None,
            },
            _ => None,
        }
    }

    #[test]
    fn lowers_statement_position_gpu_lane_to_queue_wrapped_body() {
        let module = lower_source(
            "class Target:\n    fn later(max_packet: i64):\n        pass\n\nfn run() -> i64:\n    val target = Target()\n    gpu(target.later(max_packet: 4096), \\:\n        val draw_ir_batch = 1\n    )\n    return 0\n",
        )
        .unwrap();

        let func = module
            .functions
            .iter()
            .find(|func| func.name == "run")
            .expect("run function should lower");
        let names: Vec<&str> = func.body.iter().filter_map(builtin_name).collect();

        assert_eq!(
            names,
            vec![
                "rt_host_gpu_lane_event",
                "rt_host_gpu_queue_emit",
                "rt_host_gpu_lane_event"
            ]
        );
        let queue_args = func
            .body
            .iter()
            .find_map(|stmt| builtin_args(stmt, "rt_host_gpu_queue_emit"))
            .expect("gpu lane should emit runtime queue packet");
        assert!(matches!(
            queue_args.get(2).map(|expr| &expr.kind),
            Some(HirExprKind::Integer(4096))
        ));
    }

    #[test]
    fn lowers_statement_position_host_lane_without_queue_emit() {
        let module = lower_source(
            "class Target:\n    fn later():\n        pass\n\nfn run() -> i64:\n    val target = Target()\n    host(target.later(), \\:\n        val semantic_owner = 1\n    )\n    return 0\n",
        )
        .unwrap();

        let func = module
            .functions
            .iter()
            .find(|func| func.name == "run")
            .expect("run function should lower");
        let names: Vec<&str> = func.body.iter().filter_map(builtin_name).collect();

        assert_eq!(names, vec!["rt_host_gpu_lane_event", "rt_host_gpu_lane_event"]);
    }
}

#[cfg(test)]
mod nested_struct_pattern_in_enum_payload_tests {
    use super::super::lower;
    use crate::hir::types::{HirExpr, HirExprKind, HirModule, HirStmt, LocalVar};
    use simple_parser::Parser;

    fn lower_source(source: &str) -> crate::hir::lower::LowerResult<HirModule> {
        let mut parser = Parser::new(source);
        let ast = parser.parse().expect("parse failed");
        lower(&ast)
    }

    /// Find the initializer expression of the first `Let` statement binding
    /// local `name`, recursing into `If` then/else blocks -- a `match`
    /// statement lowers to a chain of `If`s, one per arm, and the binding
    /// `Let`s for a matched arm's payload live inside that arm's `then_block`.
    fn find_let_value<'a>(stmts: &'a [HirStmt], locals: &[LocalVar], name: &str) -> Option<&'a HirExpr> {
        for stmt in stmts {
            match stmt {
                HirStmt::Let {
                    local_index, value, ..
                } => {
                    if locals.get(*local_index).map(|l| l.name.as_str()) == Some(name) {
                        if let Some(v) = value {
                            return Some(v);
                        }
                    }
                }
                HirStmt::If {
                    then_block, else_block, ..
                } => {
                    if let Some(v) = find_let_value(then_block, locals, name) {
                        return Some(v);
                    }
                    if let Some(else_b) = else_block {
                        if let Some(v) = find_let_value(else_b, locals, name) {
                            return Some(v);
                        }
                    }
                }
                _ => {}
            }
        }
        None
    }

    // Bug fix 14922f8e3cb (build_pattern_binding_stmts): a nested
    // struct-destructuring sub-pattern inside an enum payload
    // (`case Shape.Circle(Point(x, y)):`) had NO handling at all in the loop
    // over payload sub-patterns -- only a plain `Identifier`/`MutIdentifier`
    // sub-pattern emitted a binding `Let`. `collect_pattern_bindings`
    // (a separate pass) still registers locals for `x`/`y`, so the names
    // exist, but pre-fix no `Let` statement initializes them from the
    // payload at all -- they keep whatever zeroed value is already on the
    // stack. Reverting the fix removes the `else if let Pattern::Enum { .. }`
    // branch this test exercises, so `find_let_value` finds NO initializer
    // for `x`/`y` and this test fails outright (not merely a wrong value).
    // Exact repro source from
    // doc/08_tracking/bug/seed_interp_nested_struct_pattern_in_enum_payload_binds_zeros_2026-07-16.md.
    #[test]
    fn nested_struct_pattern_in_single_payload_binds_fields_via_field_access() {
        let module = lower_source(
            "struct Point:\n    x: i64\n    y: i64\n\nenum Shape:\n    Circle(Point)\n    Empty\n\nfn main() -> i64:\n    val s = Shape.Circle(Point(x: 3, y: 5))\n    match s:\n        case Shape.Circle(Point(x, y)): print(x * 10 + y)\n        case Shape.Empty: print(99)\n    return 0\n",
        )
        .expect("source should lower");

        let func = module
            .functions
            .iter()
            .find(|f| f.name == "main")
            .expect("main function should lower");

        let x_value = find_let_value(&func.body, &func.locals, "x")
            .expect("nested struct pattern must emit a Let binding for x (pre-fix: none emitted at all)");
        assert!(
            matches!(x_value.kind, HirExprKind::FieldAccess { field_index: 0, .. }),
            "x should bind via FieldAccess to field 0 of the nested Point struct, got {:?}",
            x_value.kind
        );

        let y_value = find_let_value(&func.body, &func.locals, "y")
            .expect("nested struct pattern must emit a Let binding for y (pre-fix: none emitted at all)");
        assert!(
            matches!(y_value.kind, HirExprKind::FieldAccess { field_index: 1, .. }),
            "y should bind via FieldAccess to field 1 of the nested Point struct, got {:?}",
            y_value.kind
        );
    }

    // Edge case: nested struct pattern as the SECOND item of a multi-field
    // outer variant (`CircleAt(id, Point)` matched as
    // `case Shape.CircleAt(id, Point(x, y))`). This exercises the
    // `payload_patterns.len() > 1` branch, which indexes into the wrapper
    // array (`rt_enum_payload(...)[i]`) before applying `FieldAccess` -- an
    // off-by-one in that index would silently read the wrong payload slot.
    #[test]
    fn nested_struct_pattern_in_multi_payload_indexes_correct_slot() {
        let module = lower_source(
            "struct Point:\n    x: i64\n    y: i64\n\nenum Shape:\n    CircleAt(id: i64, point: Point)\n    Empty\n\nfn main() -> i64:\n    val s = Shape.CircleAt(id: 7, point: Point(x: 3, y: 5))\n    match s:\n        case Shape.CircleAt(id, Point(x, y)): print(id * 100 + x * 10 + y)\n        case Shape.Empty: print(99)\n    return 0\n",
        )
        .expect("source should lower");

        let func = module
            .functions
            .iter()
            .find(|f| f.name == "main")
            .expect("main function should lower");

        let x_value = find_let_value(&func.body, &func.locals, "x")
            .expect("nested struct pattern (2nd payload slot) must emit a Let binding for x");
        match &x_value.kind {
            HirExprKind::FieldAccess { field_index, receiver } => {
                assert_eq!(*field_index, 0, "x is Point's field 0");
                match &receiver.kind {
                    HirExprKind::Index { index, .. } => {
                        assert!(
                            matches!(index.kind, HirExprKind::Integer(1)),
                            "the nested Point pattern is the 2nd (index 1) item of the outer \
                             variant's payload array, got index expr {:?}",
                            index.kind
                        );
                    }
                    other => panic!(
                        "expected the struct payload to be indexed out of the multi-field wrapper array, got receiver {:?}",
                        other
                    ),
                }
            }
            other => panic!("expected FieldAccess for x, got {:?}", other),
        }
    }
}

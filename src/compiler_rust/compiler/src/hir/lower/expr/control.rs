//! Control flow expression lowering
//!
//! This module contains expression lowering logic for control flow:
//! if expressions, lambda expressions, yield expressions, and match expressions.

use simple_parser::{self as ast, ast::Mutability, ast::Pattern, Expr, MatchArm};
use std::collections::HashSet;

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::LowerResult;
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    pub(super) fn result_like_payload_type(&self, ty: TypeId) -> Option<TypeId> {
        match self.module.types.get(ty) {
            Some(HirType::Enum { name, variants, .. }) if name == "Result" => {
                variants.iter().find_map(|(variant, payload)| {
                    if variant == "Ok" {
                        payload.as_ref().and_then(|fields| fields.first()).copied()
                    } else {
                        None
                    }
                })
            }
            Some(HirType::Enum { name, variants, .. }) if name == "Option" => {
                variants.iter().find_map(|(variant, payload)| {
                    if variant == "Some" {
                        payload.as_ref().and_then(|fields| fields.first()).copied()
                    } else {
                        None
                    }
                })
            }
            Some(HirType::Pointer { inner, .. }) => self.result_like_payload_type(*inner),
            _ => None,
        }
    }

    /// Lower an if expression to HIR
    ///
    /// Result type is taken from the then branch.
    /// Else branch is optional.
    pub(super) fn lower_if(
        &mut self,
        let_pattern: Option<&Pattern>,
        condition: &Expr,
        then_branch: &Expr,
        else_branch: Option<&Expr>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // `if val PAT = expr: a else: b` used as an EXPRESSION must thread the
        // pattern binding into the then-arm's scope, exactly like the statement
        // form (`Node::If` in stmt_lowering.rs). This arm previously discarded
        // `let_pattern` (it matched with `..` at the lower_expr call site), so the
        // bound name was never registered as a local. Under `lenient_types` the
        // unresolved name silently became `HirExprKind::Global`, which lowers to
        // `MirInst::GlobalLoad` and finally dies in LLVM codegen with
        // "llvm global load referenced undeclared symbol `<name>`".
        //
        // The tree-walking interpreter had the identical defect and was fixed
        // separately (see interpreter/expr/control.rs and
        // doc/08_tracking/bug/if_val_expression_form_binding_lost_2026-07-20.md);
        // the compiled HIR/MIR/LLVM path was left behind, which is why no
        // interpreter spec catches this.
        if let Some(pattern) = let_pattern {
            return self.lower_if_let_expr(pattern, condition, then_branch, else_branch, ctx);
        }
        let cond_hir = Box::new(self.lower_condition(condition, ctx)?);
        let then_hir = Box::new(self.lower_expr(then_branch, ctx)?);
        let else_hir = if let Some(eb) = else_branch {
            Some(Box::new(self.lower_expr(eb, ctx)?))
        } else {
            None
        };

        let ty = then_hir.ty;

        Ok(HirExpr {
            kind: HirExprKind::If {
                condition: cond_hir,
                then_branch: then_hir,
                else_branch: else_hir,
            },
            ty,
        })
    }

    /// Lower `if val PAT = subject: then else: else` in EXPRESSION position.
    ///
    /// Mirrors the statement lowering in `stmt_lowering.rs` (`Node::If` with a
    /// `let_pattern`), but produces a value instead of a statement list. The
    /// subject store and the pattern payload extraction are emitted as HIR
    /// statements wrapped in `HirExprKind::Block`, the same shape match-arm
    /// bindings use (`lower_match_arms`).
    fn lower_if_let_expr(
        &mut self,
        pattern: &Pattern,
        condition: &Expr,
        then_branch: &Expr,
        else_branch: Option<&Expr>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // `if val v = expr.?:` parses `expr.?` as `Expr::ExistsCheck` (a bool
        // presence check). Combined with a `val` binding the intent is "bind v to
        // the unwrapped value", so unwrap one ExistsCheck layer to keep the
        // subject Option-typed. Same reasoning as the statement path.
        let condition_expr = match condition {
            Expr::ExistsCheck(inner) => inner.as_ref(),
            other => other,
        };
        let subject_hir = self.lower_expr(condition_expr, ctx)?;
        let subject_ty = subject_hir.ty;

        // Temp local holding the subject value, so the pattern condition and the
        // payload extraction both read it without re-evaluating the expression.
        let subject_idx = ctx.locals.len();
        ctx.add_local("$if_let_subject".to_string(), subject_ty, Mutability::Immutable);
        let store_stmt = HirStmt::Let {
            local_index: subject_idx,
            ty: subject_ty,
            value: Some(subject_hir),
        };

        // The expression-form `if val` reaches here without a span of its own
        // (`lower_if_let_expr` takes the pattern and condition, not the
        // statement), so CLEAR rather than leave the previous arm's span in
        // place -- a stale location is worse than none.
        self.current_pattern_span = None;
        let cond_hir = self.if_let_pattern_condition(subject_idx, subject_ty, pattern, ctx)?;

        // Register the bindings BEFORE lowering the then-branch: this is the step
        // whose absence caused the undeclared-global defect.
        let bindings = self.extract_pattern_bindings(pattern, subject_ty);
        let previous_bindings = self.register_match_bindings(pattern, &bindings, ctx);
        let binding_stmts = self.build_pattern_binding_stmts(pattern, subject_idx, subject_ty, &bindings, ctx);

        let then_hir = self.lower_expr(then_branch, ctx)?;
        let ty = then_hir.ty;
        let then_hir = if binding_stmts.is_empty() {
            then_hir
        } else {
            let mut stmts = binding_stmts;
            stmts.push(HirStmt::Expr(then_hir));
            HirExpr {
                kind: HirExprKind::Block(stmts),
                ty,
            }
        };

        // Bindings leave name scope, but the locals stay in `ctx.locals` so the
        // indices already baked into the HIR remain valid.
        self.restore_match_bindings(previous_bindings, ctx);

        let else_hir = if let Some(eb) = else_branch {
            Some(Box::new(self.lower_expr(eb, ctx)?))
        } else {
            None
        };

        let if_expr = HirExpr {
            kind: HirExprKind::If {
                condition: Box::new(cond_hir),
                then_branch: Box::new(then_hir),
                else_branch: else_hir,
            },
            ty,
        };

        // The subject store must run before the test, so the whole form becomes a
        // block whose value is the if-expression.
        Ok(HirExpr {
            kind: HirExprKind::Block(vec![store_stmt, HirStmt::Expr(if_expr)]),
            ty,
        })
    }

    /// Lower a lambda expression to HIR
    ///
    /// Captures variables based on capture_all flag:
    /// - true: captures all immutable variables from outer scope
    /// - false: only captures variables explicitly used in body
    ///
    /// Parameters default to I64 type if not explicitly typed.
    /// Result type is taken from the lambda body.
    pub(super) fn lower_lambda(
        &mut self,
        params: &[ast::LambdaParam],
        body: &Expr,
        capture_all: bool,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Track captured variables from outer scope
        let captures: Vec<usize> = if capture_all {
            // Capture all immutable variables from outer scope
            ctx.locals.iter().enumerate().map(|(i, _)| i).collect()
        } else {
            // Analyze body to determine which variables are actually used
            let used_vars = collect_used_identifiers(body);
            ctx.locals
                .iter()
                .enumerate()
                .filter(|(_, local)| used_vars.contains(&local.name))
                .map(|(i, _)| i)
                .collect()
        };

        // Collect parameter names and types
        let param_info: Vec<(String, TypeId)> = params
            .iter()
            .map(|p| {
                let ty = if let Some(ref t) = p.ty {
                    self.resolve_type(t).unwrap_or(TypeId::I64)
                } else {
                    TypeId::I64 // Default to I64 for untyped params
                };
                (p.name.clone(), ty)
            })
            .collect();

        let saved_locals_len = ctx.locals.len();
        let saved_local_map = ctx.local_map.clone();
        let mut param_local_indices = Vec::with_capacity(param_info.len());
        // Add lambda parameters to context as locals for body lowering
        for (name, ty) in &param_info {
            let local_index = ctx.add_local(name.clone(), *ty, simple_parser::ast::Mutability::Immutable);
            param_local_indices.push(local_index);
        }

        // Lower the lambda body with access to parameters
        let body_hir = Box::new(self.lower_expr(body, ctx)?);
        let body_ty = body_hir.ty;

        // Restore context; lambda-local variables must not leak to the outer function.
        ctx.locals.truncate(saved_locals_len);
        ctx.local_map = saved_local_map;

        Ok(HirExpr {
            kind: HirExprKind::Lambda {
                params: param_info,
                param_local_indices,
                body: body_hir,
                captures,
            },
            ty: body_ty,
        })
    }

    /// Lower a yield expression to HIR
    ///
    /// Used in generator functions.
    /// If no value is provided, yields Nil.
    pub(super) fn lower_yield(&mut self, value: Option<&Expr>, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        let value_hir = if let Some(v) = value {
            Box::new(self.lower_expr(v, ctx)?)
        } else {
            Box::new(HirExpr {
                kind: HirExprKind::Nil,
                ty: TypeId::NIL,
            })
        };
        let ty = value_hir.ty;
        Ok(HirExpr {
            kind: HirExprKind::Yield(value_hir),
            ty,
        })
    }

    /// Lower a spawn expression to HIR
    ///
    /// `spawn expr` lowers to ActorSpawn
    pub(super) fn lower_spawn(&mut self, expr: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        let body_hir = Box::new(self.lower_expr(expr, ctx)?);
        Ok(HirExpr {
            kind: HirExprKind::ActorSpawn { body: body_hir },
            ty: TypeId::I64, // Returns thread handle
        })
    }

    /// Lower a go expression to HIR
    ///
    /// Forms:
    /// - `go(x, y) \a, b: body` - pass args to params (no capture)
    /// - `go(x, y) \*: body` or `go(x, y) \: body` - capture specified vars or all
    /// - `go \*: body` or `go \: body` - capture all immutables
    pub(super) fn lower_go(
        &mut self,
        args: &[Expr],
        params: &[String],
        body: &Expr,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let has_params = !params.is_empty();
        let has_args = !args.is_empty();

        if has_params {
            // Args form with params: go(x, y) \a, b: body
            // Create a lambda with the parameters
            let lambda_params: Vec<ast::LambdaParam> = params
                .iter()
                .map(|name| ast::LambdaParam {
                    name: name.clone(),
                    ty: None,
                })
                .collect();

            let lambda_hir = self.lower_lambda(&lambda_params, body, false, ctx)?;

            // Lower the arguments
            let mut arg_hirs = Vec::new();
            for arg in args {
                arg_hirs.push(self.lower_expr(arg, ctx)?);
            }

            // Create a call to the lambda with the arguments
            let call_hir = HirExpr {
                kind: HirExprKind::Call {
                    func: Box::new(lambda_hir),
                    args: arg_hirs,
                },
                ty: TypeId::I64,
            };

            // Spawn the call
            Ok(HirExpr {
                kind: HirExprKind::ActorSpawn {
                    body: Box::new(call_hir),
                },
                ty: TypeId::I64, // Returns thread handle
            })
        } else {
            // Capture form: go(x, y) \*: or go \*:
            // Empty args means capture all
            let capture_all = !has_args;
            let lambda_params: Vec<ast::LambdaParam> = Vec::new();
            let lambda_hir = self.lower_lambda(&lambda_params, body, capture_all, ctx)?;

            // Spawn the lambda
            Ok(HirExpr {
                kind: HirExprKind::ActorSpawn {
                    body: Box::new(lambda_hir),
                },
                ty: TypeId::I64, // Returns thread handle
            })
        }
    }

    /// Lower a match expression to HIR
    ///
    /// Match expressions are lowered to a chain of If-Else expressions.
    /// Each arm becomes an If with:
    /// - Condition: pattern match check (equality for literals, Or for alternations)
    /// - Then: the arm body
    /// - Else: the next arm (or Nil if no more arms)
    pub(super) fn lower_match(
        &mut self,
        subject: &Expr,
        arms: &[MatchArm],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Lower the subject once and store in a local variable to avoid re-evaluation
        let subject_hir = self.lower_expr(subject, ctx)?;
        let subject_ty = subject_hir.ty;

        // Create a temporary local to hold the subject value
        let subject_idx = ctx.locals.len();
        ctx.add_local("$match_subject".to_string(), subject_ty, Mutability::Immutable);

        // Build the chain of If-Else expressions from the arms
        let if_chain = self.lower_match_arms(subject_idx, subject_ty, arms, ctx)?;
        let result_ty = if_chain.ty;

        // Wrap in LetIn to store the subject before evaluating the if-else chain
        Ok(HirExpr {
            kind: HirExprKind::LetIn {
                local_idx: subject_idx,
                value: Box::new(subject_hir),
                body: Box::new(if_chain),
            },
            ty: result_ty,
        })
    }

    /// Lower match arms to a chain of If-Else expressions
    fn lower_match_arms(
        &mut self,
        subject_idx: usize,
        subject_ty: TypeId,
        arms: &[MatchArm],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        if arms.is_empty() {
            // No more arms - return Nil
            return Ok(HirExpr {
                kind: HirExprKind::Nil,
                ty: TypeId::NIL,
            });
        }

        let arm = &arms[0];
        let remaining_arms = &arms[1..];

        // Check if this is a wildcard pattern (always matches)
        if matches!(&arm.pattern, Pattern::Wildcard) {
            return self.lower_match_arm_body(&arm.body, ctx);
        }

        // Generate the condition for this pattern
        self.current_pattern_span = Some((arm.span.line, arm.span.column));
        let condition = self.lower_pattern_condition(subject_idx, subject_ty, &arm.pattern, ctx)?;

        // Extract pattern bindings and add them to context
        // This needs to happen after pattern condition but before guard/body
        let bindings = self.extract_pattern_bindings(&arm.pattern, subject_ty);
        let previous_bindings = self.register_match_bindings(&arm.pattern, &bindings, ctx);

        // Generate payload extraction statements so enum payload bindings are
        // initialized before a guard or arm body reads them.
        let binding_stmts = self.build_pattern_binding_stmts(&arm.pattern, subject_idx, subject_ty, &bindings, ctx);

        let (final_condition, binding_stmts) =
            self.lower_match_guard(condition, arm.guard.as_ref(), binding_stmts, ctx)?;

        // Lower the arm body with bindings in scope
        let then_branch = self.lower_match_arm_body(&arm.body, ctx)?;
        let then_ty = then_branch.ty;
        let then_branch = if binding_stmts.is_empty() {
            then_branch
        } else {
            // Prepend the binding initializations, preserving the arm value as
            // the block result (same shape lower_do_block produces).
            let mut stmts = binding_stmts;
            stmts.push(crate::hir::HirStmt::Expr(then_branch));
            HirExpr {
                kind: HirExprKind::Block(stmts),
                ty: then_ty,
            }
        };

        // Restore context (remove pattern bindings from name scope only)
        // Keep locals in ctx.locals so they get proper indices in the final function.
        // Truncating would cause local_index references in HIR stmts to be out of bounds.
        self.restore_match_bindings(previous_bindings, ctx);

        // Recursively build the else branch from remaining arms
        let else_branch = self.lower_match_arms(subject_idx, subject_ty, remaining_arms, ctx)?;

        Ok(HirExpr {
            kind: HirExprKind::If {
                condition: Box::new(final_condition),
                then_branch: Box::new(then_branch),
                else_branch: Some(Box::new(else_branch)),
            },
            ty: then_ty,
        })
    }

    /// Generate a condition expression for pattern matching
    fn lower_pattern_condition(
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
            Pattern::Identifier(_) => self.lower_pattern_condition_stmt(subject_idx, subject_ty, pattern, ctx),
            Pattern::Literal(lit_expr) => {
                // Compare subject == literal
                let lit_hir = self.lower_expr(lit_expr, ctx)?;

                // Check if subject or literal is a string type - use rt_string_eq for string comparison
                // Also check CHAR and ANY since string indexing returns single-char strings
                // and the literal may be a string (e.g., char literals like '(' are strings)
                let is_string = subject_ty == TypeId::STRING
                    || subject_ty == TypeId::CHAR
                    || matches!(self.module.types.get(subject_ty), Some(HirType::String | HirType::Char))
                    || lit_hir.ty == TypeId::STRING
                    || lit_hir.ty == TypeId::CHAR
                    || (subject_ty == TypeId::ANY && matches!(lit_hir.kind, HirExprKind::String(_)));

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

                let mut result = self.lower_pattern_condition(subject_idx, subject_ty, &patterns[0], ctx)?;
                for p in &patterns[1..] {
                    let p_cond = self.lower_pattern_condition(subject_idx, subject_ty, p, ctx)?;
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
                // Warn-only, DEFAULT OFF. Expression-form twin of the statement
                // check in hir/lower/stmt_lowering.rs; reached for
                // `val x = match subj: case Some(v)`. See
                // hir/lower/option_pattern_shape_diag.rs.
                crate::hir::lower::option_pattern_shape_diag::report_if_never_option(
                    variant,
                    self.module.types.get(subject_ty),
                    "expression form",
                    crate::hir::lower::option_pattern_shape_diag::DiagLocation {
                        file: self.current_file.as_deref(),
                        function: self.current_function_name.as_deref(),
                        line: self.current_pattern_span.map(|(line, _)| line),
                        column: self.current_pattern_span.map(|(_, column)| column),
                    },
                );
                // Does the subject's own enum type declare this variant name?
                // This must be decided BEFORE the `Some`/`None` fast paths below:
                // a user-defined enum is free to name its variants `Some`/`None`
                // (`enum Opt: Some(x: i64); None`), and for such a subject the
                // optional-shaped `rt_is_some`/`rt_is_none` probes are wrong.
                // `rt_is_some` is "not the nil sentinel", so it returns TRUE for
                // *every* value of a real enum — including `Opt.None` — making
                // `case Some(x)` an irrefutable arm that then bound x = 3 (the
                // nil tag). Only the built-in `T?` optional representation, whose
                // subject type is a Pointer/Option rather than an Enum owning
                // these names, may take the fast paths.
                let subject_enum_owns_variant = matches!(
                    self.module.types.get(subject_ty),
                    Some(HirType::Enum { variants, .. })
                        if variants.iter().any(|(name, _)| name == variant)
                );

                // Special handling for None - check both nil and enum None
                if variant == "None" && !subject_enum_owns_variant {
                    return Ok(HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: "rt_is_none".to_string(),
                            args: vec![subject_ref],
                        },
                        ty: TypeId::BOOL,
                    });
                }
                // Special handling for Some - check not-none
                if variant == "Some" && !subject_enum_owns_variant {
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
                // call site, so the CLASS half of the test is always true — but the
                // FIELD half is not, and returning a bare `Bool(true)` here discarded
                // `payload` outright. See `class_pattern_condition`.
                let is_class_pattern = !subject_enum_owns_variant
                    && self.module.types.lookup(variant.as_str()).map_or(false, |tid| {
                        matches!(self.module.types.get(tid), Some(HirType::Struct { .. }))
                    });
                if is_class_pattern {
                    let payload = match pattern {
                        Pattern::Enum { payload, .. } => payload.as_ref(),
                        _ => None,
                    };
                    let variant = variant.clone();
                    return Ok(self.class_pattern_condition(&subject_ref, &variant, payload, ctx));
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

                let tag_test = HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: "rt_enum_check_discriminant".to_string(),
                        args: vec![subject_ref.clone(), expected_val],
                    },
                    ty: TypeId::BOOL,
                };

                // Test refutable payload sub-patterns too. Testing only the outer
                // tag made a nested variant sub-pattern irrefutable — see
                // `nested_payload_condition`.
                let nested = match pattern {
                    Pattern::Enum {
                        payload: Some(payload_patterns),
                        ..
                    } => self.nested_payload_condition(variant, &subject_ref, payload_patterns, ctx),
                    _ => None,
                };

                Ok(match nested {
                    None => tag_test,
                    Some(nested_test) => HirExpr {
                        kind: HirExprKind::Binary {
                            op: BinOp::And,
                            left: Box::new(tag_test),
                            right: Box::new(nested_test),
                        },
                        ty: TypeId::BOOL,
                    },
                })
            }
            Pattern::MutIdentifier(_) | Pattern::MoveIdentifier(_) | Pattern::Rest => Ok(HirExpr {
                kind: HirExprKind::Bool(true),
                ty: TypeId::BOOL,
            }),
            Pattern::Typed { pattern, .. } => self.lower_pattern_condition(subject_idx, subject_ty, pattern, ctx),
            // Kept in sync with the statement-form twin
            // `lower_pattern_condition_stmt` (hir/lower/stmt_lowering.rs): match
            // ARMS route through that one, this is the expression form.
            Pattern::Tuple(elements) => {
                Ok(self
                    .sequence_condition(&subject_ref, elements, false, ctx)
                    .unwrap_or(HirExpr {
                        kind: HirExprKind::Bool(true),
                        ty: TypeId::BOOL,
                    }))
            }
            Pattern::Array(elements) => {
                Ok(self
                    .sequence_condition(&subject_ref, elements, true, ctx)
                    .unwrap_or(HirExpr {
                        kind: HirExprKind::Bool(true),
                        ty: TypeId::BOOL,
                    }))
            }
            // Named-field spelling. Same rule as the positional twin above: the
            // class itself is fixed by the type system, the FIELD sub-patterns
            // are not, and this used to be an unconditional `Bool(true)`.
            Pattern::Struct { name, fields } => {
                let name = name.clone();
                let fields = fields.clone();
                Ok(self.named_struct_pattern_condition(&subject_ref, &name, &fields, ctx))
            }
        }
    }

    /// Is `variant` a genuine enum-variant name (as opposed to a class/struct
    /// name that the parser also spells as `Pattern::Enum`)?
    ///
    /// The parser cannot tell `Shape.Circle(..)` from `Point(x, y)` at parse
    /// time, so both arrive as `Pattern::Enum`. Only the former is refutable;
    /// emitting a discriminant check for a struct pattern would test an object
    /// pointer's enum header and never match.
    pub(crate) fn is_real_enum_variant_name(&self, variant: &str) -> bool {
        let resolves_to_struct = self.module.types.lookup(variant).map_or(false, |tid| {
            matches!(self.module.types.get(tid), Some(HirType::Struct { .. }))
        });
        if resolves_to_struct {
            return false;
        }
        self.module.types.iter().any(|(_, ty)| {
            matches!(ty, HirType::Enum { variants, .. }
                if variants.iter().any(|(v, _)| v == variant))
        })
    }

    /// Build the refutability test for an enum variant pattern's payload
    /// sub-patterns, or `None` when every sub-pattern is irrefutable.
    ///
    /// Historically `lower_pattern_condition` tested only the OUTER variant tag
    /// and discarded `payload`, so a nested variant sub-pattern such as
    /// `Const(MirConstValue.Str(name), _)` was treated as a wildcard: the arm
    /// matched no matter what the inner variant actually was, and the binder
    /// inside it read zero. The tree-walk interpreter recurses correctly
    /// (`interpreter_patterns.rs`), so no interpreter-run spec caught this.
    ///
    /// Scope: fully recursive over variant and literal sub-patterns, at any
    /// nesting depth. Tuple/array/struct sub-patterns in payload position are
    /// still treated as irrefutable and are tracked separately in the bug doc.
    pub(crate) fn nested_payload_condition(
        &mut self,
        outer_variant: &str,
        subject_ref: &HirExpr,
        payload_patterns: &[Pattern],
        ctx: &mut FunctionContext,
    ) -> Option<HirExpr> {
        let arity = payload_patterns.len();
        let mut combined: Option<HirExpr> = None;

        for (i, p) in payload_patterns.iter().enumerate() {
            let slot_expr = Self::payload_slot_expr(outer_variant, subject_ref, i, arity);
            let Some(test) = self.subpattern_condition(&slot_expr, p, ctx) else {
                continue;
            };
            combined = Some(match combined {
                None => test,
                Some(prev) => HirExpr {
                    kind: HirExprKind::Binary {
                        op: BinOp::And,
                        left: Box::new(prev),
                        right: Box::new(test),
                    },
                    ty: TypeId::BOOL,
                },
            });
        }

        combined
    }

    /// Expression that extracts payload slot `i` of an enum value.
    ///
    /// Mirrors the extraction in `build_pattern_binding_stmts`: a single-field
    /// variant's payload is the value itself; multi-field variants wrap it in
    /// an array. Condition and binding MUST agree on this shape or an arm is
    /// selected on one slot and bound from another.
    ///
    /// `outer_variant` selects the `Some` dual-representation guard. A `T?` has
    /// TWO runtime forms: a boxed `Some` enum (literal `Some(x)` construction,
    /// `.at()`) and the "raw migration form" — the bare payload, which is what
    /// a natively compiled `T?`-returning function produces. `rt_enum_payload`
    /// answers NIL (the integer 3) for the raw form, so a NON-identifier
    /// sub-pattern under `Some` (`Some((a, b))`, `Some([a, b])`,
    /// `Some(Point(x, y))`) read the nil sentinel and bound 3. The identifier
    /// path in `build_pattern_binding_stmts` already carried this guard; this
    /// is the same runtime branch, hoisted into the slot owner so the
    /// CONDITION side and every sub-pattern binder get it too:
    ///     if rt_enum_id(subj) >= 0: rt_enum_payload(subj) else: subj
    /// See §22 of
    /// doc/08_tracking/bug/option_pattern_accepted_on_non_option_scrutinee_2026-07-27.md.
    pub(crate) fn payload_slot_expr(outer_variant: &str, subject_ref: &HirExpr, i: usize, arity: usize) -> HirExpr {
        let legacy_payload_expr = HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: "rt_enum_payload".to_string(),
                args: vec![subject_ref.clone()],
            },
            ty: TypeId::ANY,
        };
        let payload_expr = if outer_variant == "Some" && arity == 1 {
            HirExpr {
                kind: HirExprKind::If {
                    condition: Box::new(HirExpr {
                        kind: HirExprKind::Binary {
                            op: BinOp::GtEq,
                            left: Box::new(HirExpr {
                                kind: HirExprKind::BuiltinCall {
                                    name: "rt_enum_id".to_string(),
                                    args: vec![subject_ref.clone()],
                                },
                                ty: TypeId::I64,
                            }),
                            right: Box::new(HirExpr {
                                kind: HirExprKind::Integer(0),
                                ty: TypeId::I64,
                            }),
                        },
                        ty: TypeId::BOOL,
                    }),
                    then_branch: Box::new(legacy_payload_expr),
                    else_branch: Some(Box::new(HirExpr {
                        kind: subject_ref.kind.clone(),
                        ty: TypeId::ANY,
                    })),
                },
                ty: TypeId::ANY,
            }
        } else {
            legacy_payload_expr
        };
        if arity == 1 {
            payload_expr
        } else {
            HirExpr {
                kind: HirExprKind::Index {
                    receiver: Box::new(payload_expr),
                    index: Box::new(HirExpr {
                        kind: HirExprKind::Integer(i as i64),
                        ty: TypeId::I64,
                    }),
                },
                ty: TypeId::ANY,
            }
        }
    }

    /// Refutability test for ONE sub-pattern sitting in an already-extracted
    /// payload slot, or `None` when that sub-pattern is irrefutable.
    ///
    /// `slot` is an expression, not a local, so this recurses to arbitrary
    /// depth: the slot of an inner variant becomes the subject of the next
    /// level down. Descending only one level made
    /// `case C(L2.S(L3.X(n)), tag)` select on `L2.S` alone, so an `L3.Y`
    /// subject took the `L3.X` arm.
    pub(crate) fn subpattern_condition(
        &mut self,
        slot: &HirExpr,
        pattern: &Pattern,
        ctx: &mut FunctionContext,
    ) -> Option<HirExpr> {
        // Default-off probe. Which of the three match implementations a given
        // engine actually reaches is not inferable from the source: the JIT
        // does not use `interpreter_patterns.rs`, and match ARMS route through
        // the statement-form twin rather than the expression form, so an
        // unconditional print in `lower_pattern_condition`'s `Pattern::Enum`
        // arm emits nothing for a program that trips this code path. Set
        // SIMPLE_DEBUG_PATTERN_LOWER=1 to see this walk fire.
        if std::env::var_os("SIMPLE_DEBUG_PATTERN_LOWER").is_some() {
            eprintln!(
                "[pattern-lower] subpattern_condition kind={}",
                pattern_kind_name(pattern)
            );
        }
        match pattern {
            // Irrefutable: binds or ignores, never rejects.
            Pattern::Wildcard
            | Pattern::Identifier(_)
            | Pattern::MutIdentifier(_)
            | Pattern::MoveIdentifier(_)
            | Pattern::Rest => None,
            Pattern::Typed { pattern, .. } => self.subpattern_condition(slot, pattern, ctx),
            Pattern::Literal(lit_expr) => {
                // `case A(0, y)` must reject `A(9, 7)`. Without this the arm was
                // irrefutable and the first literal arm swallowed every value.
                let lit_hir = self.lower_expr(lit_expr, ctx).ok()?;
                // The slot is ANY-typed (it came out of rt_enum_payload), so the
                // literal's own type is the only usable signal for picking the
                // text comparison over the scalar one.
                let is_string = lit_hir.ty == TypeId::STRING
                    || lit_hir.ty == TypeId::CHAR
                    || matches!(lit_hir.kind, HirExprKind::String(_));
                Some(if is_string {
                    HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: "rt_string_eq".to_string(),
                            args: vec![slot.clone(), lit_hir],
                        },
                        ty: TypeId::BOOL,
                    }
                } else {
                    HirExpr {
                        kind: HirExprKind::Binary {
                            op: BinOp::Eq,
                            left: Box::new(slot.clone()),
                            right: Box::new(lit_hir),
                        },
                        ty: TypeId::BOOL,
                    }
                })
            }
            Pattern::Range { start, end, inclusive } => {
                let start_hir = self.lower_expr(start, ctx).ok()?;
                let end_hir = self.lower_expr(end, ctx).ok()?;
                let gte = HirExpr {
                    kind: HirExprKind::Binary {
                        op: BinOp::GtEq,
                        left: Box::new(slot.clone()),
                        right: Box::new(start_hir),
                    },
                    ty: TypeId::BOOL,
                };
                let lte = HirExpr {
                    kind: HirExprKind::Binary {
                        op: if *inclusive { BinOp::LtEq } else { BinOp::Lt },
                        left: Box::new(slot.clone()),
                        right: Box::new(end_hir),
                    },
                    ty: TypeId::BOOL,
                };
                Some(HirExpr {
                    kind: HirExprKind::Binary {
                        op: BinOp::And,
                        left: Box::new(gte),
                        right: Box::new(lte),
                    },
                    ty: TypeId::BOOL,
                })
            }
            Pattern::Or(alternatives) => {
                // An alternative that is itself irrefutable makes the whole
                // `Or` irrefutable — returning a partial OR would reject values
                // the pattern does accept.
                let mut acc: Option<HirExpr> = None;
                for alt in alternatives {
                    let test = self.subpattern_condition(slot, alt, ctx)?;
                    acc = Some(match acc {
                        None => test,
                        Some(prev) => HirExpr {
                            kind: HirExprKind::Binary {
                                op: BinOp::Or,
                                left: Box::new(prev),
                                right: Box::new(test),
                            },
                            ty: TypeId::BOOL,
                        },
                    });
                }
                acc
            }
            Pattern::Enum { variant, payload, .. } => {
                // A struct/class spelling (`Point(x, y)`) also arrives as
                // Pattern::Enum. Emitting a discriminant check for it would
                // read an object pointer's enum header and never match — see
                // `is_real_enum_variant_name`. The struct itself is
                // irrefutable, but a refutable sub-pattern inside it
                // (`P(Point(0, b))`) still has to be tested, by positional
                // field access rather than payload extraction.
                if !self.is_real_enum_variant_name(variant) {
                    let fields = payload.as_ref()?;
                    let positional: Vec<(usize, &Pattern)> = fields.iter().enumerate().collect();
                    return self.struct_fields_condition(slot, variant, &positional, ctx);
                }
                let expected_disc: i64 = {
                    use std::collections::hash_map::DefaultHasher;
                    use std::hash::{Hash, Hasher};
                    let mut hasher = DefaultHasher::new();
                    variant.hash(&mut hasher);
                    (hasher.finish() & 0xFFFFFFFF) as i64
                };
                let tag_test = HirExpr {
                    kind: HirExprKind::BuiltinCall {
                        name: "rt_enum_check_discriminant".to_string(),
                        args: vec![
                            slot.clone(),
                            HirExpr {
                                kind: HirExprKind::Integer(expected_disc),
                                ty: TypeId::I64,
                            },
                        ],
                    },
                    ty: TypeId::BOOL,
                };
                let deeper = payload
                    .as_ref()
                    .and_then(|inner| self.nested_payload_condition(variant, slot, inner, ctx));
                Some(match deeper {
                    None => tag_test,
                    Some(inner_test) => HirExpr {
                        kind: HirExprKind::Binary {
                            op: BinOp::And,
                            left: Box::new(tag_test),
                            right: Box::new(inner_test),
                        },
                        ty: TypeId::BOOL,
                    },
                })
            }
            Pattern::Struct { name, fields } => {
                // Named-field spelling `Point { x: 0, y: b }`. Resolve each
                // named field to its declaration index, then test positionally.
                let struct_fields = self.struct_field_list(name)?;
                let mut positional: Vec<(usize, &Pattern)> = Vec::new();
                for (field_name, field_pattern) in fields {
                    let idx = struct_fields.iter().position(|(n, _)| n == field_name)?;
                    positional.push((idx, field_pattern));
                }
                self.struct_fields_condition(slot, name, &positional, ctx)
            }
            Pattern::Tuple(elements) => self.sequence_condition(slot, elements, false, ctx),
            Pattern::Array(elements) => self.sequence_condition(slot, elements, true, ctx),
        }
    }

    /// `rt_array_len(slot)` as an i64 expression.
    pub(crate) fn array_len_expr(slot: &HirExpr) -> HirExpr {
        HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: "rt_array_len".to_string(),
                args: vec![slot.clone()],
            },
            ty: TypeId::I64,
        }
    }

    fn seq_i64_const(value: i64) -> HirExpr {
        HirExpr {
            kind: HirExprKind::Integer(value),
            ty: TypeId::I64,
        }
    }

    /// `(element_expression, sub_pattern)` for every element position of an
    /// array/tuple pattern whose value sits at `slot`.
    ///
    /// This is the SINGLE OWNER of sequence element addressing: both the
    /// refutability test ([`Self::sequence_condition`]) and the binder emission
    /// (`bind_sequence` in hir/lower/stmt_lowering.rs) walk it, so an arm can
    /// never be selected on one element and bound from another.
    ///
    /// `Pattern::Rest` (`...`) splits the walk, mirroring the tree-walk
    /// interpreter in `interpreter_patterns.rs`: leading elements keep their
    /// literal index, trailing elements are addressed from the END as
    /// `rt_array_len(slot) - k`. The parser only ever produces `Pattern::Rest`
    /// inside an ARRAY pattern (`parser_patterns.rs`, `LBracket` arm), so a
    /// rest with trailing elements in a non-array sequence has no addressable
    /// form; that shape returns `None` and leaves the caller at its previous
    /// irrefutable/unbound behaviour rather than inventing an index.
    pub(crate) fn sequence_element_slots<'p>(
        slot: &HirExpr,
        patterns: &'p [Pattern],
        is_array: bool,
    ) -> Option<Vec<(HirExpr, &'p Pattern)>> {
        let index_at = |index: HirExpr| HirExpr {
            kind: HirExprKind::Index {
                receiver: Box::new(slot.clone()),
                index: Box::new(index),
            },
            ty: TypeId::ANY,
        };

        let rest_index = patterns.iter().position(|p| matches!(p, Pattern::Rest));
        let mut out: Vec<(HirExpr, &Pattern)> = Vec::new();
        match rest_index {
            None => {
                for (i, p) in patterns.iter().enumerate() {
                    out.push((index_at(Self::seq_i64_const(i as i64)), p));
                }
            }
            Some(rest_idx) => {
                for (i, p) in patterns[..rest_idx].iter().enumerate() {
                    out.push((index_at(Self::seq_i64_const(i as i64)), p));
                }
                let after = &patterns[rest_idx + 1..];
                if !after.is_empty() && !is_array {
                    return None;
                }
                for (j, p) in after.iter().enumerate() {
                    let from_end = (after.len() - j) as i64;
                    let index = HirExpr {
                        kind: HirExprKind::Binary {
                            op: BinOp::Sub,
                            left: Box::new(Self::array_len_expr(slot)),
                            right: Box::new(Self::seq_i64_const(from_end)),
                        },
                        ty: TypeId::I64,
                    };
                    out.push((index_at(index), p));
                }
            }
        }
        Some(out)
    }

    /// Refutability test for an array/tuple pattern whose value sits at `slot`,
    /// or `None` when every element is irrefutable and no length test applies.
    ///
    /// The length discriminator is ARRAYS ONLY, and that asymmetry is load
    /// bearing:
    ///
    /// * An array's length is a runtime property, so `case [a, b]` must reject
    ///   `[1, 2, 3]`. Without it the first array arm swallowed every array.
    /// * A TUPLE's arity is fixed by its type, so an arity test is always true
    ///   for a well-typed program — and `rt_array_len` returns `-1` on a Tuple
    ///   heap object (the `as_typed_ptr!` tag check fails), so emitting one
    ///   would make every tuple arm fail to match. Tuple patterns take their
    ///   refutability from their ELEMENTS only.
    ///
    /// A length test on its own is NOT a fix for the destructuring gap: it only
    /// moves `[1, 2, 3]` from a `[a, b]` arm to a `[a, b, c]` arm that still
    /// binds zeros. The binders emitted by `bind_sequence` over the same
    /// [`Self::sequence_element_slots`] walk are the other required half.
    pub(crate) fn sequence_condition(
        &mut self,
        slot: &HirExpr,
        patterns: &[Pattern],
        is_array: bool,
        ctx: &mut FunctionContext,
    ) -> Option<HirExpr> {
        let slots = Self::sequence_element_slots(slot, patterns, is_array)?;

        let mut combined: Option<HirExpr> = None;
        if is_array {
            let has_rest = patterns.iter().any(|p| matches!(p, Pattern::Rest));
            let (op, want) = if has_rest {
                (BinOp::GtEq, (patterns.len() - 1) as i64)
            } else {
                (BinOp::Eq, patterns.len() as i64)
            };
            combined = Some(HirExpr {
                kind: HirExprKind::Binary {
                    op,
                    left: Box::new(Self::array_len_expr(slot)),
                    right: Box::new(Self::seq_i64_const(want)),
                },
                ty: TypeId::BOOL,
            });
        }

        for (elem_expr, sub) in &slots {
            let Some(test) = self.subpattern_condition(elem_expr, sub, ctx) else {
                continue;
            };
            combined = Some(match combined {
                None => test,
                Some(prev) => HirExpr {
                    kind: HirExprKind::Binary {
                        op: BinOp::And,
                        left: Box::new(prev),
                        right: Box::new(test),
                    },
                    ty: TypeId::BOOL,
                },
            });
        }
        combined
    }

    /// Declared `(name, type)` field list of the struct/class named `name`.
    pub(crate) fn struct_field_list(&self, name: &str) -> Option<Vec<(String, TypeId)>> {
        let tid = self.module.types.lookup(name)?;
        match self.module.types.get(tid) {
            Some(HirType::Struct { fields, .. }) => Some(fields.clone()),
            _ => None,
        }
    }

    /// Refutability test for the fields of a struct sub-pattern sitting at
    /// `slot`, given `(field_index, sub_pattern)` pairs.
    ///
    /// A struct pattern is itself irrefutable — the type system already fixed
    /// the class — so this returns `None` unless some FIELD is refutable.
    pub(crate) fn struct_fields_condition(
        &mut self,
        slot: &HirExpr,
        struct_name: &str,
        positional: &[(usize, &Pattern)],
        ctx: &mut FunctionContext,
    ) -> Option<HirExpr> {
        let struct_ty = self.module.types.lookup(struct_name)?;
        let fields = match self.module.types.get(struct_ty) {
            Some(HirType::Struct { fields, .. }) => fields.clone(),
            _ => return None,
        };
        let mut combined: Option<HirExpr> = None;
        for (field_index, field_pattern) in positional {
            let Some((_, field_ty)) = fields.get(*field_index).cloned() else {
                continue;
            };
            let field_expr = HirExpr {
                kind: HirExprKind::FieldAccess {
                    receiver: Box::new(HirExpr {
                        kind: slot.kind.clone(),
                        ty: struct_ty,
                    }),
                    field_index: *field_index,
                },
                ty: field_ty,
            };
            let Some(test) = self.subpattern_condition(&field_expr, field_pattern, ctx) else {
                continue;
            };
            combined = Some(match combined {
                None => test,
                Some(prev) => HirExpr {
                    kind: HirExprKind::Binary {
                        op: BinOp::And,
                        left: Box::new(prev),
                        right: Box::new(test),
                    },
                    ty: TypeId::BOOL,
                },
            });
        }
        combined
    }

    /// Top-level refutability test for the positional class spelling
    /// `case Point(0, y):`.
    ///
    /// Shared by the expression twin ([`Self::lower_pattern_condition`]) and the
    /// statement twin (`lower_pattern_condition_stmt` in
    /// hir/lower/stmt_lowering.rs — the one match ARMS take) so the two cannot
    /// drift.
    ///
    /// A struct pattern is irrefutable *on the class*: the type system already
    /// fixed which class the subject is, and a discriminant check would read an
    /// object pointer's enum header and never match. Its FIELD sub-patterns are
    /// a different question, and both twins used to answer it by returning a
    /// bare `Bool(true)` while discarding `payload` entirely. That is the same
    /// shape as the enum-payload defect fixed in
    /// [`Self::nested_payload_condition`] — the tag half handled, the payload
    /// half dropped — so `case Point(0, y):` matched EVERY `Point` and made
    /// every later arm unreachable, silently and with exit 0.
    ///
    /// Only the TOP-LEVEL position was wrong. A struct pattern nested in an enum
    /// payload, an array element or a tuple element routes through
    /// [`Self::subpattern_condition`], which has tested struct fields since
    /// `5ce2f653a49`. Recursion (depth 3+, literal fields, array/tuple field
    /// sub-patterns) is likewise [`Self::struct_fields_condition`]'s; this is
    /// only the entry point.
    ///
    /// `None` from the walk means every field is irrefutable — the one case
    /// where `Bool(true)` is the correct answer, not a dropped test.
    pub(crate) fn class_pattern_condition(
        &mut self,
        subject_ref: &HirExpr,
        struct_name: &str,
        payload: Option<&Vec<Pattern>>,
        ctx: &mut FunctionContext,
    ) -> HirExpr {
        let tested = payload.and_then(|fields| {
            let positional: Vec<(usize, &Pattern)> = fields.iter().enumerate().collect();
            self.struct_fields_condition(subject_ref, struct_name, &positional, ctx)
        });
        tested.unwrap_or(HirExpr {
            kind: HirExprKind::Bool(true),
            ty: TypeId::BOOL,
        })
    }

    /// Top-level refutability test for the named-field spelling
    /// `case Point { x: 0, y: b }:` (`Pattern::Struct`), the twin of
    /// [`Self::class_pattern_condition`].
    ///
    /// A field name that does not resolve leaves the pattern irrefutable rather
    /// than inventing an index — the same under-report rule
    /// [`Self::subpattern_condition`] already applies to this spelling.
    pub(crate) fn named_struct_pattern_condition(
        &mut self,
        subject_ref: &HirExpr,
        struct_name: &str,
        fields: &[(String, Pattern)],
        ctx: &mut FunctionContext,
    ) -> HirExpr {
        let irrefutable = HirExpr {
            kind: HirExprKind::Bool(true),
            ty: TypeId::BOOL,
        };
        let Some(struct_fields) = self.struct_field_list(struct_name) else {
            return irrefutable;
        };
        let mut positional: Vec<(usize, &Pattern)> = Vec::new();
        for (field_name, field_pattern) in fields {
            let Some(idx) = struct_fields.iter().position(|(n, _)| n == field_name) else {
                return irrefutable;
            };
            positional.push((idx, field_pattern));
        }
        self.struct_fields_condition(subject_ref, struct_name, &positional, ctx)
            .unwrap_or(irrefutable)
    }

    /// Look up the field types for an enum variant.
    /// Returns None if the enum or variant is not found.
    /// If expected_ty is provided and is an enum type, use it directly.
    fn get_enum_variant_field_types_with_hint(
        &self,
        enum_name: &str,
        variant_name: &str,
        expected_ty: TypeId,
    ) -> Option<Vec<TypeId>> {
        // `T?` resolves to Pointer<T>, while pattern syntax still uses
        // `Some(value)`. Preserve T on the binding instead of searching an
        // unrelated generic Option definition and degrading the payload to ANY.
        if variant_name == "Some" {
            if let Some(HirType::Pointer { inner, .. }) = self.module.types.get(expected_ty) {
                return Some(vec![*inner]);
            }
        }

        // First, try to use the expected type if it's an enum
        if expected_ty != TypeId::ANY {
            if let Some(HirType::Enum {
                name: enum_type_name,
                variants,
                ..
            }) = self.module.types.get(expected_ty)
            {
                for (name, fields) in variants {
                    if name == variant_name {
                        return fields.clone();
                    }
                }
            }
        }

        // Handle wildcard enum name "_" - search all enums for the variant
        if enum_name == "_" {
            // Search all types for an enum with this variant
            for (_, hir_type) in self.module.types.iter() {
                if let HirType::Enum { variants, .. } = hir_type {
                    for (name, fields) in variants {
                        if name == variant_name {
                            return fields.clone();
                        }
                    }
                }
            }
            return None;
        }

        // Look up the enum type by name
        let type_id = self.module.types.lookup(enum_name)?;
        let hir_type = self.module.types.get(type_id)?;

        if let HirType::Enum { variants, .. } = hir_type {
            for (name, fields) in variants {
                if name == variant_name {
                    return fields.clone();
                }
            }
        }
        None
    }

    /// Extract variable bindings from a pattern.
    /// Returns a list of (name, type) pairs for variables that should be bound.
    pub fn extract_pattern_bindings(&self, pattern: &Pattern, subject_ty: TypeId) -> Vec<(String, TypeId)> {
        let mut bindings = Vec::new();
        self.collect_pattern_bindings(pattern, subject_ty, &mut bindings);
        bindings
    }

    pub(crate) fn subject_enum_has_variant(&self, subject_ty: TypeId, name: &str) -> bool {
        let Some(HirType::Enum {
            name: owner, variants, ..
        }) = self.module.types.get(subject_ty)
        else {
            return false;
        };
        let local_has_variant = variants.iter().any(|(variant, _)| variant == name);
        if local_has_variant || !variants.is_empty() {
            return local_has_variant;
        }

        self.global_enum_defs
            .as_ref()
            .and_then(|defs| defs.get(owner))
            .is_some_and(|summary| {
                summary
                    .iter()
                    .any(|(variant, payload)| variant == name && payload.is_none())
            })
    }

    /// Is a bare `case <name>:` arm provably NOT an intended binding?
    ///
    /// True only when all of the following hold, so that an under-report is the
    /// failure mode rather than a false positive:
    ///
    /// * the subject's static type resolves to `HirType::Enum`,
    /// * that enum's variant list is known and non-empty (an empty list means
    ///   the summary was never populated, not that the enum has no variants),
    /// * `name` is not one of those variants, and
    /// * `name` is spelled as a type/variant/const, i.e. it starts with an
    ///   uppercase letter or is `SCREAMING_SNAKE_CASE`.
    ///
    /// Bug: `doc/08_tracking/bug/case_bare_ident_is_irrefutable_binding_2026-08-01.md`
    ///
    /// Membership tests use `char::is_ascii_uppercase`, never a `>= 'A' && <= 'Z'`
    /// range comparison -- see that bug doc's note on the JIT text-ordering
    /// defect that made range checks on derived text silently false.
    pub(crate) fn bare_case_name_is_certainly_not_a_binding(&self, subject_ty: TypeId, name: &str) -> bool {
        let Some(HirType::Enum { variants, .. }) = self.module.types.get(subject_ty) else {
            return false;
        };
        if variants.is_empty() {
            // Variant list not populated -- we cannot conclude anything.
            return false;
        }
        if variants.iter().any(|(variant, _)| variant == name) {
            return false;
        }
        crate::pattern_case_naming::case_name_is_spelled_like_a_variant(name)
    }

    fn pattern_binding_is_mutable(pattern: &Pattern, name: &str) -> bool {
        match pattern {
            Pattern::MutIdentifier(binding) => binding == name,
            Pattern::Tuple(patterns) | Pattern::Array(patterns) | Pattern::Or(patterns) => patterns
                .iter()
                .any(|pattern| Self::pattern_binding_is_mutable(pattern, name)),
            Pattern::Struct { fields, .. } => fields
                .iter()
                .any(|(_, pattern)| Self::pattern_binding_is_mutable(pattern, name)),
            Pattern::Enum { payload, .. } => payload.as_ref().is_some_and(|patterns| {
                patterns
                    .iter()
                    .any(|pattern| Self::pattern_binding_is_mutable(pattern, name))
            }),
            Pattern::Typed { pattern, .. } => Self::pattern_binding_is_mutable(pattern, name),
            _ => false,
        }
    }

    pub(crate) fn register_match_bindings(
        &self,
        pattern: &Pattern,
        bindings: &[(String, TypeId)],
        ctx: &mut FunctionContext,
    ) -> Vec<(String, Option<usize>)> {
        bindings
            .iter()
            .map(|(name, ty)| {
                let previous = ctx.local_map.get(name).copied();
                let mutability = if Self::pattern_binding_is_mutable(pattern, name) {
                    Mutability::Mutable
                } else {
                    Mutability::Immutable
                };
                ctx.add_local(name.clone(), *ty, mutability);
                (name.clone(), previous)
            })
            .collect()
    }

    pub(crate) fn restore_match_bindings(
        &self,
        previous_bindings: Vec<(String, Option<usize>)>,
        ctx: &mut FunctionContext,
    ) {
        for (name, previous) in previous_bindings {
            if let Some(local_index) = previous {
                ctx.local_map.insert(name, local_index);
            } else {
                ctx.local_map.remove(&name);
            }
        }
    }

    /// Recursively collect bindings from a pattern
    fn collect_pattern_bindings(&self, pattern: &Pattern, expected_ty: TypeId, bindings: &mut Vec<(String, TypeId)>) {
        match pattern {
            Pattern::Identifier(name) => {
                if !self.subject_enum_has_variant(expected_ty, name) {
                    bindings.push((name.clone(), expected_ty));
                }
            }
            Pattern::MutIdentifier(name) => {
                bindings.push((name.clone(), expected_ty));
            }
            Pattern::Tuple(patterns) => {
                // For tuples, try to get element types from expected type
                let resolved_ty = self.module.types.get(expected_ty);
                let element_types = if let Some(HirType::Tuple(types)) = resolved_ty {
                    Some(types.clone())
                } else {
                    None
                };

                for (i, p) in patterns.iter().enumerate() {
                    let elem_ty = element_types
                        .as_ref()
                        .and_then(|types| types.get(i).copied())
                        .unwrap_or(TypeId::ANY);
                    self.collect_pattern_bindings(p, elem_ty, bindings);
                }
            }
            Pattern::Enum {
                name: enum_name,
                variant: variant_name,
                payload,
            } => {
                // Enum pattern like Some(x) or Int(bits_a, signed_a)
                // Try to look up the actual variant field types
                if let Some(patterns) = payload {
                    // Try to find the enum type and variant to get field types
                    // Use expected_ty as a hint when enum_name is wildcard
                    // Fall back to the STRUCT field list for the positional
                    // class spelling `case Holder([a, b], (c, d))`: the parser
                    // cannot tell it from an enum variant, so it arrives here
                    // as `Pattern::Enum` with a struct name in `variant`, and
                    // the enum lookup answers `None`. Without this fallback
                    // every field sub-pattern was typed ANY, which typed the
                    // ARRAY elements ANY too (the `Pattern::Array` arm below
                    // resolves its element type from `expected_ty`) and left
                    // `bind_sequence` emitting ANY-typed `Let`s over an
                    // ANY-typed local — so `case Holder([a, b], ...)` selected
                    // the right arm and then surfaced `a` as an undecoded
                    // tagged `<value:0x6>` and `b` as `1` on the JIT.
                    // `bind_struct_fields` / `struct_fields_condition` already
                    // resolve the same struct by the same name; this is the
                    // binding-TYPE half of that same resolution.
                    let field_types = self
                        .get_enum_variant_field_types_with_hint(enum_name, variant_name, expected_ty)
                        .or_else(|| {
                            self.struct_field_list(variant_name)
                                .map(|fields| fields.into_iter().map(|(_, ty)| ty).collect())
                        });

                    for (i, p) in patterns.iter().enumerate() {
                        let field_ty = field_types
                            .as_ref()
                            .and_then(|types| types.get(i).copied())
                            .unwrap_or(TypeId::ANY);
                        self.collect_pattern_bindings(p, field_ty, bindings);
                    }
                }
            }
            Pattern::Struct { name, fields } => {
                // Struct pattern like `Point { x, y }`. Resolve each field's
                // DECLARED type by name, for the same reason as the positional
                // spelling above: an ANY-typed binding makes MIR pick generic
                // boxing, which surfaces an i64 as a misformatted value at use
                // sites and mistypes array elements one level down.
                let struct_fields = self.struct_field_list(name);
                for (field_name, field_pattern) in fields {
                    let field_ty = struct_fields
                        .as_ref()
                        .and_then(|f| f.iter().find(|(n, _)| n == field_name))
                        .map(|(_, ty)| *ty)
                        .unwrap_or(TypeId::ANY);
                    self.collect_pattern_bindings(field_pattern, field_ty, bindings);
                }
            }
            Pattern::Array(patterns) => {
                // Resolve the declared element type when the subject is a known
                // array, so the `Let` emitted by `bind_sequence` carries a
                // concrete type instead of ANY. An ANY-typed binding makes MIR
                // pick generic boxing and can surface an i64 element as a
                // misformatted value at use sites.
                let element_ty = match self.module.types.get(expected_ty) {
                    Some(HirType::Array { element, .. }) => *element,
                    _ => TypeId::ANY,
                };
                for p in patterns {
                    self.collect_pattern_bindings(p, element_ty, bindings);
                }
            }
            Pattern::Or(patterns) => {
                // Or patterns should bind the same variables - just use first pattern
                if let Some(first) = patterns.first() {
                    self.collect_pattern_bindings(first, expected_ty, bindings);
                }
            }
            Pattern::Typed { pattern, ty: _ } => {
                // Type annotation on pattern - recurse into inner pattern
                self.collect_pattern_bindings(pattern, expected_ty, bindings);
            }
            // Patterns that don't introduce bindings
            Pattern::Wildcard
            | Pattern::Literal(_)
            | Pattern::Range { .. }
            | Pattern::Rest
            | Pattern::MoveIdentifier(_) => {}
        }
    }

    /// Lower a match arm body (block of statements) to a single HIR expression
    fn lower_match_arm_body(&mut self, body: &ast::Block, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        // If body is empty, return Nil
        if body.statements.is_empty() {
            return Ok(HirExpr {
                kind: HirExprKind::Nil,
                ty: TypeId::NIL,
            });
        }

        // For a single expression statement, just lower that expression
        if body.statements.len() == 1 {
            if let simple_parser::ast::Node::Expression(expr) = &body.statements[0] {
                return self.lower_expr(expr, ctx);
            }
            if let simple_parser::ast::Node::Return(ret_stmt) = &body.statements[0] {
                // S70 root cause (native-smoke-matrix `match_value_position_return`):
                // an arm body that is a genuine `return <expr>` must stay a real
                // function-level return, not collapse into the arm's *value*.
                // The previous `return self.lower_expr(expr, ctx)` silently
                // discarded the `return` — the enclosing `HirExprKind::If` chain
                // built by `lower_match_arms` for `val r = match n: ...` then
                // stored that value into the match's result temp and fell
                // through to whatever followed the `match` (e.g. `return r + 1`
                // ran even though the arm said `return 7`, yielding 8 instead of
                // 7). Wrapping the return in a one-statement `Block` preserves
                // the terminator: MIR's `HirStmt::Return` handling sets a real
                // `Terminator::Return` on the current block, and
                // `finalize_block_jump`'s existing Unreachable-only guard
                // (mirroring the pure-Simple fix in f10db44f0f4) already stops
                // `lower_if_expr` from clobbering it with a merge-block jump.
                // `ty` still reports the returned expression's type (not NIL)
                // so callers that read the arm's type (e.g. the overall match
                // expression's inferred type) see the same type as before.
                let (value, ty) = match &ret_stmt.value {
                    Some(expr) => {
                        let lowered = self.lower_expr(expr, ctx)?;
                        let ty = lowered.ty;
                        (Some(lowered), ty)
                    }
                    None => (None, TypeId::NIL),
                };
                return Ok(HirExpr {
                    kind: HirExprKind::Block(vec![crate::hir::HirStmt::Return(value)]),
                    ty,
                });
            }
        }

        // For multiple statements, lower the whole arm body as a value-producing
        // block, exactly like a do-block. The previous hand-rolled loop here
        // dropped every non-final statement: `val x = f()` only registered the
        // local (no `HirStmt::Let`, so no store — the local stayed
        // uninitialized/zero), and side-effecting expression statements before
        // the last one were lowered and discarded. A lambda in the arm's
        // result expression capturing such a `val` then read garbage at
        // runtime (stage4 `CompileContext.create` SIGSEGV, receiver = nil).
        self.lower_do_block(&body.statements, ctx)
    }

    /// Lower a do block expression to HIR
    ///
    /// A do block is a sequence of statements that evaluates to the result
    /// of the last expression. It's essentially an anonymous block expression.
    /// For now, we only support Expression nodes in do blocks.
    pub(super) fn lower_do_block(
        &mut self,
        statements: &[simple_parser::ast::Node],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // If the block is empty, return nil
        if statements.is_empty() {
            return Ok(HirExpr {
                kind: HirExprKind::Nil,
                ty: TypeId::NIL,
            });
        }

        // If there's only one expression statement, lower it directly
        if statements.len() == 1 {
            if let simple_parser::ast::Node::Expression(expr) = &statements[0] {
                return self.lower_expr(expr, ctx);
            }
        }

        let mut block_stmts = Vec::new();
        let mut result_ty = TypeId::NIL;

        for stmt in statements {
            match stmt {
                simple_parser::ast::Node::Expression(expr) => {
                    let expr = self.lower_expr(expr, ctx)?;
                    result_ty = expr.ty;
                    block_stmts.push(crate::hir::HirStmt::Expr(expr));
                }
                simple_parser::ast::Node::Return(ret_stmt) => {
                    // S70 root cause (native-smoke-matrix `match_value_position_return`):
                    // same class of bug as the single-statement case in
                    // `lower_match_arm_body` above — a `return <expr>` inside a
                    // multi-statement do-block/match-arm body must stay a real
                    // function-level return (`HirStmt::Return`, which MIR turns
                    // into an actual block `Terminator::Return`), not a plain
                    // `HirStmt::Expr` that the enclosing if-chain just treats as
                    // this block's tail value and falls through past.
                    let (value, ty) = match &ret_stmt.value {
                        Some(expr) => {
                            let lowered = self.lower_expr(expr, ctx)?;
                            let ty = lowered.ty;
                            (Some(lowered), ty)
                        }
                        None => (None, TypeId::NIL),
                    };
                    result_ty = ty;
                    block_stmts.push(crate::hir::HirStmt::Return(value));
                }
                _ => block_stmts.extend(self.lower_node(stmt, ctx)?),
            }
        }

        Ok(HirExpr {
            kind: HirExprKind::Block(block_stmts),
            ty: result_ty,
        })
    }

    /// Lower a lexical unsafe block without turning `return` or loop control
    /// into a tail value. The marker remains visible to HIR safety passes.
    pub(super) fn lower_unsafe_block(
        &mut self,
        statements: &[simple_parser::ast::Node],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let block = simple_parser::ast::Block {
            statements: statements.to_vec(),
            ..Default::default()
        };
        let block_stmts = self.lower_block(&block, ctx)?;
        let result_ty = match block_stmts.last() {
            Some(crate::hir::HirStmt::Expr(expr)) => expr.ty,
            _ => TypeId::NIL,
        };
        Ok(HirExpr {
            kind: HirExprKind::UnsafeBlock(block_stmts),
            ty: result_ty,
        })
    }

    /// Lower a null coalescing expression (expr ?? default) to HIR
    ///
    /// The `??` operator returns the left operand if it's not nil,
    /// otherwise returns the right operand. This is lowered to:
    /// `if expr != nil then expr else default`
    ///
    /// For simplicity, we evaluate expr once and check against nil.
    pub(super) fn lower_coalesce(
        &mut self,
        expr: &Expr,
        default: &Expr,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let expr_hir = self.lower_expr(expr, ctx)?;
        let default_hir = self.lower_expr(default, ctx)?;

        // Statically non-nullable scalars can NEVER legitimately be nil, and the
        // runtime nil sentinel IS the raw integer 3 (TAG_SPECIAL = 0b011), so
        // emitting a runtime `expr != nil` check on a raw scalar turns the real
        // value 3 into the default (`x.index_of(..) ?? d` returned d when the
        // real answer was 3 — see
        // doc/08_tracking/bug/coalesce_raw_i64_sentinel_collision_2026-08-02.md).
        // For these types `??` is the identity: lower to the left operand
        // directly, no runtime check. STRING/ANY/UNKNOWN and every registered
        // type (incl. `T?`, which resolves to a Pointer TypeId) keep the
        // runtime nil check below.
        // Known caveat (tracked in the plan doc
        // doc/03_plan/compiler/type_system/seed_hirtype_optional_plan.md):
        // `first/last/get` are currently *typed* bare `T` while being
        // genuinely optional — they need an Optional TypeId to take the
        // checked path; that is the root fix this static rule is staged under.
        // The scalar TypeId alone is NOT sufficient evidence of presence, because
        // the method result-type table in `hir/lower/expr/mod.rs` deliberately
        // types several *genuinely optional* accessors as bare `T`
        // (`[T].first/last/get/min/max/pop`, `{K:V}.get/remove`). Trusting the
        // TypeId there made `[].first() ?? -1` and `{}.get(k) ?? -1` return the
        // raw sentinel `3` instead of `-1` — the sentinel leaking out as an
        // integer, which is strictly worse than the bug being fixed. Those
        // accessors therefore keep the runtime nil check.
        //
        // Retyping them to `T?` (`HirType::Pointer`, what `at` already does) is
        // the type-system-level root fix and is tracked in
        // doc/03_plan/compiler/type_system/seed_hirtype_optional_plan.md. It is
        // NOT done here: `at` itself is currently broken in value position on
        // the JIT (`xs.at(0)` prints `<enum@0x..>` and `val a: i64 = xs.at(1)`
        // binds 3200464915713, while `xs.first()` is correct), so moving the
        // widely-used accessors onto that lane today would import a larger
        // defect than it removes.
        let receiver_is_optional_accessor = matches!(
            expr,
            Expr::MethodCall { method, .. }
                if matches!(
                    method.as_str(),
                    "first" | "last" | "get" | "min" | "max" | "pop" | "remove" | "at"
                )
        );
        let statically_non_nullable = !receiver_is_optional_accessor
            && matches!(
                expr_hir.ty,
                TypeId::BOOL
                    | TypeId::I8
                    | TypeId::I16
                    | TypeId::I32
                    | TypeId::I64
                    | TypeId::U8
                    | TypeId::U16
                    | TypeId::U32
                    | TypeId::U64
                    | TypeId::F32
                    | TypeId::F64
                    | TypeId::CHAR
            );
        if std::env::var("SIMPLE_DEBUG_COALESCE").is_ok() {
            eprintln!(
                "[coalesce] operand ty={:?} optional_accessor={} non_nullable={}",
                expr_hir.ty, receiver_is_optional_accessor, statically_non_nullable
            );
        }
        if statically_non_nullable {
            return Ok(expr_hir);
        }

        // Create a nil check: expr != nil
        let nil_expr = HirExpr {
            kind: HirExprKind::Nil,
            ty: TypeId::NIL,
        };
        let condition = HirExpr {
            kind: HirExprKind::Binary {
                op: BinOp::NotEq,
                left: Box::new(expr_hir.clone()),
                right: Box::new(nil_expr),
            },
            ty: TypeId::BOOL,
        };

        // The result type is the type of the expression (or default if expr could be nil)
        let result_ty = if expr_hir.ty == TypeId::NIL {
            default_hir.ty
        } else {
            expr_hir.ty
        };

        // Unwrap the then-branch: if expr is Some(x), return x, not Some(x).
        // Use rt_unwrap_or_self which handles both enum and raw values.
        let unwrapped_expr = HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: "rt_unwrap_or_self".to_string(),
                args: vec![expr_hir],
            },
            ty: result_ty,
        };

        // The then-branch yields a TAGGED RuntimeValue (that is what a `T?` slot
        // holds). A raw scalar literal in the else-branch would leave the `If`
        // producing a tagged word on one edge and a raw one on the other, and
        // the consumer decodes by tag: `n ?? 9` on a nil `i64?` printed
        // `<invalid-heap:0x9>` because `9 & 7 == 1` is TAG_HEAP.
        // Bug: doc/08_tracking/bug/jit_optional_i64_payload_reinterpreted_2026-08-17.md
        let default_hir = self.box_scalar_into_tagged_result(result_ty, default_hir);

        Ok(HirExpr {
            kind: HirExprKind::If {
                condition: Box::new(condition),
                then_branch: Box::new(unwrapped_expr),
                else_branch: Some(Box::new(default_hir)),
            },
            ty: result_ty,
        })
    }

    /// Box a raw-scalar expression when it must flow out through a slot whose
    /// runtime representation is a tagged `RuntimeValue` (a nullable `T?`, or
    /// `Any`). Returns the expression unchanged in every other case.
    fn box_scalar_into_tagged_result(&self, result_ty: TypeId, value: HirExpr) -> HirExpr {
        let tagged_slot = result_ty == TypeId::ANY
            || matches!(self.module.types.get(result_ty), Some(HirType::Pointer { .. }));
        if !tagged_slot {
            return value;
        }
        let boxer = match value.ty {
            TypeId::BOOL => "rt_value_bool",
            TypeId::U64 => "rt_value_u64",
            TypeId::F32 | TypeId::F64 => "rt_value_float",
            TypeId::I8 | TypeId::I16 | TypeId::I32 | TypeId::I64 | TypeId::U8 | TypeId::U16 | TypeId::U32 => {
                "rt_value_int"
            }
            _ => return value,
        };
        HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: boxer.to_string(),
                args: vec![value],
            },
            ty: result_ty,
        }
    }

    /// Lower an expression that appears in **condition position** — an
    /// `if`/`elif`/`while`/`assert` test, a contract clause, a match guard, a
    /// ternary test, or an operand of `and`/`or`/`not`.
    ///
    /// The only expression that lowers differently here than in value position
    /// is `expr.?` (`Expr::ExistsCheck`). In value position `.?` yields `T?`
    /// (see `lower_exists_check`), and the nil sentinel is the non-zero integer
    /// `3` (`lower_nil_expr`), so branching directly on that value would make
    /// `if nil_opt.?:` truthy — a silent wrong-branch bug. Condition position
    /// therefore keeps the boolean presence predicate.
    ///
    /// This mirrors what the interpreter already does: it evaluates `.?` to the
    /// value and every condition site funnels through `is_condition_present`
    /// (`interpreter_control.rs`), which special-cases `Expr::ExistsCheck` to
    /// mean "not nil" rather than generic truthiness.
    ///
    /// `and`/`or`/`not` recurse so that `if a.? and b.?:` keeps both operands in
    /// condition position.
    pub(crate) fn lower_condition(&mut self, expr: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        // A bare `.?` test: emit the presence predicate directly.
        if let Expr::ExistsCheck(inner) = expr {
            let inner_hir = self.lower_expr(inner, ctx)?;
            return Ok(HirExpr {
                kind: HirExprKind::BuiltinCall {
                    name: "rt_is_some".to_string(),
                    args: vec![inner_hir],
                },
                ty: TypeId::BOOL,
            });
        }

        // Everything else goes through the normal dispatcher and is only
        // post-rewritten. Hand-building the `and`/`or`/`not` HIR here instead
        // bypassed whatever `lower_expr` does for those forms and perturbed
        // the JIT's extern set — observed as an "unresolved external symbol
        // 'rt_index_of'" bailout that demoted the whole browser-engine module
        // to the interpreter (8s -> 384s on the showcase style pass).
        let mut lowered = self.lower_expr(expr, ctx)?;
        let is_logical_combinator = match expr {
            Expr::Binary { op, .. } => matches!(op, ast::BinOp::And | ast::BinOp::Or),
            Expr::Unary { op, .. } => matches!(op, ast::UnaryOp::Not),
            _ => false,
        };
        if is_logical_combinator {
            // `if a.? and b.?:` — the operands are conditions too.
            Self::coerce_exists_value_to_bool_in_place(&mut lowered);
            return Ok(lowered);
        }

        // ROOT FIX (JIT branches on the raw slot word, 2026-08-17).
        //
        // A condition whose STATIC type is an optional / reference slot
        // (`T?` resolves to `HirType::Pointer` — see
        // `type_resolver.rs` `Type::Optional`) holds a TAGGED runtime word, not
        // a native boolean. The Cranelift `Terminator::Branch` lowering
        // (`codegen/instr/body.rs`) tests such a word with a bare
        // `icmp_imm(NotEqual, cond, 0)` — no tag decode, no nil check — and the
        // canonical nil sentinel is the NON-ZERO word `3`
        // (`TAG_SPECIAL | SPECIAL_NIL`). So `val n: text? = nil; if n:` took the
        // TRUE branch under the JIT while the interpreter (whose
        // `is_condition_present` decodes the value) took the FALSE branch —
        // a silent wrong-branch divergence with rc=0 on both engines.
        //
        // Fixed HERE rather than in `Terminator::Branch` deliberately: at the
        // Cranelift terminator the condition is an untyped i64 vreg that may
        // equally be a RAW native comparison result, so masking or routing
        // every branch through `rt_value_truthy` there would miscompile every
        // native conditional in the compiler. HIR still has the static type, so
        // only genuinely tagged conditions are rewritten, and the rewrite lands
        // on BOTH engines at once (no new interpreter/JIT skew).
        //
        // CANONICAL SEMANTICS (decided, not silently picked): `if x:` on an
        // optional/reference-typed `x` means PRESENCE — "x is not nil" — the
        // same meaning `x.?` already carries in condition position two dozen
        // lines above, and the same predicate (`rt_is_some`) implements both.
        // This deliberately does NOT adopt `RuntimeValue::truthy`'s
        // emptiness-aware rule; see the residual note below.
        //
        // RESIDUAL, knowingly left open: `RuntimeValue::truthy`
        // (runtime/src/value/core.rs) and the interpreter's
        // `interpreter/value_impl.rs` disagree independently about `""` and
        // about a boxed `false`, so `val b: bool? = false; if b:` is presence
        // (true) under this rule while a truthiness reading would say false.
        // Unifying those two truthiness tables is a separate change and is NOT
        // attempted here.
        // Narrow deliberately to the managed pointer kinds. `T?` resolves to
        // `Pointer { kind: Shared }` (type_resolver.rs), and Unique/Weak/Handle
        // are managed tagged slots too. RAW pointers (`RawConst`/`RawMut`) and
        // borrows are NOT: they hold an untagged machine address where the old
        // `!= 0` test is the correct null check, and `rt_is_some` would call a
        // null raw pointer "present" (word 0 decodes as TAG_INT 0, not nil).
        // Excluding them keeps this rewrite from regressing raw-pointer code.
        let is_tagged_slot = matches!(
            self.module.types.get(lowered.ty),
            Some(HirType::Pointer {
                kind: PointerKind::Shared | PointerKind::Unique | PointerKind::Weak | PointerKind::Handle,
                ..
            })
        ) || lowered.ty == TypeId::NIL;
        if is_tagged_slot {
            lowered = HirExpr {
                kind: HirExprKind::BuiltinCall {
                    name: "rt_is_some".to_string(),
                    args: vec![lowered],
                },
                ty: TypeId::BOOL,
            };
        }
        Ok(lowered)
    }

    /// Rewrite an already-lowered value-position `.?` into the boolean
    /// presence predicate, in place, for the implicit-return tail of a
    /// function declared `-> bool`.
    ///
    /// This is the implicit-return counterpart of `lower_bool_return_expr`
    /// (which handles the explicit `return x.?` form before lowering). It
    /// works on HIR rather than re-lowering the AST: a second `lower_expr`
    /// pass over the same subtree re-registers whatever that subtree
    /// references and perturbed the JIT's extern set — observed as a spurious
    /// "unresolved external symbol 'rt_index_of'" bailout that demoted the
    /// whole browser-engine module to the interpreter.
    ///
    /// Recognizes exactly the shape `lower_exists_check` emits —
    /// `LetIn { value, body: If { condition: rt_is_some(Local(idx)), .. } }` —
    /// and replaces it with `rt_is_some(value)`, dropping the now-unused
    /// binding. Recurses through `and`/`or`/`not` so
    /// `fn f() -> bool: a.? and b.?` is covered too.
    pub(crate) fn coerce_exists_value_to_bool_in_place(expr: &mut HirExpr) {
        match &mut expr.kind {
            HirExprKind::Binary { op, left, right } if matches!(op, BinOp::And | BinOp::Or) => {
                Self::coerce_exists_value_to_bool_in_place(left);
                Self::coerce_exists_value_to_bool_in_place(right);
                expr.ty = TypeId::BOOL;
            }
            HirExprKind::Unary { op, operand } if matches!(op, UnaryOp::Not) => {
                Self::coerce_exists_value_to_bool_in_place(operand);
                expr.ty = TypeId::BOOL;
            }
            // An `if`/`match` in tail position is itself the returned value, so
            // each of its arms is in bool-return position too.
            HirExprKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                Self::coerce_exists_value_to_bool_in_place(then_branch);
                if let Some(else_branch) = else_branch {
                    Self::coerce_exists_value_to_bool_in_place(else_branch);
                }
                expr.ty = TypeId::BOOL;
            }
            HirExprKind::Block(stmts) => {
                Self::coerce_exists_tail_in_place(stmts);
                expr.ty = TypeId::BOOL;
            }
            HirExprKind::LetIn { local_idx, value, body } => {
                let is_exists_shape = match &body.kind {
                    HirExprKind::If { condition, .. } => matches!(
                        &condition.kind,
                        HirExprKind::BuiltinCall { name, args }
                            if name == "rt_is_some"
                                && matches!(
                                    args.first().map(|a| &a.kind),
                                    Some(HirExprKind::Local(idx)) if idx == local_idx
                                )
                    ),
                    _ => false,
                };
                if is_exists_shape {
                    let subject = std::mem::replace(
                        value.as_mut(),
                        HirExpr {
                            kind: HirExprKind::Nil,
                            ty: TypeId::NIL,
                        },
                    );
                    expr.kind = HirExprKind::BuiltinCall {
                        name: "rt_is_some".to_string(),
                        args: vec![subject],
                    };
                    expr.ty = TypeId::BOOL;
                }
            }
            _ => {}
        }
    }

    /// Walk the **tail position** of a statement list and coerce every `.?`
    /// that ends up being the implicitly returned value.
    ///
    /// The tail of a `-> bool` body is not always a single trailing
    /// `HirStmt::Expr`. A `match` lowers to a chain of `HirStmt::If`, so
    ///
    /// ```text
    /// fn has_suggestion() -> bool:
    ///     match self:
    ///         case UnknownKey(_, _, suggestion): suggestion.?
    ///         case _: false
    /// ```
    ///
    /// leaves the `.?` as the last statement of a nested `then_block`, not of
    /// the function body. Handling only the outermost statement left that form
    /// returning the non-zero nil sentinel — measured on the pristine seed as
    /// `nested nil = true` where a plain-`bool` arm in the same position
    /// correctly returned `false`, so the nested implicit return is a real,
    /// working feature and the `.?` behaviour there was a genuine wrong-branch
    /// bug. Four owned sites use exactly this shape, all inside
    /// `src/compiler/` (`dim_constraints.spl`, `const_keys.spl`,
    /// `backend_types.spl`, `interpreter/pattern.spl`).
    ///
    /// Only `If` recurses. Loop bodies are deliberately excluded: the last
    /// expression of a `while`/`for`/`loop` body is not the function's return
    /// value.
    pub(crate) fn coerce_exists_tail_in_place(stmts: &mut [HirStmt]) {
        match stmts.last_mut() {
            Some(HirStmt::Expr(tail)) => Self::coerce_exists_value_to_bool_in_place(tail),
            Some(HirStmt::If {
                then_block, else_block, ..
            }) => {
                Self::coerce_exists_tail_in_place(then_block);
                if let Some(else_block) = else_block {
                    Self::coerce_exists_tail_in_place(else_block);
                }
            }
            _ => {}
        }
    }

    /// Lower an expression in **bool-return position** — the value of a
    /// `return` in, or the trailing expression of, a function declared
    /// `-> bool`.
    ///
    /// A declared `-> bool` return is a boolean context, so `.?` must produce
    /// the presence predicate here exactly as it does in an `if` test.
    /// Otherwise the `T?` value form escapes through the function boundary and
    /// every caller writing `if has(..):` branches on the non-zero nil
    /// sentinel and takes the wrong branch — the same silent wrong-branch bug
    /// `lower_condition` exists to prevent, just laundered through a return.
    ///
    /// This is not a special case for `.?`: it is the declared return type
    /// being honoured. It also closes the divergence recorded in
    /// `doc/08_tracking/bug/option_predicate_returns_payload_not_bool_2026-07-28.md`
    /// (a `-> bool` function returning `opt.?` silently returning the object).
    ///
    /// Non-bool return types are unaffected and lower normally, so
    /// `fn f() -> T?: x.?` still yields `T?` per spec.
    pub(crate) fn lower_bool_return_expr(&mut self, expr: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        if ctx.return_type == TypeId::BOOL {
            return self.lower_condition(expr, ctx);
        }
        self.lower_expr(expr, ctx)
    }

    /// Lower an existence check expression (`expr.?`) in **value position** to HIR.
    ///
    /// `.?` returns `T?` — the payload itself when present, `nil` when absent
    /// (`doc/07_guide/quick_reference/syntax_quick_reference.md`, "Existence
    /// Check (`.?`) — Returns `T?`"). "Present" means non-nil, and for
    /// Option/Result the Some/Ok arm.
    ///
    /// It must NOT collapse to a bare `rt_is_some` bool. That discarded the
    /// payload, so `val u = x.?` bound `true` (integer 1); a following field
    /// access masked the receiver with `~0x7` (`1 & ~7 == 0`), hit the
    /// nil-receiver guard in `codegen/instr/fields.rs` and executed `ud2`
    /// (SIGILL). See
    /// `doc/08_tracking/bug/seed_exists_check_lowers_to_bool_field_access_sigill_2026-07-28.md`
    /// and the native-smoke-matrix item "(14) Option/nil check (x.?)".
    ///
    /// The interpreter (`interpreter/expr.rs`) and the pure-Simple compiler
    /// (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`, `ExistsCheck`
    /// arm) already lower it this way; this is the port of that fix to the seed.
    ///
    /// The absent arm emits `HirExprKind::Nil`, which materializes the canonical
    /// nil sentinel `3` (`lower_nil_expr`) — NOT `0`, so `rt_is_none` recognizes
    /// it and an outer `if val v = x.?:` does not treat it as `Some(0)`.
    ///
    /// Condition position (`if x.?:`) does not come through here; it is handled
    /// by `lower_condition`, because branching on the non-zero nil sentinel
    /// would take the true branch for an absent value.
    ///
    /// The subject is bound to a `LetIn` temp so a side-effecting receiver
    /// (`f().?`) is evaluated exactly once — the presence test and the unwrap
    /// both read the temp.
    pub(super) fn lower_exists_check(&mut self, expr: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        let expr_hir = self.lower_expr(expr, ctx)?;
        let subject_ty = expr_hir.ty;

        // Result type is the Option/Result payload when the subject carries a
        // declared enum type. Struct-typed optionals often use the "raw
        // migration form" (a bare struct pointer assigned to a `T?` binding
        // without the canonical Some-wrap), in which case the subject type IS
        // already the payload type — keeping it preserves the struct-name
        // provenance a later `v.field` needs to resolve a field index.
        let payload_ty = match self.result_like_payload_type(subject_ty) {
            Some(ty) => ty,
            None if subject_ty == TypeId::NIL => TypeId::ANY,
            None => subject_ty,
        };

        let subject_idx = ctx.locals.len();
        ctx.add_local("$exists_check_subject".to_string(), subject_ty, Mutability::Immutable);

        let condition = HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: "rt_is_some".to_string(),
                args: vec![HirExpr {
                    kind: HirExprKind::Local(subject_idx),
                    ty: subject_ty,
                }],
            },
            ty: TypeId::BOOL,
        };
        // `rt_unwrap_or_self` handles both the wrapped enum form and the raw
        // migration form, same helper `lower_null_coalesce` uses.
        let present = HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: "rt_unwrap_or_self".to_string(),
                args: vec![HirExpr {
                    kind: HirExprKind::Local(subject_idx),
                    ty: subject_ty,
                }],
            },
            ty: payload_ty,
        };
        let absent = HirExpr {
            kind: HirExprKind::Nil,
            ty: TypeId::NIL,
        };

        Ok(HirExpr {
            kind: HirExprKind::LetIn {
                local_idx: subject_idx,
                value: Box::new(expr_hir),
                body: Box::new(HirExpr {
                    kind: HirExprKind::If {
                        condition: Box::new(condition),
                        then_branch: Box::new(present),
                        else_branch: Some(Box::new(absent)),
                    },
                    ty: payload_ty,
                }),
            },
            ty: payload_ty,
        })
    }

    /// Lower a try expression (expr?) to HIR
    ///
    /// The `?` operator unwraps a Result type:
    /// - If Ok(value), evaluates to the payload
    /// - If Err(error), propagates the error (early return of the whole
    ///   Err-tagged value, unchanged)
    ///
    /// History: this used to lower to a bare `rt_enum_payload(expr)` — no
    /// discriminant test, no branch, no early return — so under the JIT an
    /// `Err` was silently unwrapped as if it were `Ok` and execution fell
    /// through with the ERROR payload bound as the success value. See
    /// `doc/08_tracking/bug/try_operator_early_return_matches_neither_ok_nor_err_2026-08-07.md`.
    ///
    /// Shape emitted now (mirrors `compile_try_unwrap` in
    /// `codegen/instr/result.rs` and the pure-Simple `lower_try_expr` in
    /// `src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl`):
    ///
    /// ```text
    /// LetIn tmp = <inner> in
    ///   if rt_enum_check_discriminant(tmp, disc("Err")):
    ///       return tmp            // early-return the Err as-is
    ///   else:
    ///       rt_enum_payload(tmp)  // Ok payload
    /// ```
    ///
    /// The subject is bound to a `LetIn` temp so a side-effecting operand
    /// (`f()?`) is evaluated exactly once; the discriminant test, the early
    /// return, and the unwrap all read the temp. The discriminant constant
    /// uses the same hashed-variant-name convention as enum `match` lowering
    /// above (and as `create_enum_value` at construction) — the proven-correct
    /// path, since a hand-written `case Err(e)` always matched.
    ///
    /// SCOPE: `Result` ONLY. The `"Err"` discriminant above is computed from a
    /// string literal UNCONDITIONALLY, with no branch on the subject's type, so
    /// for an `Option` the test is false for BOTH `Some` and `None`: `None?`
    /// neither early-returns nor yields a value that matches either variant. The
    /// "mirrors the pure-Simple `lower_try_expr`" claim above therefore holds for
    /// `Result` only — that lowering has a dedicated `case HirTypeKind.Optional`
    /// arm (presence via `rt_enum_discriminant`/`rt_is_some`, both the flat-
    /// nullable and boxed physical reps, `None`-handle promotion before the early
    /// return) which this function has no equivalent of. Tracked in
    /// `doc/08_tracking/bug/try_operator_on_option_no_early_return_2026-08-08.md`.
    /// Guard for the Result half (the spec DSL cannot reach this lowering):
    /// `scripts/check/check-try-operator-error-propagation.shs`.
    pub(super) fn lower_try(&mut self, inner: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        // Lower the inner expression once and bind it to a temp.
        let inner_hir = self.lower_expr(inner, ctx)?;
        let subject_ty = inner_hir.ty;

        // A nullable SCALAR (`i64?`, `f64?`, `bool?`, `text?`) is not a
        // Result/Option enum: it lowers to `HirType::Pointer { inner }` and its
        // runtime value is the tagged payload itself, with nil as the absent
        // case. Routing it through `rt_enum_payload` below asked a non-enum for
        // its payload, which answers `rt_core_nil()` — so `x!` on a plainly
        // non-nil `i64? = 42` evaluated to `nil`.
        // Bug: doc/08_tracking/bug/jit_optional_i64_payload_reinterpreted_2026-08-17.md
        // The tagged word IS the payload here (this is the same "bare/flat-
        // nullable payload convention" `rt_unwrap_or_value` already documents),
        // so unwrapping is the identity on the value and only the static type
        // narrows from `T?` to `T`.
        if self.result_like_payload_type(subject_ty).is_none() {
            if let Some(HirType::Pointer { inner: pointee, .. }) = self.module.types.get(subject_ty) {
                let pointee = *pointee;
                if matches!(
                    pointee,
                    TypeId::BOOL
                        | TypeId::I8
                        | TypeId::I16
                        | TypeId::I32
                        | TypeId::I64
                        | TypeId::U8
                        | TypeId::U16
                        | TypeId::U32
                        | TypeId::U64
                        | TypeId::F32
                        | TypeId::F64
                        | TypeId::STRING
                ) {
                    // Type it `ANY`, not `pointee`: the runtime word is still a
                    // TAGGED RuntimeValue, and claiming the raw scalar type here
                    // would make the next consumer read `42 << 3` as a raw int.
                    // `ANY` is what every other tagged-value producer reports.
                    let _ = pointee;
                    return Ok(HirExpr {
                        kind: inner_hir.kind,
                        ty: TypeId::ANY,
                    });
                }
            }
        }

        let payload_ty = self.result_like_payload_type(subject_ty).unwrap_or(TypeId::ANY);

        let subject_idx = ctx.locals.len();
        ctx.add_local("$try_subject".to_string(), subject_ty, Mutability::Immutable);
        let subject_ref = HirExpr {
            kind: HirExprKind::Local(subject_idx),
            ty: subject_ty,
        };

        // Hashed "Err" discriminant — same convention as match lowering.
        let err_disc: i64 = {
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};
            let mut hasher = DefaultHasher::new();
            "Err".hash(&mut hasher);
            (hasher.finish() & 0xFFFFFFFF) as i64
        };

        let is_err = HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: "rt_enum_check_discriminant".to_string(),
                args: vec![
                    subject_ref.clone(),
                    HirExpr {
                        kind: HirExprKind::Integer(err_disc),
                        ty: TypeId::I64,
                    },
                ],
            },
            ty: TypeId::BOOL,
        };

        // Early return of the whole Err-tagged value. A one-statement Block
        // holding a real `HirStmt::Return` preserves the terminator in
        // expression position — same device as the match-arm return fix above
        // (`finalize_block_jump`'s Unreachable-only guard keeps the enclosing
        // if-merge from clobbering it).
        let early_return = HirExpr {
            kind: HirExprKind::Block(vec![crate::hir::HirStmt::Return(Some(subject_ref.clone()))]),
            ty: payload_ty,
        };

        let unwrap_ok = HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: "rt_enum_payload".to_string(),
                args: vec![subject_ref],
            },
            ty: payload_ty,
        };

        Ok(HirExpr {
            kind: HirExprKind::LetIn {
                local_idx: subject_idx,
                value: Box::new(inner_hir),
                body: Box::new(HirExpr {
                    kind: HirExprKind::If {
                        condition: Box::new(is_err),
                        then_branch: Box::new(early_return),
                        else_branch: Some(Box::new(unwrap_ok)),
                    },
                    ty: payload_ty,
                }),
            },
            ty: payload_ty,
        })
    }

    /// Lower a range expression (start..end or start..=end) to HIR
    ///
    /// Ranges are represented as a builtin call that creates a Range object.
    /// The inclusive flag determines whether the end is included.
    pub(super) fn lower_range(
        &mut self,
        start: Option<&Expr>,
        end: Option<&Expr>,
        bound: simple_parser::ast::RangeBound,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Lower start and end expressions
        let start_hir = if let Some(s) = start {
            self.lower_expr(s, ctx)?
        } else {
            HirExpr {
                kind: HirExprKind::Integer(0),
                ty: TypeId::I64,
            }
        };

        let end_hir = if let Some(e) = end {
            self.lower_expr(e, ctx)?
        } else {
            // If no end, use a large value (or could return error)
            HirExpr {
                kind: HirExprKind::Integer(i64::MAX),
                ty: TypeId::I64,
            }
        };

        // Check if inclusive
        let inclusive = matches!(bound, simple_parser::ast::RangeBound::Inclusive);

        // Create a Range using a builtin call
        Ok(HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: if inclusive {
                    "rt_range_inclusive".to_string()
                } else {
                    "rt_range".to_string()
                },
                args: vec![start_hir, end_hir],
            },
            ty: TypeId::ANY, // Range type - could be more specific
        })
    }
}

/// Collect all identifiers used in an expression tree.
///
/// Walks the expression tree **and every statement form inside blocks**, and
/// collects the variable identifiers that are *free*: referenced without being
/// bound earlier inside the walked body by a `val`/`var`, a `for` binder, an
/// `if let`/`while let` pattern, a match-arm pattern, a `with ... as` name, or a
/// nested lambda parameter. Used for lambda capture optimization.
///
/// History: this walker used to descend only into `Node::Expression` statements
/// and had no `Expr::DoBlock` arm at all, so a `fn(): ...` block body captured
/// nothing and outer locals silently lowered to `0` under the JIT. See
/// `doc/08_tracking/bug/closure_selective_capture_skips_non_expression_statements_2026-07-27.md`.
///
/// Over-capturing is harmless (the filter is only an optimisation);
/// under-capturing is a correctness bug. Shadowing is honoured *sequentially*,
/// so `val x = x` still counts the outer `x` as used by its own initializer.
fn collect_used_identifiers(expr: &Expr) -> HashSet<String> {
    let mut identifiers = HashSet::new();
    let mut bound: Vec<String> = Vec::new();
    collect_identifiers_recursive(expr, &mut bound, &mut identifiers);
    identifiers
}

/// Record `name` as used unless a binder inside the walked body owns it.
fn note_used_identifier(name: &str, bound: &[String], identifiers: &mut HashSet<String>) {
    if !bound.iter().any(|b| b == name) {
        identifiers.insert(name.to_string());
    }
}

/// Add every name a pattern binds to `bound`; literal/range patterns instead
/// *read* their sub-expressions.
fn bind_pattern_identifiers(pattern: &Pattern, bound: &mut Vec<String>, identifiers: &mut HashSet<String>) {
    match pattern {
        Pattern::Identifier(name) | Pattern::MutIdentifier(name) | Pattern::MoveIdentifier(name) => {
            bound.push(name.clone());
        }
        Pattern::Tuple(pats) | Pattern::Array(pats) | Pattern::Or(pats) => {
            for p in pats {
                bind_pattern_identifiers(p, bound, identifiers);
            }
        }
        Pattern::Struct { fields, .. } => {
            for (_, p) in fields {
                bind_pattern_identifiers(p, bound, identifiers);
            }
        }
        Pattern::Enum {
            payload: Some(pats), ..
        } => {
            for p in pats {
                bind_pattern_identifiers(p, bound, identifiers);
            }
        }
        Pattern::Typed { pattern, .. } => bind_pattern_identifiers(pattern, bound, identifiers),
        Pattern::Literal(e) => collect_identifiers_recursive(e, bound, identifiers),
        Pattern::Range { start, end, .. } => {
            collect_identifiers_recursive(start, bound, identifiers);
            collect_identifiers_recursive(end, bound, identifiers);
        }
        Pattern::Wildcard | Pattern::Rest | Pattern::Enum { payload: None, .. } => {}
    }
}

/// Walk a statement list as a lexical scope: binders introduced inside it are
/// visible to the statements that follow, and dropped at the end of the block.
pub(crate) fn collect_identifiers_block(
    stmts: &[simple_parser::ast::Node],
    bound: &mut Vec<String>,
    identifiers: &mut HashSet<String>,
) {
    let mark = bound.len();
    for stmt in stmts {
        collect_identifiers_stmt(stmt, bound, identifiers);
    }
    bound.truncate(mark);
}

fn collect_identifiers_arms(arms: &[MatchArm], bound: &mut Vec<String>, identifiers: &mut HashSet<String>) {
    for arm in arms {
        let mark = bound.len();
        bind_pattern_identifiers(&arm.pattern, bound, identifiers);
        if let Some(guard) = &arm.guard {
            collect_identifiers_recursive(guard, bound, identifiers);
        }
        collect_identifiers_block(&arm.body.statements, bound, identifiers);
        bound.truncate(mark);
    }
}

fn collect_identifiers_defer(
    body: &simple_parser::ast::DeferBody,
    bound: &mut Vec<String>,
    identifiers: &mut HashSet<String>,
) {
    match body {
        simple_parser::ast::DeferBody::Expr(e) => collect_identifiers_recursive(e, bound, identifiers),
        simple_parser::ast::DeferBody::Block(b) => collect_identifiers_block(&b.statements, bound, identifiers),
    }
}

/// Walk a function body as a lexical scope: parameter defaults are evaluated in
/// the enclosing scope, the parameters themselves shadow it, and both are
/// dropped again at the end. Shared with the entry-script wrapper
/// (`pipeline::native_project::compiler`), which needs the same free-read set
/// for class/impl methods -- those reach this only as bare `FunctionDef`s, never
/// as a `Node::Function`.
pub(crate) fn collect_identifiers_function(
    f: &simple_parser::ast::FunctionDef,
    bound: &mut Vec<String>,
    identifiers: &mut HashSet<String>,
) {
    let mark = bound.len();
    for p in &f.params {
        if let Some(default) = &p.default {
            collect_identifiers_recursive(default, bound, identifiers);
        }
    }
    for p in &f.params {
        bound.push(p.name.clone());
    }
    collect_identifiers_block(&f.body.statements, bound, identifiers);
    bound.truncate(mark);
}

/// Walk a single statement, collecting free reads and registering its binders.
fn collect_identifiers_stmt(
    stmt: &simple_parser::ast::Node,
    bound: &mut Vec<String>,
    identifiers: &mut HashSet<String>,
) {
    use simple_parser::ast::Node;
    match stmt {
        Node::Expression(e) => collect_identifiers_recursive(e, bound, identifiers),
        Node::Let(l) => {
            // Initializer is evaluated BEFORE the binder exists: `val x = x`
            // reads the outer `x`.
            if let Some(v) = &l.value {
                collect_identifiers_recursive(v, bound, identifiers);
            }
            bind_pattern_identifiers(&l.pattern, bound, identifiers);
        }
        Node::Const(c) => {
            collect_identifiers_recursive(&c.value, bound, identifiers);
            bound.push(c.name.clone());
        }
        Node::Static(s) => {
            collect_identifiers_recursive(&s.value, bound, identifiers);
            bound.push(s.name.clone());
        }
        Node::Assignment(a) => {
            // The target counts as a read: compound ops (`x += 1`) read it, and
            // `x.f = v` / `x[i] = v` need the receiver present either way.
            collect_identifiers_recursive(&a.target, bound, identifiers);
            collect_identifiers_recursive(&a.value, bound, identifiers);
        }
        Node::Return(r) => {
            if let Some(v) = &r.value {
                collect_identifiers_recursive(v, bound, identifiers);
            }
        }
        Node::If(i) => {
            let mark = bound.len();
            collect_identifiers_recursive(&i.condition, bound, identifiers);
            if let Some(p) = &i.let_pattern {
                bind_pattern_identifiers(p, bound, identifiers);
            }
            collect_identifiers_block(&i.then_block.statements, bound, identifiers);
            bound.truncate(mark);
            for (pat, cond, blk) in &i.elif_branches {
                let elif_mark = bound.len();
                collect_identifiers_recursive(cond, bound, identifiers);
                if let Some(p) = pat {
                    bind_pattern_identifiers(p, bound, identifiers);
                }
                collect_identifiers_block(&blk.statements, bound, identifiers);
                bound.truncate(elif_mark);
            }
            if let Some(eb) = &i.else_block {
                collect_identifiers_block(&eb.statements, bound, identifiers);
            }
        }
        Node::Match(m) => {
            collect_identifiers_recursive(&m.subject, bound, identifiers);
            collect_identifiers_arms(&m.arms, bound, identifiers);
        }
        Node::For(f) => {
            collect_identifiers_recursive(&f.iterable, bound, identifiers);
            let mark = bound.len();
            bind_pattern_identifiers(&f.pattern, bound, identifiers);
            collect_identifiers_block(&f.body.statements, bound, identifiers);
            bound.truncate(mark);
        }
        Node::While(w) => {
            let mark = bound.len();
            collect_identifiers_recursive(&w.condition, bound, identifiers);
            if let Some(p) = &w.let_pattern {
                bind_pattern_identifiers(p, bound, identifiers);
            }
            collect_identifiers_block(&w.body.statements, bound, identifiers);
            bound.truncate(mark);
        }
        Node::Loop(l) => collect_identifiers_block(&l.body.statements, bound, identifiers),
        Node::Break(b) => {
            if let Some(v) = &b.value {
                collect_identifiers_recursive(v, bound, identifiers);
            }
        }
        Node::Defer(d) => collect_identifiers_defer(&d.body, bound, identifiers),
        Node::ErrDefer(d) => collect_identifiers_defer(&d.body, bound, identifiers),
        Node::Guard(g) => {
            if let Some(c) = &g.condition {
                collect_identifiers_recursive(c, bound, identifiers);
            }
            collect_identifiers_recursive(&g.result, bound, identifiers);
        }
        Node::Assert(a) => collect_identifiers_recursive(&a.condition, bound, identifiers),
        Node::Assume(a) => collect_identifiers_recursive(&a.condition, bound, identifiers),
        Node::Admit(a) => collect_identifiers_recursive(&a.condition, bound, identifiers),
        Node::Calc(c) => {
            for step in &c.steps {
                collect_identifiers_recursive(&step.expr, bound, identifiers);
            }
        }
        Node::Context(c) => {
            collect_identifiers_recursive(&c.context, bound, identifiers);
            collect_identifiers_block(&c.body.statements, bound, identifiers);
        }
        Node::With(w) => {
            collect_identifiers_recursive(&w.resource, bound, identifiers);
            let mark = bound.len();
            if let Some(n) = &w.name {
                bound.push(n.clone());
            }
            collect_identifiers_block(&w.body.statements, bound, identifiers);
            bound.truncate(mark);
        }
        Node::Function(f) => collect_identifiers_function(f, bound, identifiers),
        // Type/module declarations and no-op statements contribute no reads.
        _ => {}
    }
}

/// Recursively walk the expression tree and collect free identifiers.
fn collect_identifiers_recursive(expr: &Expr, bound: &mut Vec<String>, identifiers: &mut HashSet<String>) {
    match expr {
        Expr::Identifier(name) => {
            note_used_identifier(name, bound, identifiers);
        }
        Expr::Binary { left, right, .. } => {
            collect_identifiers_recursive(left, bound, identifiers);
            collect_identifiers_recursive(right, bound, identifiers);
        }
        Expr::Unary { operand, .. } => {
            collect_identifiers_recursive(operand, bound, identifiers);
        }
        Expr::Call { callee, args } => {
            collect_identifiers_recursive(callee, bound, identifiers);
            for arg in args {
                collect_identifiers_recursive(&arg.value, bound, identifiers);
            }
        }
        Expr::KernelLaunch {
            kernel,
            grid,
            block,
            args,
        } => {
            collect_identifiers_recursive(kernel, bound, identifiers);
            collect_identifiers_recursive(grid, bound, identifiers);
            collect_identifiers_recursive(block, bound, identifiers);
            for arg in args {
                collect_identifiers_recursive(&arg.value, bound, identifiers);
            }
        }
        Expr::MethodCall { receiver, args, .. } | Expr::OptionalMethodCall { receiver, args, .. } => {
            collect_identifiers_recursive(receiver, bound, identifiers);
            for arg in args {
                collect_identifiers_recursive(&arg.value, bound, identifiers);
            }
        }
        Expr::FieldAccess { receiver, .. } | Expr::TupleIndex { receiver, .. } => {
            collect_identifiers_recursive(receiver, bound, identifiers);
        }
        Expr::Index { receiver, index } => {
            collect_identifiers_recursive(receiver, bound, identifiers);
            collect_identifiers_recursive(index, bound, identifiers);
        }
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => {
            collect_identifiers_recursive(receiver, bound, identifiers);
            for part in [start, end, step].into_iter().flatten() {
                collect_identifiers_recursive(part, bound, identifiers);
            }
        }
        Expr::Tuple(exprs) | Expr::Array(exprs) | Expr::VecLiteral(exprs) => {
            for e in exprs {
                collect_identifiers_recursive(e, bound, identifiers);
            }
        }
        Expr::LabeledTuple(fields) => {
            for field in fields {
                collect_identifiers_recursive(&field.value, bound, identifiers);
            }
        }
        Expr::ArrayRepeat { value, count } => {
            collect_identifiers_recursive(value, bound, identifiers);
            collect_identifiers_recursive(count, bound, identifiers);
        }
        Expr::Dict(entries) => {
            for (k, v) in entries {
                collect_identifiers_recursive(k, bound, identifiers);
                collect_identifiers_recursive(v, bound, identifiers);
            }
        }
        Expr::ListComprehension {
            expr,
            pattern,
            iterable,
            condition,
        } => {
            collect_identifiers_recursive(iterable, bound, identifiers);
            let mark = bound.len();
            bind_pattern_identifiers(pattern, bound, identifiers);
            collect_identifiers_recursive(expr, bound, identifiers);
            if let Some(c) = condition {
                collect_identifiers_recursive(c, bound, identifiers);
            }
            bound.truncate(mark);
        }
        Expr::DictComprehension {
            key,
            value,
            pattern,
            iterable,
            condition,
        } => {
            collect_identifiers_recursive(iterable, bound, identifiers);
            let mark = bound.len();
            bind_pattern_identifiers(pattern, bound, identifiers);
            collect_identifiers_recursive(key, bound, identifiers);
            collect_identifiers_recursive(value, bound, identifiers);
            if let Some(c) = condition {
                collect_identifiers_recursive(c, bound, identifiers);
            }
            bound.truncate(mark);
        }
        Expr::If {
            let_pattern,
            condition,
            then_branch,
            else_branch,
        } => {
            let mark = bound.len();
            collect_identifiers_recursive(condition, bound, identifiers);
            if let Some(p) = let_pattern {
                bind_pattern_identifiers(p, bound, identifiers);
            }
            collect_identifiers_recursive(then_branch, bound, identifiers);
            bound.truncate(mark);
            if let Some(eb) = else_branch {
                collect_identifiers_recursive(eb, bound, identifiers);
            }
        }
        Expr::Lambda { params, body, .. } => {
            // Nested lambda params shadow the outer scope, so they are not free.
            let mark = bound.len();
            for p in params {
                bound.push(p.name.clone());
            }
            collect_identifiers_recursive(body, bound, identifiers);
            bound.truncate(mark);
        }
        Expr::Go { args, params, body } => {
            for a in args {
                collect_identifiers_recursive(a, bound, identifiers);
            }
            let mark = bound.len();
            for p in params {
                bound.push(p.clone());
            }
            collect_identifiers_recursive(body, bound, identifiers);
            bound.truncate(mark);
        }
        Expr::Cast { expr, .. }
        | Expr::CastOrReturn { expr, .. }
        | Expr::New { expr, .. }
        | Expr::ContractOld(expr)
        | Expr::Await(expr)
        | Expr::Try(expr)
        | Expr::ForceUnwrap(expr)
        | Expr::ExistsCheck(expr)
        | Expr::UnwrapOrReturn { expr, .. }
        | Expr::Spread(expr)
        | Expr::DictSpread(expr)
        | Expr::OptionalChain { expr, .. } => {
            collect_identifiers_recursive(expr, bound, identifiers);
        }
        Expr::UnwrapOr { expr, default } | Expr::CastOr { expr, default, .. } | Expr::Coalesce { expr, default } => {
            collect_identifiers_recursive(expr, bound, identifiers);
            collect_identifiers_recursive(default, bound, identifiers);
        }
        Expr::UnwrapElse { expr, fallback_fn } | Expr::CastElse { expr, fallback_fn, .. } => {
            collect_identifiers_recursive(expr, bound, identifiers);
            collect_identifiers_recursive(fallback_fn, bound, identifiers);
        }
        Expr::Range { start, end, .. } => {
            for part in [start, end].into_iter().flatten() {
                collect_identifiers_recursive(part, bound, identifiers);
            }
        }
        Expr::FunctionalUpdate { target, args, .. } => {
            collect_identifiers_recursive(target, bound, identifiers);
            for arg in args {
                collect_identifiers_recursive(&arg.value, bound, identifiers);
            }
        }
        Expr::FString { parts, .. } => {
            for part in parts {
                match part {
                    simple_parser::FStringPart::Expr(e) | simple_parser::FStringPart::ExprWithFormat(e, _) => {
                        collect_identifiers_recursive(e, bound, identifiers);
                    }
                    _ => {}
                }
            }
        }
        Expr::StructInit { fields, spread, .. } => {
            for (_, value) in fields {
                collect_identifiers_recursive(value, bound, identifiers);
            }
            if let Some(s) = spread {
                collect_identifiers_recursive(s, bound, identifiers);
            }
        }
        Expr::Yield(Some(v)) => {
            collect_identifiers_recursive(v, bound, identifiers);
        }
        Expr::Yield(None) => {}
        Expr::Spawn(inner) => {
            collect_identifiers_recursive(inner, bound, identifiers);
        }
        Expr::Forall {
            pattern,
            range,
            predicate,
        }
        | Expr::Exists {
            pattern,
            range,
            predicate,
        } => {
            collect_identifiers_recursive(range, bound, identifiers);
            let mark = bound.len();
            bind_pattern_identifiers(pattern, bound, identifiers);
            collect_identifiers_recursive(predicate, bound, identifiers);
            bound.truncate(mark);
        }
        Expr::Match { subject, arms } => {
            collect_identifiers_recursive(subject, bound, identifiers);
            collect_identifiers_arms(arms, bound, identifiers);
        }
        Expr::DoBlock(nodes) | Expr::UnsafeBlock(nodes) => {
            collect_identifiers_block(nodes, bound, identifiers);
        }
        // Literals and other expressions that don't contain identifiers
        _ => {}
    }
}

/// Discriminant name of a `Pattern`, for the default-off pattern-lowering probe.
pub(crate) fn pattern_kind_name(pattern: &Pattern) -> &'static str {
    match pattern {
        Pattern::Wildcard => "Wildcard",
        Pattern::Identifier(_) => "Identifier",
        Pattern::MutIdentifier(_) => "MutIdentifier",
        Pattern::MoveIdentifier(_) => "MoveIdentifier",
        Pattern::Literal(_) => "Literal",
        Pattern::Tuple(_) => "Tuple",
        Pattern::Array(_) => "Array",
        Pattern::Struct { .. } => "Struct",
        Pattern::Enum { .. } => "Enum",
        Pattern::Or(_) => "Or",
        Pattern::Typed { .. } => "Typed",
        Pattern::Range { .. } => "Range",
        Pattern::Rest => "Rest",
    }
}

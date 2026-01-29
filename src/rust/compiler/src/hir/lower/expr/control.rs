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
    /// Lower an if expression to HIR
    ///
    /// Result type is taken from the then branch.
    /// Else branch is optional.
    pub(super) fn lower_if(
        &mut self,
        condition: &Expr,
        then_branch: &Expr,
        else_branch: Option<&Expr>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let cond_hir = Box::new(self.lower_expr(condition, ctx)?);
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

    /// Lower a lambda expression to HIR
    ///
    /// Captures variables based on capture_all flag:
    /// - true: captures all immutable variables from outer scope
    /// - false: only captures variables explicitly used in body
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

        // Add lambda parameters to context as locals for body lowering
        let saved_locals_len = ctx.locals.len();
        for (name, ty) in &param_info {
            ctx.add_local(name.clone(), *ty, simple_parser::ast::Mutability::Immutable);
        }

        // Lower the lambda body with access to parameters
        let body_hir = Box::new(self.lower_expr(body, ctx)?);
        let body_ty = body_hir.ty;

        // Restore context (remove lambda parameters)
        ctx.locals.truncate(saved_locals_len);
        // Also need to remove from local_map
        for (name, _) in &param_info {
            ctx.local_map.remove(name);
        }

        Ok(HirExpr {
            kind: HirExprKind::Lambda {
                params: param_info,
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
        let result = self.lower_match_arms(subject_idx, subject_ty, arms, ctx)?;

        Ok(result)
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
        if matches!(&arm.pattern, Pattern::Wildcard | Pattern::Identifier(_)) {
            // Wildcard or binding pattern - just execute the body
            return self.lower_match_arm_body(&arm.body, ctx);
        }

        // Generate the condition for this pattern
        let condition = self.lower_pattern_condition(subject_idx, subject_ty, &arm.pattern, ctx)?;

        // Extract pattern bindings and add them to context
        // This needs to happen after pattern condition but before guard/body
        let bindings = self.extract_pattern_bindings(&arm.pattern, subject_ty);
        for (name, ty) in &bindings {
            ctx.add_local(name.clone(), *ty, simple_parser::ast::Mutability::Immutable);
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

        // Lower the arm body with bindings in scope
        let then_branch = self.lower_match_arm_body(&arm.body, ctx)?;
        let then_ty = then_branch.ty;

        // Restore context (remove pattern bindings from name scope only)
        // Keep locals in ctx.locals so they get proper indices in the final function.
        // Truncating would cause local_index references in HIR stmts to be out of bounds.
        for (name, _) in &bindings {
            ctx.local_map.remove(name);
        }

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
            Pattern::Wildcard | Pattern::Identifier(_) => {
                // Always matches
                Ok(HirExpr {
                    kind: HirExprKind::Bool(true),
                    ty: TypeId::BOOL,
                })
            }
            Pattern::Literal(lit_expr) => {
                // Compare subject == literal
                let lit_hir = self.lower_expr(lit_expr, ctx)?;

                // Check if subject or literal is a string type - use rt_string_eq for string comparison
                // Also check CHAR and ANY since string indexing returns single-char strings
                // and the literal may be a string (e.g., char literals like '(' are strings)
                let is_string =
                    subject_ty == TypeId::STRING
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
            // For more complex patterns (struct, tuple, array), return false for now
            _ => {
                eprintln!("[WARN] unimplemented pattern-to-expr lowering for: {:?}", pattern);
                Ok(HirExpr {
                    kind: HirExprKind::Bool(false),
                    ty: TypeId::BOOL,
                })
            }
        }
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

    /// Recursively collect bindings from a pattern
    fn collect_pattern_bindings(&self, pattern: &Pattern, expected_ty: TypeId, bindings: &mut Vec<(String, TypeId)>) {
        match pattern {
            Pattern::Identifier(name) => {
                // Variable binding - use expected type
                bindings.push((name.clone(), expected_ty));
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
                    let field_types = self.get_enum_variant_field_types_with_hint(enum_name, variant_name, expected_ty);

                    for (i, p) in patterns.iter().enumerate() {
                        let field_ty = field_types
                            .as_ref()
                            .and_then(|types| types.get(i).copied())
                            .unwrap_or(TypeId::ANY);
                        self.collect_pattern_bindings(p, field_ty, bindings);
                    }
                }
            }
            Pattern::Struct { name: _, fields } => {
                // Struct pattern like Point { x, y }
                for (_field_name, field_pattern) in fields {
                    self.collect_pattern_bindings(field_pattern, TypeId::ANY, bindings);
                }
            }
            Pattern::Array(patterns) => {
                for p in patterns {
                    self.collect_pattern_bindings(p, TypeId::ANY, bindings);
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
                if let Some(expr) = &ret_stmt.value {
                    return self.lower_expr(expr, ctx);
                } else {
                    return Ok(HirExpr {
                        kind: HirExprKind::Nil,
                        ty: TypeId::NIL,
                    });
                }
            }
        }

        // For multiple statements, we need to lower them all and return the last value
        // For now, just look for the last expression or return
        let mut last_expr = HirExpr {
            kind: HirExprKind::Nil,
            ty: TypeId::NIL,
        };

        for stmt in &body.statements {
            match stmt {
                simple_parser::ast::Node::Expression(expr) => {
                    last_expr = self.lower_expr(expr, ctx)?;
                }
                simple_parser::ast::Node::Return(ret_stmt) => {
                    if let Some(expr) = &ret_stmt.value {
                        last_expr = self.lower_expr(expr, ctx)?;
                    } else {
                        last_expr = HirExpr {
                            kind: HirExprKind::Nil,
                            ty: TypeId::NIL,
                        };
                    }
                }
                // Handle Let statements to add local variables
                simple_parser::ast::Node::Let(let_stmt) => {
                    // Lower the initializer expression (if present)
                    let init_ty = if let Some(ref value) = let_stmt.value {
                        let init_expr = self.lower_expr(value, ctx)?;
                        init_expr.ty
                    } else {
                        TypeId::NIL
                    };

                    // Extract variable name from pattern
                    if let simple_parser::ast::Pattern::Identifier(name) = &let_stmt.pattern {
                        // Add the variable to the context
                        ctx.add_local(name.clone(), init_ty, let_stmt.mutability);
                        // The let statement doesn't produce a value itself
                    } else if let simple_parser::ast::Pattern::MutIdentifier(name) = &let_stmt.pattern {
                        ctx.add_local(name.clone(), init_ty, simple_parser::ast::Mutability::Mutable);
                    }
                    // Other patterns (typed, tuple, etc.) would need more complex handling
                }
                // Skip other statement types for now
                _ => {}
            }
        }

        Ok(last_expr)
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

        // For multiple statements, evaluate each expression and return the last result
        // TODO: Full statement support would require exposing lower_node or creating a block HIR node
        let mut last_expr = HirExpr {
            kind: HirExprKind::Nil,
            ty: TypeId::NIL,
        };

        for stmt in statements {
            match stmt {
                simple_parser::ast::Node::Expression(expr) => {
                    last_expr = self.lower_expr(expr, ctx)?;
                }
                simple_parser::ast::Node::Return(ret_stmt) => {
                    if let Some(expr) = &ret_stmt.value {
                        last_expr = self.lower_expr(expr, ctx)?;
                    } else {
                        last_expr = HirExpr {
                            kind: HirExprKind::Nil,
                            ty: TypeId::NIL,
                        };
                    }
                }
                _ => {
                    // Other statement types are not yet supported in do blocks
                }
            }
        }

        Ok(last_expr)
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

        Ok(HirExpr {
            kind: HirExprKind::If {
                condition: Box::new(condition),
                then_branch: Box::new(unwrapped_expr),
                else_branch: Some(Box::new(default_hir)),
            },
            ty: result_ty,
        })
    }

    /// Lower an existence check expression (expr.?) to HIR
    ///
    /// The `.?` operator checks if a value is "present":
    /// - For Option types: true if Some, false if None
    /// - For collections: true if non-empty, false if empty
    /// - For Result types: use result.ok.? or result.err.?
    /// - For primitives: always true (they always exist)
    ///
    /// This is lowered to a nil check: `expr != nil`
    /// For more sophisticated checks (e.g., empty collections), the interpreter
    /// handles this at runtime through the appropriate FFI calls.
    pub(super) fn lower_exists_check(&mut self, expr: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        let expr_hir = self.lower_expr(expr, ctx)?;

        // Create a nil check: expr != nil
        let nil_expr = HirExpr {
            kind: HirExprKind::Nil,
            ty: TypeId::NIL,
        };

        Ok(HirExpr {
            kind: HirExprKind::Binary {
                op: BinOp::NotEq,
                left: Box::new(expr_hir),
                right: Box::new(nil_expr),
            },
            ty: TypeId::BOOL,
        })
    }

    /// Lower a try expression (expr?) to HIR
    ///
    /// The `?` operator unwraps a Result type:
    /// - If Ok(value), returns the value
    /// - If Err(error), propagates the error (early return)
    ///
    /// For native compilation, we simplify this to just unwrapping the value.
    /// The actual error propagation would require more complex control flow
    /// (generating early returns), which we'll implement in a future phase.
    ///
    /// For now, this is equivalent to calling .unwrap() on the result.
    pub(super) fn lower_try(&mut self, inner: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        // Lower the inner expression
        let inner_hir = self.lower_expr(inner, ctx)?;

        // Generate an unwrap call on the result
        // This uses the MethodCall HIR node with dynamic dispatch
        Ok(HirExpr {
            kind: HirExprKind::MethodCall {
                receiver: Box::new(inner_hir),
                method: "unwrap".to_string(),
                args: vec![],
                dispatch: DispatchMode::Dynamic,
            },
            ty: TypeId::ANY, // The unwrapped type is dynamically determined
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
/// This function walks the expression tree and collects all variable
/// identifiers that are referenced. Used for lambda capture optimization.
fn collect_used_identifiers(expr: &Expr) -> HashSet<String> {
    let mut identifiers = HashSet::new();
    collect_identifiers_recursive(expr, &mut identifiers);
    identifiers
}

/// Recursively walk the expression tree and collect identifiers.
fn collect_identifiers_recursive(expr: &Expr, identifiers: &mut HashSet<String>) {
    match expr {
        Expr::Identifier(name) => {
            identifiers.insert(name.clone());
        }
        Expr::Binary { left, right, .. } => {
            collect_identifiers_recursive(left, identifiers);
            collect_identifiers_recursive(right, identifiers);
        }
        Expr::Unary { operand, .. } => {
            collect_identifiers_recursive(operand, identifiers);
        }
        Expr::Call { callee, args } => {
            collect_identifiers_recursive(callee, identifiers);
            for arg in args {
                collect_identifiers_recursive(&arg.value, identifiers);
            }
        }
        Expr::MethodCall { receiver, args, .. } => {
            collect_identifiers_recursive(receiver, identifiers);
            for arg in args {
                collect_identifiers_recursive(&arg.value, identifiers);
            }
        }
        Expr::FieldAccess { receiver, .. } => {
            collect_identifiers_recursive(receiver, identifiers);
        }
        Expr::Index { receiver, index } => {
            collect_identifiers_recursive(receiver, identifiers);
            collect_identifiers_recursive(index, identifiers);
        }
        Expr::Tuple(exprs) | Expr::Array(exprs) | Expr::VecLiteral(exprs) => {
            for e in exprs {
                collect_identifiers_recursive(e, identifiers);
            }
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            collect_identifiers_recursive(condition, identifiers);
            collect_identifiers_recursive(then_branch, identifiers);
            if let Some(eb) = else_branch {
                collect_identifiers_recursive(eb, identifiers);
            }
        }
        Expr::Lambda { body, .. } => {
            // Note: We don't exclude lambda params here since they shadow outer scope
            // The actual capture filtering happens when we compare against ctx.locals
            collect_identifiers_recursive(body, identifiers);
        }
        Expr::Cast { expr, .. } => {
            collect_identifiers_recursive(expr, identifiers);
        }
        Expr::FString { parts, .. } => {
            for part in parts {
                if let simple_parser::FStringPart::Expr(e) = part {
                    collect_identifiers_recursive(&e, identifiers);
                }
            }
        }
        Expr::StructInit { fields, .. } => {
            for (_, value) in fields {
                collect_identifiers_recursive(value, identifiers);
            }
        }
        Expr::New { expr, .. } => {
            collect_identifiers_recursive(expr, identifiers);
        }
        Expr::Yield(value) => {
            if let Some(v) = value {
                collect_identifiers_recursive(v, identifiers);
            }
        }
        Expr::Spawn(inner) => {
            collect_identifiers_recursive(inner, identifiers);
        }
        Expr::Match { subject, arms } => {
            collect_identifiers_recursive(subject, identifiers);
            for arm in arms {
                if let Some(guard) = &arm.guard {
                    collect_identifiers_recursive(guard, identifiers);
                }
                for stmt in &arm.body.statements {
                    if let simple_parser::ast::Node::Expression(e) = stmt {
                        collect_identifiers_recursive(e, identifiers);
                    }
                }
            }
        }
        // Literals and other expressions that don't contain identifiers
        _ => {}
    }
}

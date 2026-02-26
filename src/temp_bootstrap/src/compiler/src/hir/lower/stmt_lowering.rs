use simple_parser::ast::{Mutability, RangeBound};
use simple_parser::{self as ast, Expr, Node, Pattern};

use super::context::FunctionContext;
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;
use super::super::types::*;

/// Calculate discriminant hash for enum variant name (same as expr_lowering.rs)
fn calculate_variant_discriminant(variant_name: &str) -> u32 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut hasher = DefaultHasher::new();
    variant_name.hash(&mut hasher);
    (hasher.finish() & 0xFFFFFFFF) as u32
}

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

                // Try to extract a simple name from the pattern
                if let Some(name) = Self::extract_pattern_name(&let_stmt.pattern) {
                    let local_index = ctx.add_local(name, ty, let_stmt.mutability);
                    Ok(vec![HirStmt::Let {
                        local_index,
                        ty,
                        value,
                    }])
                } else {
                    // Complex pattern (e.g., tuple destructuring)
                    // Lower RHS into a temp, then create locals for each element
                    let mut stmts = Vec::new();
                    let uid = ctx.locals.len();

                    // Store the RHS in a temporary
                    let temp_name = format!("_destr_{}", uid);
                    let temp_local = ctx.add_local(temp_name, TypeId::I64, Mutability::Immutable);
                    stmts.push(HirStmt::Let {
                        local_index: temp_local,
                        ty: TypeId::I64,
                        value,
                    });

                    // Destructure based on pattern type
                    self.lower_let_pattern_binding(
                        &let_stmt.pattern,
                        temp_local,
                        let_stmt.mutability,
                        ctx,
                        &mut stmts,
                    )?;

                    Ok(stmts)
                }
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
                Ok(vec![HirStmt::While { condition, body, increment: vec![] }])
            }

            Node::Loop(loop_stmt) => {
                let body = self.lower_block(&loop_stmt.body, ctx)?;
                Ok(vec![HirStmt::Loop { body }])
            }

            Node::For(for_stmt) => self.lower_for_loop(for_stmt, ctx),

            Node::Break(_) => Ok(vec![HirStmt::Break]),
            Node::Continue(_) => Ok(vec![HirStmt::Continue]),

            Node::Expression(expr) => {
                let hir_expr = self.lower_expr(expr, ctx)?;
                Ok(vec![HirStmt::Expr(hir_expr)])
            }

            Node::Match(match_stmt) => {
                // Lower match statement as a chain of if/else statements
                let subject_hir = self.lower_expr(&match_stmt.subject, ctx)?;
                let subject_ty = subject_hir.ty;

                // Store subject in a temporary local
                let temp_name = format!("_match_subj_{}", ctx.locals.len());
                let temp_idx = ctx.add_local(temp_name, subject_ty, Mutability::Immutable);
                let temp_local = HirExpr {
                    kind: HirExprKind::Local(temp_idx),
                    ty: subject_ty,
                };

                let mut stmts = vec![HirStmt::Let {
                    local_index: temp_idx,
                    ty: subject_ty,
                    value: Some(subject_hir),
                }];

                // Build if/else chain from the arms
                let mut else_block: Option<Vec<HirStmt>> = None;

                for arm in match_stmt.arms.iter().rev() {
                    // Register pattern binding locals BEFORE lowering body
                    // so that references to payload variables resolve correctly
                    let mut binding_info: Vec<(usize, usize)> = Vec::new(); // (local_idx, payload_index)
                    let payload_count;
                    if let simple_parser::Pattern::Enum { payload, .. } = &arm.pattern {
                        if let Some(payload_patterns) = payload {
                            payload_count = payload_patterns.len();
                            for (i, pat) in payload_patterns.iter().enumerate() {
                                if let Some(name) = Self::extract_pattern_name(pat) {
                                    let local_idx = ctx.add_local(name, TypeId::I64, Mutability::Immutable);
                                    binding_info.push((local_idx, i));
                                }
                            }
                        } else {
                            payload_count = 0;
                        }
                    } else if let simple_parser::Pattern::Identifier(name) = &arm.pattern {
                        // Bind the entire subject to the identifier
                        payload_count = 0;
                        let local_idx = ctx.add_local(name.clone(), TypeId::I64, Mutability::Immutable);
                        binding_info.push((local_idx, usize::MAX)); // MAX signals "bind whole subject"
                    } else {
                        payload_count = 0;
                    }

                    let mut body = self.lower_block(&arm.body, ctx)?;

                    // Prepend Let statements for pattern bindings
                    if !binding_info.is_empty() {
                        let mut bindings = Vec::new();
                        for &(local_idx, payload_index) in &binding_info {
                            let value_expr = if payload_index == usize::MAX {
                                // Identifier pattern: bind the whole subject
                                temp_local.clone()
                            } else if payload_count == 1 {
                                // Single payload: rt_enum_payload(subject)
                                HirExpr {
                                    kind: HirExprKind::BuiltinCall {
                                        name: "rt_enum_payload".to_string(),
                                        args: vec![temp_local.clone()],
                                    },
                                    ty: TypeId::I64,
                                }
                            } else {
                                // Multi payload: rt_object_field_get(rt_enum_payload(subject), i*8)
                                HirExpr {
                                    kind: HirExprKind::BuiltinCall {
                                        name: "rt_object_field_get".to_string(),
                                        args: vec![
                                            HirExpr {
                                                kind: HirExprKind::BuiltinCall {
                                                    name: "rt_enum_payload".to_string(),
                                                    args: vec![temp_local.clone()],
                                                },
                                                ty: TypeId::I64,
                                            },
                                            HirExpr {
                                                kind: HirExprKind::Integer((payload_index * 8) as i64),
                                                ty: TypeId::I64,
                                            },
                                        ],
                                    },
                                    ty: TypeId::I64,
                                }
                            };
                            bindings.push(HirStmt::Let {
                                local_index: local_idx,
                                ty: TypeId::I64,
                                value: Some(value_expr),
                            });
                        }
                        // Prepend bindings before the body
                        bindings.append(&mut body);
                        body = bindings;
                    }

                    let condition = match &arm.pattern {
                        simple_parser::Pattern::Wildcard => {
                            // Always matches
                            None
                        }
                        simple_parser::Pattern::Identifier(name) if name.chars().next().map_or(false, |c| c.is_uppercase()) => {
                            // Uppercase identifier = unit enum variant (NilLit, Error, etc.)
                            let disc_hash = calculate_variant_discriminant(name) as i64;
                            let enum_cond = HirExpr {
                                kind: HirExprKind::Binary {
                                    op: BinOp::Is,
                                    left: Box::new(HirExpr {
                                        kind: HirExprKind::BuiltinCall {
                                            name: "rt_enum_discriminant".to_string(),
                                            args: vec![temp_local.clone()],
                                        },
                                        ty: TypeId::I64,
                                    }),
                                    right: Box::new(HirExpr {
                                        kind: HirExprKind::Integer(disc_hash),
                                        ty: TypeId::I64,
                                    }),
                                },
                                ty: TypeId::BOOL,
                            };
                            let variant_str = format!("_::{}", name);
                            let int_tag_cond = HirExpr {
                                kind: HirExprKind::Binary {
                                    op: BinOp::Is,
                                    left: Box::new(temp_local.clone()),
                                    right: Box::new(HirExpr {
                                        kind: HirExprKind::Global(variant_str),
                                        ty: TypeId::I64,
                                    }),
                                },
                                ty: TypeId::BOOL,
                            };
                            Some(HirExpr {
                                kind: HirExprKind::Binary {
                                    op: BinOp::Or,
                                    left: Box::new(enum_cond),
                                    right: Box::new(int_tag_cond),
                                },
                                ty: TypeId::BOOL,
                            })
                        }
                        simple_parser::Pattern::Identifier(_) => {
                            // Lowercase binding pattern — always matches
                            None
                        }
                        simple_parser::Pattern::Literal(lit_expr) => {
                            let lit_hir = self.lower_expr(lit_expr, ctx)?;
                            Some(HirExpr {
                                kind: HirExprKind::Binary {
                                    op: BinOp::Eq,
                                    left: Box::new(temp_local.clone()),
                                    right: Box::new(lit_hir),
                                },
                                ty: TypeId::BOOL,
                            })
                        }
                        simple_parser::Pattern::Enum { name, variant, .. } => {
                            // Two-way comparison for both enum discriminants AND integer tags:
                            // (rt_enum_discriminant(subject) == hash("Variant")) OR (subject == Variant_global)
                            let disc_hash = calculate_variant_discriminant(variant) as i64;
                            let enum_cond = HirExpr {
                                kind: HirExprKind::Binary {
                                    op: BinOp::Is,
                                    left: Box::new(HirExpr {
                                        kind: HirExprKind::BuiltinCall {
                                            name: "rt_enum_discriminant".to_string(),
                                            args: vec![temp_local.clone()],
                                        },
                                        ty: TypeId::I64,
                                    }),
                                    right: Box::new(HirExpr {
                                        kind: HirExprKind::Integer(disc_hash),
                                        ty: TypeId::I64,
                                    }),
                                },
                                ty: TypeId::BOOL,
                            };
                            // Also try integer-tag comparison: subject == Global("Variant")
                            let variant_str = format!("{}::{}", name, variant);
                            let int_tag_cond = HirExpr {
                                kind: HirExprKind::Binary {
                                    op: BinOp::Is,
                                    left: Box::new(temp_local.clone()),
                                    right: Box::new(HirExpr {
                                        kind: HirExprKind::Global(variant_str),
                                        ty: TypeId::I64,
                                    }),
                                },
                                ty: TypeId::BOOL,
                            };
                            Some(HirExpr {
                                kind: HirExprKind::Binary {
                                    op: BinOp::Or,
                                    left: Box::new(enum_cond),
                                    right: Box::new(int_tag_cond),
                                },
                                ty: TypeId::BOOL,
                            })
                        }
                        simple_parser::Pattern::Or(patterns) => {
                            // Build: subject == p1 || subject == p2 || ...
                            let mut result: Option<HirExpr> = None;
                            for p in patterns {
                                let sub_cond = match p {
                                    simple_parser::Pattern::Literal(lit_expr) => {
                                        if let Ok(lit_hir) = self.lower_expr(lit_expr, ctx) {
                                            Some(HirExpr {
                                                kind: HirExprKind::Binary {
                                                    op: BinOp::Eq,
                                                    left: Box::new(temp_local.clone()),
                                                    right: Box::new(lit_hir),
                                                },
                                                ty: TypeId::BOOL,
                                            })
                                        } else {
                                            None
                                        }
                                    }
                                    simple_parser::Pattern::Enum { name, variant, .. } => {
                                        let disc_hash = calculate_variant_discriminant(variant) as i64;
                                        let enum_cond = HirExpr {
                                            kind: HirExprKind::Binary {
                                                op: BinOp::Is,
                                                left: Box::new(HirExpr {
                                                    kind: HirExprKind::BuiltinCall {
                                                        name: "rt_enum_discriminant".to_string(),
                                                        args: vec![temp_local.clone()],
                                                    },
                                                    ty: TypeId::I64,
                                                }),
                                                right: Box::new(HirExpr {
                                                    kind: HirExprKind::Integer(disc_hash),
                                                    ty: TypeId::I64,
                                                }),
                                            },
                                            ty: TypeId::BOOL,
                                        };
                                        let variant_str = format!("{}::{}", name, variant);
                                        let int_tag_cond = HirExpr {
                                            kind: HirExprKind::Binary {
                                                op: BinOp::Is,
                                                left: Box::new(temp_local.clone()),
                                                right: Box::new(HirExpr {
                                                    kind: HirExprKind::Global(variant_str),
                                                    ty: TypeId::I64,
                                                }),
                                            },
                                            ty: TypeId::BOOL,
                                        };
                                        Some(HirExpr {
                                            kind: HirExprKind::Binary {
                                                op: BinOp::Or,
                                                left: Box::new(enum_cond),
                                                right: Box::new(int_tag_cond),
                                            },
                                            ty: TypeId::BOOL,
                                        })
                                    }
                                    simple_parser::Pattern::Identifier(name) if name.chars().next().map_or(false, |c| c.is_uppercase()) => {
                                        // Uppercase identifier = unit enum variant in or-pattern
                                        let disc_hash = calculate_variant_discriminant(name) as i64;
                                        let enum_cond = HirExpr {
                                            kind: HirExprKind::Binary {
                                                op: BinOp::Is,
                                                left: Box::new(HirExpr {
                                                    kind: HirExprKind::BuiltinCall {
                                                        name: "rt_enum_discriminant".to_string(),
                                                        args: vec![temp_local.clone()],
                                                    },
                                                    ty: TypeId::I64,
                                                }),
                                                right: Box::new(HirExpr {
                                                    kind: HirExprKind::Integer(disc_hash),
                                                    ty: TypeId::I64,
                                                }),
                                            },
                                            ty: TypeId::BOOL,
                                        };
                                        let variant_str = format!("_::{}", name);
                                        let int_tag_cond = HirExpr {
                                            kind: HirExprKind::Binary {
                                                op: BinOp::Is,
                                                left: Box::new(temp_local.clone()),
                                                right: Box::new(HirExpr {
                                                    kind: HirExprKind::Global(variant_str),
                                                    ty: TypeId::I64,
                                                }),
                                            },
                                            ty: TypeId::BOOL,
                                        };
                                        Some(HirExpr {
                                            kind: HirExprKind::Binary {
                                                op: BinOp::Or,
                                                left: Box::new(enum_cond),
                                                right: Box::new(int_tag_cond),
                                            },
                                            ty: TypeId::BOOL,
                                        })
                                    }
                                    _ => None, // Wildcard in or-pattern
                                };
                                if let Some(cond) = sub_cond {
                                    result = Some(match result {
                                        Some(prev) => HirExpr {
                                            kind: HirExprKind::Binary {
                                                op: BinOp::Or,
                                                left: Box::new(prev),
                                                right: Box::new(cond),
                                            },
                                            ty: TypeId::BOOL,
                                        },
                                        None => cond,
                                    });
                                }
                            }
                            result // None means wildcard (if all sub-patterns were wildcards)
                        }
                        _ => {
                            // For other patterns, treat as always matching (bootstrap)
                            None
                        }
                    };

                    if let Some(cond) = condition {
                        else_block = Some(vec![HirStmt::If {
                            condition: cond,
                            then_block: body,
                            else_block,
                        }]);
                    } else {
                        // Wildcard/catch-all
                        else_block = Some(body);
                    }
                }

                if let Some(match_body) = else_block {
                    stmts.extend(match_body);
                }

                Ok(stmts)
            }

            Node::Const(const_stmt) => {
                // Lower const as a regular let binding (for bootstrap)
                let ty = if let Some(t) = &const_stmt.ty {
                    self.resolve_type(t)?
                } else {
                    self.infer_type(&const_stmt.value, ctx)?
                };
                let value = self.lower_expr(&const_stmt.value, ctx)?;
                let local_index = ctx.add_local(const_stmt.name.clone(), ty, Mutability::Immutable);
                Ok(vec![HirStmt::Let {
                    local_index,
                    ty,
                    value: Some(value),
                }])
            }

            Node::Static(static_stmt) => {
                // Lower static as a regular let binding (for bootstrap)
                let ty = if let Some(t) = &static_stmt.ty {
                    self.resolve_type(t)?
                } else {
                    self.infer_type(&static_stmt.value, ctx)?
                };
                let value = self.lower_expr(&static_stmt.value, ctx)?;
                let local_index = ctx.add_local(static_stmt.name.clone(), ty, static_stmt.mutability);
                Ok(vec![HirStmt::Let {
                    local_index,
                    ty,
                    value: Some(value),
                }])
            }

            // Use/import statements - skip in function-level lowering (module-level handles these)
            Node::UseStmt(_)
            | Node::CommonUseStmt(_)
            | Node::ExportUseStmt(_)
            | Node::AutoImportStmt(_)
            | Node::ModDecl(_) => Ok(vec![]),

            // Extern declarations - register as globals and skip (bootstrap)
            Node::Extern(ext) => {
                // Register extern function as a global with I64 type for bootstrap
                self.globals.insert(ext.name.clone(), TypeId::I64);
                Ok(vec![])
            }

            // Trait/Impl/Class/Struct/Enum/TypeAlias/Actor/Macro/Unit - skip at statement level
            Node::Trait(_)
            | Node::Impl(_)
            | Node::Class(_)
            | Node::Struct(_)
            | Node::Enum(_)
            | Node::TypeAlias(_)
            | Node::Actor(_)
            | Node::Macro(_)
            | Node::Unit(_)
            | Node::UnitFamily(_)
            | Node::Function(_)
            | Node::Context(_)
            | Node::With(_) => Ok(vec![]),

            _ => Err(LowerError::Unsupported(format!("{:?}", node))),
        }
    }

    /// Desugar a for-loop into a while-loop.
    ///
    /// Range-based (`for i in start..end:`) desugars to a counting while loop.
    /// Generic iterables (`for item in items:`) desugar to:
    /// ```
    /// var _iter_N = items
    /// var _idx_N = 0
    /// var _len_N = rt_len(_iter_N)
    /// while _idx_N < _len_N:
    ///     var item = rt_index_get(_iter_N, _idx_N)
    ///     ... body ...
    ///     _idx_N = _idx_N + 1
    /// ```
    fn lower_for_loop(
        &mut self,
        for_stmt: &ast::ForStmt,
        ctx: &mut FunctionContext,
    ) -> LowerResult<Vec<HirStmt>> {
        // Check if iterable is a range expression: start..end or start..=end
        match &for_stmt.iterable {
            Expr::Range { start, end, bound } => {
                // Extract the loop variable name from the pattern
                // For complex patterns (e.g., tuple), use a temp name
                let var_name = Self::extract_pattern_name(&for_stmt.pattern)
                    .unwrap_or_else(|| format!("_range_iter_{}", ctx.locals.len()));

                let mut stmts = Vec::new();

                // Lower start and end expressions
                let start_expr = if let Some(s) = start {
                    self.lower_expr(s, ctx)?
                } else {
                    HirExpr {
                        kind: HirExprKind::Integer(0),
                        ty: TypeId::I64,
                    }
                };

                let end_expr = if let Some(e) = end {
                    self.lower_expr(e, ctx)?
                } else {
                    return Err(LowerError::Unsupported(
                        "for loop with unbounded range".to_string(),
                    ));
                };

                let end_var_name = format!("_iter_end_{}", ctx.locals.len());
                let end_local = ctx.add_local(end_var_name.clone(), TypeId::I64, Mutability::Immutable);
                stmts.push(HirStmt::Let {
                    local_index: end_local,
                    ty: TypeId::I64,
                    value: Some(end_expr),
                });

                let iter_local = ctx.add_local(var_name.clone(), TypeId::I64, Mutability::Mutable);
                stmts.push(HirStmt::Let {
                    local_index: iter_local,
                    ty: TypeId::I64,
                    value: Some(start_expr),
                });

                let cmp_op = match bound {
                    RangeBound::Inclusive => BinOp::LtEq,
                    RangeBound::Exclusive => BinOp::Lt,
                };

                let condition = HirExpr {
                    kind: HirExprKind::Binary {
                        op: cmp_op,
                        left: Box::new(HirExpr {
                            kind: HirExprKind::Local(iter_local),
                            ty: TypeId::I64,
                        }),
                        right: Box::new(HirExpr {
                            kind: HirExprKind::Local(end_local),
                            ty: TypeId::I64,
                        }),
                    },
                    ty: TypeId::BOOL,
                };

                let body_stmts = self.lower_block(&for_stmt.body, ctx)?;

                let increment = vec![HirStmt::Assign {
                    target: HirExpr {
                        kind: HirExprKind::Local(iter_local),
                        ty: TypeId::I64,
                    },
                    value: HirExpr {
                        kind: HirExprKind::Binary {
                            op: BinOp::Add,
                            left: Box::new(HirExpr {
                                kind: HirExprKind::Local(iter_local),
                                ty: TypeId::I64,
                            }),
                            right: Box::new(HirExpr {
                                kind: HirExprKind::Integer(1),
                                ty: TypeId::I64,
                            }),
                        },
                        ty: TypeId::I64,
                    },
                }];

                stmts.push(HirStmt::While {
                    condition,
                    body: body_stmts,
                    increment,
                });

                Ok(stmts)
            }

            // Handle range(N) and range(start, end) function calls
            Expr::Call { callee, args } => {
                if let Expr::Identifier(name) = callee.as_ref() {
                    if name == "range" {
                        let var_name = Self::extract_pattern_name(&for_stmt.pattern)
                            .unwrap_or_else(|| format!("_range_iter_{}", ctx.locals.len()));
                        return self.lower_for_range_call(
                            &var_name, args, &for_stmt.body, ctx,
                        );
                    }
                }
                // Non-range call iterable: fall through to generic iterable lowering
                self.lower_for_generic_iterable(for_stmt, ctx)
            }

            // All other iterables: identifiers, field accesses, method calls, etc.
            _ => self.lower_for_generic_iterable(for_stmt, ctx),
        }
    }

    /// Lower a for-loop over a generic iterable (not a range) into a while-loop.
    ///
    /// `for item in items:` desugars to:
    /// ```
    /// var _iter_N = items
    /// var _idx_N = 0
    /// var _len_N = len(_iter_N)
    /// while _idx_N < _len_N:
    ///     var item = _iter_N[_idx_N]
    ///     ... body ...
    ///     _idx_N = _idx_N + 1
    /// ```
    fn lower_for_generic_iterable(
        &mut self,
        for_stmt: &ast::ForStmt,
        ctx: &mut FunctionContext,
    ) -> LowerResult<Vec<HirStmt>> {
        let mut stmts = Vec::new();
        let uid = ctx.locals.len();

        // Step 1: var _iter_N = <iterable>
        let iterable_expr = self.lower_expr(&for_stmt.iterable, ctx)?;
        let iter_ty = iterable_expr.ty;
        let elem_ty = self.get_index_element_type(iter_ty).unwrap_or(TypeId::I64);
        let iter_name = format!("_iter_{}", uid);
        let iter_local = ctx.add_local(iter_name, iter_ty, Mutability::Immutable);
        stmts.push(HirStmt::Let {
            local_index: iter_local,
            ty: iter_ty,
            value: Some(iterable_expr),
        });

        // Step 2: var _idx_N = 0
        let idx_name = format!("_idx_{}", uid);
        let idx_local = ctx.add_local(idx_name, TypeId::I64, Mutability::Mutable);
        stmts.push(HirStmt::Let {
            local_index: idx_local,
            ty: TypeId::I64,
            value: Some(HirExpr {
                kind: HirExprKind::Integer(0),
                ty: TypeId::I64,
            }),
        });

        // Step 3: var _len_N = len(_iter_N)
        let len_name = format!("_len_{}", uid);
        let len_local = ctx.add_local(len_name, TypeId::I64, Mutability::Immutable);
        stmts.push(HirStmt::Let {
            local_index: len_local,
            ty: TypeId::I64,
            value: Some(HirExpr {
                kind: HirExprKind::BuiltinCall {
                    name: "__spl_method_len".to_string(),
                    args: vec![HirExpr {
                        kind: HirExprKind::Local(iter_local),
                        ty: TypeId::I64,
                    }],
                },
                ty: TypeId::I64,
            }),
        });

        // Step 4: Build while condition: _idx_N < _len_N
        let condition = HirExpr {
            kind: HirExprKind::Binary {
                op: BinOp::Lt,
                left: Box::new(HirExpr {
                    kind: HirExprKind::Local(idx_local),
                    ty: TypeId::I64,
                }),
                right: Box::new(HirExpr {
                    kind: HirExprKind::Local(len_local),
                    ty: TypeId::I64,
                }),
            },
            ty: TypeId::BOOL,
        };

        // Step 5: Build loop body
        let mut body_stmts = Vec::new();

        // Get current element: _iter_N[_idx_N] via Index (rt_index_get)
        let elem_expr = HirExpr {
            kind: HirExprKind::Index {
                receiver: Box::new(HirExpr {
                    kind: HirExprKind::Local(iter_local),
                    ty: iter_ty,
                }),
                index: Box::new(HirExpr {
                    kind: HirExprKind::Local(idx_local),
                    ty: TypeId::I64,
                }),
            },
            ty: elem_ty,
        };

        // Bind the element to the pattern variable(s)
        // Pass iterable type so Dict tuple destructuring can use proper key/value types
        self.lower_for_pattern_binding(&for_stmt.pattern, elem_expr, ctx, &mut body_stmts, Some(iter_ty))?;

        // Lower the user's loop body
        body_stmts.extend(self.lower_block(&for_stmt.body, ctx)?);

        // Increment: _idx_N = _idx_N + 1 (separate from body for correct `continue`)
        let increment = vec![HirStmt::Assign {
            target: HirExpr {
                kind: HirExprKind::Local(idx_local),
                ty: TypeId::I64,
            },
            value: HirExpr {
                kind: HirExprKind::Binary {
                    op: BinOp::Add,
                    left: Box::new(HirExpr {
                        kind: HirExprKind::Local(idx_local),
                        ty: TypeId::I64,
                    }),
                    right: Box::new(HirExpr {
                        kind: HirExprKind::Integer(1),
                        ty: TypeId::I64,
                    }),
                },
                ty: TypeId::I64,
            },
        }];

        // Build while loop with separate increment
        stmts.push(HirStmt::While {
            condition,
            body: body_stmts,
            increment,
        });

        Ok(stmts)
    }

    /// Bind a for-loop pattern to the current element expression.
    /// `iter_ty` is the type of the iterable being looped over (used to extract Dict key/value types).
    fn lower_for_pattern_binding(
        &mut self,
        pattern: &Pattern,
        elem_expr: HirExpr,
        ctx: &mut FunctionContext,
        body_stmts: &mut Vec<HirStmt>,
        iter_ty: Option<TypeId>,
    ) -> LowerResult<()> {
        match pattern {
            Pattern::Identifier(name) => {
                let ty = elem_expr.ty;
                let local = ctx.add_local(name.clone(), ty, Mutability::Immutable);
                body_stmts.push(HirStmt::Let {
                    local_index: local,
                    ty,
                    value: Some(elem_expr),
                });
                Ok(())
            }
            Pattern::MutIdentifier(name) => {
                let local = ctx.add_local(name.clone(), TypeId::I64, Mutability::Mutable);
                body_stmts.push(HirStmt::Let {
                    local_index: local,
                    ty: TypeId::I64,
                    value: Some(elem_expr),
                });
                Ok(())
            }
            Pattern::Typed { pattern: inner, .. } => {
                self.lower_for_pattern_binding(inner, elem_expr, ctx, body_stmts, iter_ty)
            }
            Pattern::Tuple(elements) => {
                // Create intermediate: var _elem_N = <elem_expr>
                let uid = ctx.locals.len();
                let elem_name = format!("_elem_{}", uid);
                let elem_local = ctx.add_local(elem_name, TypeId::I64, Mutability::Immutable);
                body_stmts.push(HirStmt::Let {
                    local_index: elem_local,
                    ty: TypeId::I64,
                    value: Some(elem_expr),
                });

                // For Dict iteration with tuple pattern (key, value), use Dict's key/value types
                let dict_kv = iter_ty.and_then(|it| self.get_dict_kv_types(it));

                // Destructure: var a = _elem_N[0], var b = _elem_N[1], ...
                for (idx, sub_pattern) in elements.iter().enumerate() {
                    // Determine the type of this tuple element
                    let sub_ty = if let Some((key_ty, val_ty)) = dict_kv {
                        match idx {
                            0 => key_ty,   // Dict key
                            1 => val_ty,   // Dict value
                            _ => TypeId::I64,
                        }
                    } else {
                        TypeId::I64
                    };

                    let field_expr = HirExpr {
                        kind: HirExprKind::Index {
                            receiver: Box::new(HirExpr {
                                kind: HirExprKind::Local(elem_local),
                                ty: TypeId::I64,
                            }),
                            index: Box::new(HirExpr {
                                kind: HirExprKind::Integer(idx as i64),
                                ty: TypeId::I64,
                            }),
                        },
                        ty: sub_ty,
                    };
                    self.lower_for_pattern_binding(sub_pattern, field_expr, ctx, body_stmts, None)?;
                }
                Ok(())
            }
            Pattern::Wildcard => {
                let uid = ctx.locals.len();
                let discard_name = format!("_discard_{}", uid);
                let local = ctx.add_local(discard_name, TypeId::I64, Mutability::Immutable);
                body_stmts.push(HirStmt::Let {
                    local_index: local,
                    ty: TypeId::I64,
                    value: Some(elem_expr),
                });
                Ok(())
            }
            _ => {
                // Best effort: extract name or use temp
                let name = Self::extract_pattern_name(pattern)
                    .unwrap_or_else(|| format!("_for_elem_{}", ctx.locals.len()));
                let local = ctx.add_local(name, TypeId::I64, Mutability::Immutable);
                body_stmts.push(HirStmt::Let {
                    local_index: local,
                    ty: TypeId::I64,
                    value: Some(elem_expr),
                });
                Ok(())
            }
        }
    }

    /// Lower `for i in range(end):` or `for i in range(start, end):` to a while loop.
    fn lower_for_range_call(
        &mut self,
        var_name: &str,
        args: &[ast::Argument],
        body: &ast::Block,
        ctx: &mut FunctionContext,
    ) -> LowerResult<Vec<HirStmt>> {
        let mut stmts = Vec::new();

        let (start_expr, end_expr) = match args.len() {
            1 => {
                let end = self.lower_expr(&args[0].value, ctx)?;
                let start = HirExpr {
                    kind: HirExprKind::Integer(0),
                    ty: TypeId::I64,
                };
                (start, end)
            }
            2 => {
                let start = self.lower_expr(&args[0].value, ctx)?;
                let end = self.lower_expr(&args[1].value, ctx)?;
                (start, end)
            }
            _ => {
                return Err(LowerError::Unsupported(
                    "range() with unsupported number of arguments".to_string(),
                ));
            }
        };

        let end_var_name = format!("_iter_end_{}", ctx.locals.len());
        let end_local = ctx.add_local(end_var_name, TypeId::I64, Mutability::Immutable);
        stmts.push(HirStmt::Let {
            local_index: end_local,
            ty: TypeId::I64,
            value: Some(end_expr),
        });

        let iter_local = ctx.add_local(var_name.to_string(), TypeId::I64, Mutability::Mutable);
        stmts.push(HirStmt::Let {
            local_index: iter_local,
            ty: TypeId::I64,
            value: Some(start_expr),
        });

        let condition = HirExpr {
            kind: HirExprKind::Binary {
                op: BinOp::Lt,
                left: Box::new(HirExpr {
                    kind: HirExprKind::Local(iter_local),
                    ty: TypeId::I64,
                }),
                right: Box::new(HirExpr {
                    kind: HirExprKind::Local(end_local),
                    ty: TypeId::I64,
                }),
            },
            ty: TypeId::BOOL,
        };

        let body_stmts = self.lower_block(body, ctx)?;
        let increment = vec![HirStmt::Assign {
            target: HirExpr {
                kind: HirExprKind::Local(iter_local),
                ty: TypeId::I64,
            },
            value: HirExpr {
                kind: HirExprKind::Binary {
                    op: BinOp::Add,
                    left: Box::new(HirExpr {
                        kind: HirExprKind::Local(iter_local),
                        ty: TypeId::I64,
                    }),
                    right: Box::new(HirExpr {
                        kind: HirExprKind::Integer(1),
                        ty: TypeId::I64,
                    }),
                },
                ty: TypeId::I64,
            },
        }];

        stmts.push(HirStmt::While {
            condition,
            body: body_stmts,
            increment,
        });

        Ok(stmts)
    }

    /// Destructure a let pattern binding into individual local variable assignments.
    ///
    /// For tuple patterns like `val (a, b, c) = expr`, this creates:
    /// - `var a = temp[0]`
    /// - `var b = temp[1]`
    /// - `var c = temp[2]`
    fn lower_let_pattern_binding(
        &mut self,
        pattern: &Pattern,
        source_local: usize,
        mutability: Mutability,
        ctx: &mut FunctionContext,
        stmts: &mut Vec<HirStmt>,
    ) -> LowerResult<()> {
        match pattern {
            Pattern::Tuple(elements) => {
                for (idx, sub_pattern) in elements.iter().enumerate() {
                    let field_expr = HirExpr {
                        kind: HirExprKind::Index {
                            receiver: Box::new(HirExpr {
                                kind: HirExprKind::Local(source_local),
                                ty: TypeId::I64,
                            }),
                            index: Box::new(HirExpr {
                                kind: HirExprKind::Integer(idx as i64),
                                ty: TypeId::I64,
                            }),
                        },
                        ty: TypeId::I64,
                    };

                    match sub_pattern {
                        Pattern::Identifier(name) => {
                            let local = ctx.add_local(name.clone(), TypeId::I64, mutability);
                            stmts.push(HirStmt::Let {
                                local_index: local,
                                ty: TypeId::I64,
                                value: Some(field_expr),
                            });
                        }
                        Pattern::MutIdentifier(name) => {
                            let local = ctx.add_local(name.clone(), TypeId::I64, Mutability::Mutable);
                            stmts.push(HirStmt::Let {
                                local_index: local,
                                ty: TypeId::I64,
                                value: Some(field_expr),
                            });
                        }
                        Pattern::Wildcard => {
                            // Discard this element
                            let discard_name = format!("_discard_{}", ctx.locals.len());
                            let local = ctx.add_local(discard_name, TypeId::I64, Mutability::Immutable);
                            stmts.push(HirStmt::Let {
                                local_index: local,
                                ty: TypeId::I64,
                                value: Some(field_expr),
                            });
                        }
                        Pattern::Tuple(_) => {
                            // Nested tuple: store element in temp, then recurse
                            let uid = ctx.locals.len();
                            let nested_name = format!("_destr_{}", uid);
                            let nested_local = ctx.add_local(nested_name, TypeId::I64, Mutability::Immutable);
                            stmts.push(HirStmt::Let {
                                local_index: nested_local,
                                ty: TypeId::I64,
                                value: Some(field_expr),
                            });
                            self.lower_let_pattern_binding(sub_pattern, nested_local, mutability, ctx, stmts)?;
                        }
                        Pattern::Typed { pattern: inner, .. } => {
                            // Typed pattern: unwrap and handle inner
                            let uid = ctx.locals.len();
                            let typed_name = format!("_destr_{}", uid);
                            let typed_local = ctx.add_local(typed_name, TypeId::I64, Mutability::Immutable);
                            stmts.push(HirStmt::Let {
                                local_index: typed_local,
                                ty: TypeId::I64,
                                value: Some(field_expr),
                            });
                            self.lower_let_pattern_binding(inner, typed_local, mutability, ctx, stmts)?;
                        }
                        _ => {
                            // Best effort: extract name or use temp
                            let name = Self::extract_pattern_name(sub_pattern)
                                .unwrap_or_else(|| format!("_destr_elem_{}", ctx.locals.len()));
                            let local = ctx.add_local(name, TypeId::I64, mutability);
                            stmts.push(HirStmt::Let {
                                local_index: local,
                                ty: TypeId::I64,
                                value: Some(field_expr),
                            });
                        }
                    }
                }
                Ok(())
            }
            Pattern::Array(elements) => {
                // Handle array destructuring the same way as tuples (for bootstrap)
                for (idx, sub_pattern) in elements.iter().enumerate() {
                    let field_expr = HirExpr {
                        kind: HirExprKind::Index {
                            receiver: Box::new(HirExpr {
                                kind: HirExprKind::Local(source_local),
                                ty: TypeId::I64,
                            }),
                            index: Box::new(HirExpr {
                                kind: HirExprKind::Integer(idx as i64),
                                ty: TypeId::I64,
                            }),
                        },
                        ty: TypeId::I64,
                    };
                    let name = Self::extract_pattern_name(sub_pattern)
                        .unwrap_or_else(|| format!("_destr_arr_{}", ctx.locals.len()));
                    let local = ctx.add_local(name, TypeId::I64, mutability);
                    stmts.push(HirStmt::Let {
                        local_index: local,
                        ty: TypeId::I64,
                        value: Some(field_expr),
                    });
                }
                Ok(())
            }
            _ => {
                // For any other pattern type (struct, enum, etc.), assign the whole value
                // to a dummy variable (bootstrap best-effort)
                let name = Self::extract_pattern_name(pattern)
                    .unwrap_or_else(|| format!("_destr_other_{}", ctx.locals.len()));
                let local = ctx.add_local(name, TypeId::I64, mutability);
                stmts.push(HirStmt::Let {
                    local_index: local,
                    ty: TypeId::I64,
                    value: Some(HirExpr {
                        kind: HirExprKind::Local(source_local),
                        ty: TypeId::I64,
                    }),
                });
                Ok(())
            }
        }
    }
}

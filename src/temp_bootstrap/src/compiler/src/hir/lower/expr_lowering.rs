use simple_parser::{self as ast, Expr};

use crate::value::BUILTIN_SPAWN;
use super::context::FunctionContext;
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;
use super::super::types::*;

impl Lowerer {
    /// Helper to lower builtin function calls with consistent handling.
    /// Prefixes with `__spl_` to avoid C name collisions with user functions.
    fn lower_builtin_call(
        &mut self,
        name: &str,
        args: &[ast::Argument],
        ret_ty: TypeId,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let mut args_hir = Vec::new();
        for arg in args {
            args_hir.push(self.lower_expr(&arg.value, ctx)?);
        }
        Ok(HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: format!("__spl_{}", name),
                args: args_hir,
            },
            ty: ret_ty,
        })
    }

    /// Helper to create a builtin call from already-lowered HIR exprs.
    /// Prefixes with `__spl_` to avoid C name collisions with user functions.
    fn make_builtin_call(&self, name: &str, args: Vec<HirExpr>, ty: TypeId) -> HirExpr {
        HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: format!("__spl_{}", name),
                args,
            },
            ty,
        }
    }

    pub(super) fn lower_expr(&mut self, expr: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        match expr {
            Expr::Integer(n) => Ok(HirExpr {
                kind: HirExprKind::Integer(*n),
                ty: TypeId::I64,
            }),

            Expr::Float(f) => Ok(HirExpr {
                kind: HirExprKind::Float(*f),
                ty: TypeId::F64,
            }),

            Expr::String(s) => Ok(HirExpr {
                kind: HirExprKind::String(s.clone()),
                ty: TypeId::STRING,
            }),

            Expr::FString(parts) => {
                use simple_parser::ast::FStringPart;
                // Lower each part and concatenate
                let mut hir_parts: Vec<HirExpr> = Vec::new();
                for part in parts {
                    match part {
                        FStringPart::Literal(s) => {
                            hir_parts.push(HirExpr {
                                kind: HirExprKind::String(s.clone()),
                                ty: TypeId::STRING,
                            });
                        }
                        FStringPart::Expr(e) => {
                            let expr_hir = self.lower_expr(e, ctx)?;
                            // Wrap in to_string call
                            let as_str = self.make_builtin_call(
                                "to_string",
                                vec![expr_hir],
                                TypeId::STRING,
                            );
                            hir_parts.push(as_str);
                        }
                    }
                }
                // Concatenate all parts
                if hir_parts.is_empty() {
                    return Ok(HirExpr {
                        kind: HirExprKind::String(String::new()),
                        ty: TypeId::STRING,
                    });
                }
                let mut result = hir_parts.remove(0);
                for part in hir_parts {
                    result = self.make_builtin_call(
                        "string_concat",
                        vec![result, part],
                        TypeId::STRING,
                    );
                }
                Ok(result)
            }

            Expr::Bool(b) => Ok(HirExpr {
                kind: HirExprKind::Bool(*b),
                ty: TypeId::BOOL,
            }),

            Expr::Nil => Ok(HirExpr {
                kind: HirExprKind::Nil,
                ty: TypeId::NIL,
            }),

            Expr::Identifier(name) => {
                // Check if this is a contract binding (ret, err, result in postconditions)
                if ctx.is_postcondition_binding(name) {
                    return Ok(HirExpr {
                        kind: HirExprKind::ContractResult,
                        ty: ctx.return_type,
                    });
                }
                if ctx.is_error_binding(name) {
                    return Ok(HirExpr {
                        kind: HirExprKind::ContractResult,
                        ty: ctx.return_type,
                    });
                }

                if let Some(idx) = ctx.lookup(name) {
                    let ty = ctx.locals[idx].ty;
                    Ok(HirExpr {
                        kind: HirExprKind::Local(idx),
                        ty,
                    })
                } else if let Some(ty) = self.globals.get(name).copied() {
                    Ok(HirExpr {
                        kind: HirExprKind::Global(name.clone()),
                        ty,
                    })
                } else {
                    // Bootstrap: unknown variable → global with I64 type
                    Ok(HirExpr {
                        kind: HirExprKind::Global(name.clone()),
                        ty: TypeId::I64,
                    })
                }
            }

            Expr::Binary { op, left, right } => {
                let left_hir = Box::new(self.lower_expr(left, ctx)?);
                let right_hir = Box::new(self.lower_expr(right, ctx)?);

                let ty = match op {
                    ast::BinOp::Eq
                    | ast::BinOp::NotEq
                    | ast::BinOp::Lt
                    | ast::BinOp::Gt
                    | ast::BinOp::LtEq
                    | ast::BinOp::GtEq
                    | ast::BinOp::And
                    | ast::BinOp::Or
                    | ast::BinOp::Is
                    | ast::BinOp::In
                    | ast::BinOp::NotIn => TypeId::BOOL,
                    _ => left_hir.ty,
                };

                Ok(HirExpr {
                    kind: HirExprKind::Binary {
                        op: (*op).into(),
                        left: left_hir,
                        right: right_hir,
                    },
                    ty,
                })
            }

            Expr::Unary { op, operand } => {
                let operand_hir = Box::new(self.lower_expr(operand, ctx)?);
                let ty = match op {
                    ast::UnaryOp::Not => TypeId::BOOL,
                    ast::UnaryOp::Ref | ast::UnaryOp::RefMut => {
                        let kind = if *op == ast::UnaryOp::RefMut {
                            PointerKind::BorrowMut
                        } else {
                            PointerKind::Borrow
                        };
                        let ptr_type = HirType::Pointer {
                            kind,
                            inner: operand_hir.ty,
                        };
                        self.module.types.register(ptr_type)
                    }
                    ast::UnaryOp::Deref => {
                        self.get_deref_type(operand_hir.ty)?
                    }
                    _ => operand_hir.ty,
                };

                match op {
                    ast::UnaryOp::Ref | ast::UnaryOp::RefMut => Ok(HirExpr {
                        kind: HirExprKind::Ref(operand_hir),
                        ty,
                    }),
                    ast::UnaryOp::Deref => Ok(HirExpr {
                        kind: HirExprKind::Deref(operand_hir),
                        ty,
                    }),
                    _ => Ok(HirExpr {
                        kind: HirExprKind::Unary {
                            op: (*op).into(),
                            operand: operand_hir,
                        },
                        ty,
                    }),
                }
            }

            Expr::Call { callee, args } => {
                if let Expr::Identifier(name) = callee.as_ref() {
                    match name.as_str() {
                        "generator" => {
                            if args.len() != 1 {
                                return Err(LowerError::Unsupported(
                                    "generator expects exactly one argument (a lambda)".into(),
                                ));
                            }
                            let body_hir = Box::new(self.lower_expr(&args[0].value, ctx)?);
                            return Ok(HirExpr {
                                kind: HirExprKind::GeneratorCreate { body: body_hir },
                                ty: TypeId::I64,
                            });
                        }
                        "future" => {
                            if args.len() != 1 {
                                return Err(LowerError::Unsupported(
                                    "future expects exactly one argument".into(),
                                ));
                            }
                            let body_hir = Box::new(self.lower_expr(&args[0].value, ctx)?);
                            return Ok(HirExpr {
                                kind: HirExprKind::FutureCreate { body: body_hir },
                                ty: TypeId::I64,
                            });
                        }
                        "await" => {
                            if args.len() != 1 {
                                return Err(LowerError::Unsupported(
                                    "await expects exactly one argument".into(),
                                ));
                            }
                            let future_hir = Box::new(self.lower_expr(&args[0].value, ctx)?);
                            return Ok(HirExpr {
                                kind: HirExprKind::Await(future_hir),
                                ty: TypeId::I64,
                            });
                        }
                        "print" | "println" | "eprint" | "eprintln" => {
                            return self.lower_builtin_call(name, args, TypeId::NIL, ctx);
                        }
                        "abs" | "min" | "max" | "sqrt" | "floor" | "ceil" | "pow" => {
                            return self.lower_builtin_call(name, args, TypeId::I64, ctx);
                        }
                        "to_string" | "to_int" => {
                            let ret_ty = if name == "to_string" {
                                TypeId::STRING
                            } else {
                                TypeId::I64
                            };
                            return self.lower_builtin_call(name, args, ret_ty, ctx);
                        }
                        "len" | "length" | "type_of" | "typeof" | "hash" | "input"
                        | "assert" | "panic" | "exit" | "range" => {
                            return self.lower_builtin_call(name, args, TypeId::I64, ctx);
                        }
                        _ => {}
                    }
                }

                if let Expr::Identifier(name) = callee.as_ref() {
                    if name == BUILTIN_SPAWN && args.len() == 1 {
                        let body_hir = Box::new(self.lower_expr(&args[0].value, ctx)?);
                        return Ok(HirExpr {
                            kind: HirExprKind::ActorSpawn { body: body_hir },
                            ty: TypeId::I64,
                        });
                    }
                }

                if ctx.contract_ctx.is_some() {
                    if let Expr::Identifier(name) = callee.as_ref() {
                        let is_implicitly_pure = matches!(name.as_str(),
                            "abs" | "min" | "max" | "sqrt" | "floor" | "ceil" | "pow" |
                            "len" | "is_empty" | "contains" | "to_string" | "to_int"
                        );
                        if !is_implicitly_pure && !self.is_pure_function(name) {
                            return Err(LowerError::ImpureFunctionInContract {
                                func_name: name.clone(),
                            });
                        }
                    }
                }

                let func_hir = Box::new(self.lower_expr(callee, ctx)?);
                let mut args_hir = Vec::new();
                for arg in args {
                    args_hir.push(self.lower_expr(&arg.value, ctx)?);
                }

                let ret_ty = func_hir.ty;

                Ok(HirExpr {
                    kind: HirExprKind::Call {
                        func: func_hir,
                        args: args_hir,
                    },
                    ty: ret_ty,
                })
            }

            // Bootstrap: MethodCall → BuiltinCall with method_ prefix
            Expr::MethodCall { receiver, method, args } => {
                let recv_hir = self.lower_expr(receiver, ctx)?;
                let mut all_args = vec![recv_hir];
                for arg in args {
                    all_args.push(self.lower_expr(&arg.value, ctx)?);
                }
                Ok(self.make_builtin_call(
                    &format!("method_{}", method),
                    all_args,
                    TypeId::I64,
                ))
            }

            Expr::FieldAccess { receiver, field } => {
                let recv_hir = Box::new(self.lower_expr(receiver, ctx)?);
                let (field_index, field_ty) = self.get_field_info(recv_hir.ty, field)?;
                Ok(HirExpr {
                    kind: HirExprKind::FieldAccess {
                        receiver: recv_hir,
                        field_index,
                    },
                    ty: field_ty,
                })
            }

            Expr::Index { receiver, index } => {
                let recv_hir = Box::new(self.lower_expr(receiver, ctx)?);
                let idx_hir = Box::new(self.lower_expr(index, ctx)?);
                let elem_ty = self.get_index_element_type(recv_hir.ty)?;

                Ok(HirExpr {
                    kind: HirExprKind::Index {
                        receiver: recv_hir,
                        index: idx_hir,
                    },
                    ty: elem_ty,
                })
            }

            Expr::Tuple(exprs) => {
                let mut hir_exprs = Vec::new();
                let mut types = Vec::new();
                for e in exprs {
                    let hir = self.lower_expr(e, ctx)?;
                    types.push(hir.ty);
                    hir_exprs.push(hir);
                }

                let tuple_ty = self.module.types.register(HirType::Tuple(types));

                Ok(HirExpr {
                    kind: HirExprKind::Tuple(hir_exprs),
                    ty: tuple_ty,
                })
            }

            Expr::Array(exprs) => {
                let mut hir_exprs = Vec::new();
                let elem_ty = if let Some(first) = exprs.first() {
                    self.infer_type(first, ctx).unwrap_or(TypeId::I64)
                } else {
                    TypeId::VOID
                };

                for e in exprs {
                    hir_exprs.push(self.lower_expr(e, ctx)?);
                }

                let arr_ty = self.module.types.register(HirType::Array {
                    element: elem_ty,
                    size: Some(exprs.len()),
                });

                Ok(HirExpr {
                    kind: HirExprKind::Array(hir_exprs),
                    ty: arr_ty,
                })
            }

            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => {
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

            Expr::Lambda { params, body, .. } => {
                let captures: Vec<usize> = ctx.locals.iter().enumerate().map(|(i, _)| i).collect();
                let param_info: Vec<(String, TypeId)> = params
                    .iter()
                    .map(|p| (p.name.clone(), TypeId::I64))
                    .collect();

                let body_hir = Box::new(self.lower_expr(body, ctx)?);
                let body_ty = body_hir.ty;

                Ok(HirExpr {
                    kind: HirExprKind::Lambda {
                        params: param_info,
                        body: body_hir,
                        captures,
                    },
                    ty: body_ty,
                })
            }

            Expr::Yield(value) => {
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

            Expr::ContractResult => {
                Ok(HirExpr {
                    kind: HirExprKind::ContractResult,
                    ty: ctx.return_type,
                })
            }

            Expr::ContractOld(inner) => {
                let inner_hir = Box::new(self.lower_expr(inner, ctx)?);
                let ty = inner_hir.ty;
                if !self.module.types.is_snapshot_safe(ty) {
                    return Err(LowerError::NotSnapshotSafe);
                }
                Ok(HirExpr {
                    kind: HirExprKind::ContractOld(inner_hir),
                    ty,
                })
            }

            Expr::New { kind, expr } => {
                let value_hir = Box::new(self.lower_expr(expr, ctx)?);
                let inner_ty = value_hir.ty;
                let ptr_kind: PointerKind = (*kind).into();
                let ptr_type = HirType::Pointer {
                    kind: ptr_kind,
                    inner: inner_ty,
                };
                let ptr_ty = self.module.types.register(ptr_type);
                Ok(HirExpr {
                    kind: HirExprKind::PointerNew {
                        kind: ptr_kind,
                        value: value_hir,
                    },
                    ty: ptr_ty,
                })
            }

            // Bootstrap: Match → if/else chain
            Expr::Match { subject, arms } => {
                self.lower_match_expr(subject, arms, ctx)
            }

            // Bootstrap: StructInit → builtin call
            Expr::StructInit { name, fields } => {
                let mut args = Vec::new();
                for (_field_name, field_val) in fields {
                    args.push(self.lower_expr(field_val, ctx)?);
                }
                Ok(self.make_builtin_call(
                    &format!("struct_init_{}", name),
                    args,
                    TypeId::I64,
                ))
            }

            // Bootstrap: NullCoalesce (a ?? b)
            Expr::NullCoalesce { expr, default } => {
                let val_hir = self.lower_expr(expr, ctx)?;
                let def_hir = self.lower_expr(default, ctx)?;
                Ok(self.make_builtin_call("null_coalesce", vec![val_hir, def_hir], TypeId::I64))
            }

            // Bootstrap: Try (expr?)
            Expr::Try(inner) => {
                let inner_hir = self.lower_expr(inner, ctx)?;
                Ok(self.make_builtin_call("try_unwrap", vec![inner_hir], TypeId::I64))
            }

            // Bootstrap: TypeCast (expr as Type)
            Expr::TypeCast { expr, .. } => {
                self.lower_expr(expr, ctx)
            }

            // Bootstrap: DoBlock
            Expr::DoBlock(stmts) => {
                if stmts.is_empty() {
                    return Ok(HirExpr { kind: HirExprKind::Nil, ty: TypeId::NIL });
                }
                // Lower all statements, return the last expression
                let last = stmts.last().unwrap();
                // Try to lower last as expression
                if let ast::Node::Expression(e) = last {
                    return self.lower_expr(e, ctx);
                }
                Ok(HirExpr { kind: HirExprKind::Nil, ty: TypeId::NIL })
            }

            // Bootstrap: Dict literal
            Expr::Dict(entries) => {
                let mut args = Vec::new();
                for (k, v) in entries {
                    args.push(self.lower_expr(k, ctx)?);
                    args.push(self.lower_expr(v, ctx)?);
                }
                Ok(self.make_builtin_call("dict_new", args, TypeId::I64))
            }

            // Bootstrap: Path expression (e.g., Module::Variant)
            Expr::Path(segments) => {
                let name = segments.join("::");
                Ok(HirExpr {
                    kind: HirExprKind::Global(name),
                    ty: TypeId::I64,
                })
            }

            // Bootstrap: Range
            Expr::Range { start, end, .. } => {
                let start_hir = if let Some(s) = start {
                    self.lower_expr(s, ctx)?
                } else {
                    HirExpr { kind: HirExprKind::Integer(0), ty: TypeId::I64 }
                };
                let end_hir = if let Some(e) = end {
                    self.lower_expr(e, ctx)?
                } else {
                    HirExpr { kind: HirExprKind::Integer(0), ty: TypeId::I64 }
                };
                Ok(self.make_builtin_call("range", vec![start_hir, end_hir], TypeId::I64))
            }

            // Bootstrap: Slice
            Expr::Slice { receiver, start, end, .. } => {
                let recv_hir = self.lower_expr(receiver, ctx)?;
                let start_hir = if let Some(s) = start {
                    self.lower_expr(s, ctx)?
                } else {
                    HirExpr { kind: HirExprKind::Integer(0), ty: TypeId::I64 }
                };
                let end_hir = if let Some(e) = end {
                    self.lower_expr(e, ctx)?
                } else {
                    HirExpr { kind: HirExprKind::Integer(-1), ty: TypeId::I64 }
                };
                Ok(self.make_builtin_call("slice", vec![recv_hir, start_hir, end_hir], TypeId::I64))
            }

            // Bootstrap: ListComprehension
            Expr::ListComprehension { expr, iterable, .. } => {
                let iter_hir = self.lower_expr(iterable, ctx)?;
                let expr_hir = self.lower_expr(expr, ctx)?;
                Ok(self.make_builtin_call("list_comprehension", vec![iter_hir, expr_hir], TypeId::I64))
            }

            // Bootstrap: DictComprehension
            Expr::DictComprehension { key, value, iterable, .. } => {
                let iter_hir = self.lower_expr(iterable, ctx)?;
                let key_hir = self.lower_expr(key, ctx)?;
                let val_hir = self.lower_expr(value, ctx)?;
                Ok(self.make_builtin_call("dict_comprehension", vec![iter_hir, key_hir, val_hir], TypeId::I64))
            }

            // Bootstrap: Spawn
            Expr::Spawn(inner) => {
                let body_hir = Box::new(self.lower_expr(inner, ctx)?);
                Ok(HirExpr {
                    kind: HirExprKind::ActorSpawn { body: body_hir },
                    ty: TypeId::I64,
                })
            }

            // Bootstrap: typed literals
            Expr::TypedInteger(n, _) => Ok(HirExpr {
                kind: HirExprKind::Integer(*n),
                ty: TypeId::I64,
            }),
            Expr::TypedFloat(f, _) => Ok(HirExpr {
                kind: HirExprKind::Float(*f),
                ty: TypeId::F64,
            }),
            Expr::TypedString(s, _) => Ok(HirExpr {
                kind: HirExprKind::String(s.clone()),
                ty: TypeId::STRING,
            }),
            Expr::Symbol(s) => Ok(HirExpr {
                kind: HirExprKind::String(s.clone()),
                ty: TypeId::STRING,
            }),

            // Bootstrap: OptionalCheck (expr?)
            Expr::OptionalCheck(inner) => {
                let inner_hir = self.lower_expr(inner, ctx)?;
                Ok(self.make_builtin_call("optional_check", vec![inner_hir], TypeId::BOOL))
            }

            // Bootstrap: TupleIndex
            Expr::TupleIndex { receiver, index } => {
                let recv_hir = Box::new(self.lower_expr(receiver, ctx)?);
                let idx_hir = Box::new(HirExpr {
                    kind: HirExprKind::Integer(*index as i64),
                    ty: TypeId::I64,
                });
                Ok(HirExpr {
                    kind: HirExprKind::Index { receiver: recv_hir, index: idx_hir },
                    ty: TypeId::I64,
                })
            }

            // Bootstrap: Spread/DictSpread
            Expr::Spread(inner) | Expr::DictSpread(inner) => {
                self.lower_expr(inner, ctx)
            }

            // Bootstrap: MacroInvocation
            Expr::MacroInvocation { name, .. } => {
                Ok(self.make_builtin_call(
                    &format!("macro_{}", name),
                    vec![],
                    TypeId::I64,
                ))
            }

            // Bootstrap: LetBinding in expression context
            Expr::LetBinding { value, .. } => {
                self.lower_expr(value, ctx)
            }

            // Bootstrap: FunctionalUpdate (obj->method(args))
            Expr::FunctionalUpdate { target, method, args } => {
                let target_hir = self.lower_expr(target, ctx)?;
                let mut call_args = vec![target_hir];
                for arg in args {
                    call_args.push(self.lower_expr(&arg.value, ctx)?);
                }
                Ok(self.make_builtin_call(
                    &format!("method_{}", method),
                    call_args,
                    TypeId::I64,
                ))
            }

            // Bootstrap: catch-all — any unhandled expression type → Nil
            // This ensures compilation succeeds even for exotic expressions
            _ => Ok(HirExpr { kind: HirExprKind::Nil, ty: TypeId::I64 }),
        }
    }

    /// Lower a match expression to an if/else chain
    fn lower_match_expr(
        &mut self,
        subject: &Expr,
        arms: &[ast::MatchArm],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let subject_hir = self.lower_expr(subject, ctx)?;

        if arms.is_empty() {
            return Ok(HirExpr { kind: HirExprKind::Nil, ty: TypeId::NIL });
        }

        // Build if/else chain in reverse
        let mut result: Option<HirExpr> = None;

        for arm in arms.iter().rev() {
            // Lower arm body: use last expression from body block
            let body_hir = if let Some(last_stmt) = arm.body.statements.last() {
                if let ast::Node::Expression(e) = last_stmt {
                    self.lower_expr(e, ctx)?
                } else {
                    HirExpr { kind: HirExprKind::Nil, ty: TypeId::NIL }
                }
            } else {
                HirExpr { kind: HirExprKind::Nil, ty: TypeId::NIL }
            };

            // Check if this is a wildcard/catch-all
            let is_wildcard = matches!(
                &arm.pattern,
                ast::Pattern::Wildcard | ast::Pattern::Identifier(_) | ast::Pattern::MutIdentifier(_)
            );

            if is_wildcard {
                result = Some(body_hir);
            } else if let Some(else_expr) = result.take() {
                // Build condition from pattern
                let cond = self.lower_pattern_condition(&subject_hir, &arm.pattern, ctx);
                result = Some(HirExpr {
                    kind: HirExprKind::If {
                        condition: Box::new(cond),
                        then_branch: Box::new(body_hir),
                        else_branch: Some(Box::new(else_expr)),
                    },
                    ty: TypeId::I64,
                });
            } else {
                // No else — this arm becomes the result
                let cond = self.lower_pattern_condition(&subject_hir, &arm.pattern, ctx);
                result = Some(HirExpr {
                    kind: HirExprKind::If {
                        condition: Box::new(cond),
                        then_branch: Box::new(body_hir),
                        else_branch: None,
                    },
                    ty: TypeId::I64,
                });
            }
        }

        Ok(result.unwrap_or(HirExpr { kind: HirExprKind::Nil, ty: TypeId::NIL }))
    }

    /// Build a condition expression for a match pattern
    fn lower_pattern_condition(
        &mut self,
        subject: &HirExpr,
        pattern: &ast::Pattern,
        _ctx: &mut FunctionContext,
    ) -> HirExpr {
        match pattern {
            ast::Pattern::Literal(expr) => {
                // Compare subject == literal
                if let Ok(lit_hir) = self.lower_expr(expr, _ctx) {
                    HirExpr {
                        kind: HirExprKind::Binary {
                            op: BinOp::Eq,
                            left: Box::new(subject.clone()),
                            right: Box::new(lit_hir),
                        },
                        ty: TypeId::BOOL,
                    }
                } else {
                    HirExpr { kind: HirExprKind::Bool(true), ty: TypeId::BOOL }
                }
            }
            ast::Pattern::Enum { name, variant, .. } => {
                // Compare subject to enum variant (use string-based comparison for bootstrap)
                let variant_name = format!("{}::{}", name, variant);
                HirExpr {
                    kind: HirExprKind::Binary {
                        op: BinOp::Eq,
                        left: Box::new(subject.clone()),
                        right: Box::new(HirExpr {
                            kind: HirExprKind::Global(variant_name),
                            ty: TypeId::I64,
                        }),
                    },
                    ty: TypeId::BOOL,
                }
            }
            // Default: unconditional match
            _ => HirExpr { kind: HirExprKind::Bool(true), ty: TypeId::BOOL },
        }
    }

    pub(super) fn infer_type(&mut self, expr: &Expr, ctx: &FunctionContext) -> LowerResult<TypeId> {
        match expr {
            Expr::Integer(_) => Ok(TypeId::I64),
            Expr::Float(_) => Ok(TypeId::F64),
            Expr::String(_) => Ok(TypeId::STRING),
            Expr::FString(_) => Ok(TypeId::STRING),
            Expr::Bool(_) => Ok(TypeId::BOOL),
            Expr::Nil => Ok(TypeId::NIL),
            Expr::Identifier(name) => {
                if let Some(idx) = ctx.lookup(name) {
                    Ok(ctx.locals[idx].ty)
                } else if let Some(ty) = self.globals.get(name) {
                    Ok(*ty)
                } else {
                    // Bootstrap: unknown variable → I64
                    Ok(TypeId::I64)
                }
            }
            Expr::Binary { op, left, .. } => match op {
                ast::BinOp::Eq
                | ast::BinOp::NotEq
                | ast::BinOp::Lt
                | ast::BinOp::Gt
                | ast::BinOp::LtEq
                | ast::BinOp::GtEq
                | ast::BinOp::And
                | ast::BinOp::Or => Ok(TypeId::BOOL),
                _ => self.infer_type(left, ctx),
            },
            Expr::Unary { op, operand } => match op {
                ast::UnaryOp::Not => Ok(TypeId::BOOL),
                _ => self.infer_type(operand, ctx),
            },
            Expr::Call { callee, .. } => {
                self.infer_type(callee, ctx)
            }
            Expr::If { then_branch, .. } => {
                self.infer_type(then_branch, ctx)
            }
            Expr::Tuple(exprs) => {
                if exprs.is_empty() {
                    Ok(TypeId::VOID)
                } else {
                    let mut types = Vec::new();
                    for e in exprs {
                        types.push(self.infer_type(e, ctx).unwrap_or(TypeId::I64));
                    }
                    Ok(self.module.types.register(HirType::Tuple(types)))
                }
            }
            Expr::Array(exprs) => {
                if let Some(first) = exprs.first() {
                    let elem_ty = self.infer_type(first, ctx).unwrap_or(TypeId::I64);
                    Ok(self.module.types.register(HirType::Array {
                        element: elem_ty,
                        size: Some(exprs.len()),
                    }))
                } else {
                    Ok(TypeId::VOID)
                }
            }
            Expr::Index { receiver, .. } => {
                let arr_ty = self.infer_type(receiver, ctx)?;
                self.get_index_element_type(arr_ty)
            }
            Expr::FieldAccess { receiver, field } => {
                let struct_ty = self.infer_type(receiver, ctx).unwrap_or(TypeId::I64);
                let (_idx, field_ty) = self.get_field_info(struct_ty, field)?;
                Ok(field_ty)
            }
            // Bootstrap: MethodCall → I64
            Expr::MethodCall { .. } => Ok(TypeId::I64),
            // Bootstrap: all other expressions → I64
            _ => Ok(TypeId::I64),
        }
    }
}

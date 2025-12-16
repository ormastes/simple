use simple_parser::{self as ast, Expr};

use crate::value::BUILTIN_SPAWN;
use super::context::FunctionContext;
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;
use super::super::types::*;

impl Lowerer {
    /// Helper to lower builtin function calls with consistent handling
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
                name: name.to_string(),
                args: args_hir,
            },
            ty: ret_ty,
        })
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
                // Check if the FString is a simple literal (no interpolation)
                // If so, convert it to a plain string
                use simple_parser::ast::FStringPart;
                let mut result = String::new();
                let mut all_literal = true;
                for part in parts {
                    match part {
                        FStringPart::Literal(s) => {
                            result.push_str(s);
                        }
                        FStringPart::Expr(_) => {
                            all_literal = false;
                            break;
                        }
                    }
                }
                if all_literal {
                    Ok(HirExpr {
                        kind: HirExprKind::String(result),
                        ty: TypeId::STRING,
                    })
                } else {
                    Err(LowerError::Unsupported(format!(
                        "FString with interpolation not yet supported in native compilation"
                    )))
                }
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
                    // Error binding also refers to the return value (the error part)
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
                    Err(LowerError::UnknownVariable(name.clone()))
                }
            }

            Expr::Binary { op, left, right } => {
                let left_hir = Box::new(self.lower_expr(left, ctx)?);
                let right_hir = Box::new(self.lower_expr(right, ctx)?);

                // Type is determined by operands (simplified)
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
                    | ast::BinOp::In => TypeId::BOOL,
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
                        // Look up inner type from pointer type
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
                // Check for special builtins: generator, future, spawn, await, print, etc.
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
                        // Prelude I/O functions
                        "print" | "println" | "eprint" | "eprintln" => {
                            return self.lower_builtin_call(name, args, TypeId::NIL, ctx);
                        }
                        // Prelude math functions
                        "abs" | "min" | "max" | "sqrt" | "floor" | "ceil" | "pow" => {
                            return self.lower_builtin_call(name, args, TypeId::I64, ctx);
                        }
                        // Prelude conversion functions
                        "to_string" | "to_int" => {
                            let ret_ty = if name == "to_string" {
                                TypeId::STRING
                            } else {
                                TypeId::I64
                            };
                            return self.lower_builtin_call(name, args, ret_ty, ctx);
                        }
                        _ => {} // Fall through to normal call handling
                    }
                }

                // Check for spawn as a statement-like expression
                if let Expr::Identifier(name) = callee.as_ref() {
                    if name == BUILTIN_SPAWN && args.len() == 1 {
                        let body_hir = Box::new(self.lower_expr(&args[0].value, ctx)?);
                        return Ok(HirExpr {
                            kind: HirExprKind::ActorSpawn { body: body_hir },
                            ty: TypeId::I64,
                        });
                    }
                }

                // CTR-030-032: Check for impure function calls in contract expressions
                if ctx.contract_ctx.is_some() {
                    if let Expr::Identifier(name) = callee.as_ref() {
                        // Check if function is pure (marked with #[pure])
                        // Some builtins are implicitly pure: comparisons, math, etc.
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

                // Return type comes from function type
                let ret_ty = func_hir.ty; // Simplified - would need function type lookup

                Ok(HirExpr {
                    kind: HirExprKind::Call {
                        func: func_hir,
                        args: args_hir,
                    },
                    ty: ret_ty,
                })
            }

            Expr::FieldAccess { receiver, field } => {
                let recv_hir = Box::new(self.lower_expr(receiver, ctx)?);
                // Look up struct field type and index
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
                // Look up element type from array type
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
                    self.infer_type(first, ctx)?
                } else {
                    // Empty array needs explicit type annotation
                    // For now, default to VOID to allow empty arrays (will fail later if used)
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
                // Track captured variables from outer scope
                let captures: Vec<usize> = ctx.locals.iter().enumerate().map(|(i, _)| i).collect();

                // Collect parameter names and types
                let param_info: Vec<(String, TypeId)> = params
                    .iter()
                    .map(|p| (p.name.clone(), TypeId::I64)) // Default to I64 for untyped params
                    .collect();

                // Lower the lambda body
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

            // Contract expressions (Design by Contract)
            Expr::ContractResult => {
                // ContractResult refers to the return value in postconditions
                // The type is determined by the function's return type from context
                Ok(HirExpr {
                    kind: HirExprKind::ContractResult,
                    ty: ctx.return_type,
                })
            }

            Expr::ContractOld(inner) => {
                // old(expr) captures the value of expr at function entry
                let inner_hir = Box::new(self.lower_expr(inner, ctx)?);
                let ty = inner_hir.ty;

                // CTR-060-062: Check that the type is snapshot-safe
                // Snapshot-safe types include primitives, enums, and immutable structs
                if !self.module.types.is_snapshot_safe(ty) {
                    return Err(LowerError::NotSnapshotSafe);
                }

                Ok(HirExpr {
                    kind: HirExprKind::ContractOld(inner_hir),
                    ty,
                })
            }

            _ => Err(LowerError::Unsupported(format!("{:?}", expr))),
        }
    }

    pub(super) fn infer_type(&mut self, expr: &Expr, ctx: &FunctionContext) -> LowerResult<TypeId> {
        match expr {
            Expr::Integer(_) => Ok(TypeId::I64),
            Expr::Float(_) => Ok(TypeId::F64),
            Expr::String(_) => Ok(TypeId::STRING),
            Expr::Bool(_) => Ok(TypeId::BOOL),
            Expr::Nil => Ok(TypeId::NIL),
            Expr::Identifier(name) => {
                if let Some(idx) = ctx.lookup(name) {
                    Ok(ctx.locals[idx].ty)
                } else if let Some(ty) = self.globals.get(name) {
                    Ok(*ty)
                } else {
                    Err(LowerError::UnknownVariable(name.clone()))
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
                // Return type of call is the type of the callee (function)
                self.infer_type(callee, ctx)
            }
            Expr::If { then_branch, .. } => {
                // Type of if-expression is the type of the then branch
                self.infer_type(then_branch, ctx)
            }
            Expr::Tuple(exprs) => {
                // Infer tuple type from elements
                if exprs.is_empty() {
                    Ok(TypeId::VOID)
                } else {
                    // Recursively infer element types
                    let mut types = Vec::new();
                    for e in exprs {
                        types.push(self.infer_type(e, ctx)?);
                    }
                    Ok(self.module.types.register(HirType::Tuple(types)))
                }
            }
            Expr::Array(exprs) => {
                if let Some(first) = exprs.first() {
                    // Infer array type from first element
                    let elem_ty = self.infer_type(first, ctx)?;
                    Ok(self.module.types.register(HirType::Array {
                        element: elem_ty,
                        size: Some(exprs.len()),
                    }))
                } else {
                    Ok(TypeId::VOID)
                }
            }
            Expr::Index { receiver, .. } => {
                // Infer element type from array type
                let arr_ty = self.infer_type(receiver, ctx)?;
                self.get_index_element_type(arr_ty)
            }
            Expr::FieldAccess { receiver, field } => {
                // Infer field type from struct type
                let struct_ty = self.infer_type(receiver, ctx)?;
                let (_idx, field_ty) = self.get_field_info(struct_ty, field)?;
                Ok(field_ty)
            }
            // Cannot infer type for complex expressions - require annotation
            _ => Err(LowerError::CannotInferTypeFor(format!("{:?}", expr))),
        }
    }

}

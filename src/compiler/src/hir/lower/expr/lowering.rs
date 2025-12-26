use simple_parser::{self as ast, ast::ReferenceCapability, Expr};

use crate::value::BUILTIN_SPAWN;
use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    pub(in crate::hir::lower) fn lower_expr(&mut self, expr: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
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

                // Type is determined by operands
                // For SIMD vectors, comparison returns a SIMD bool vector
                let ty = match op {
                    ast::BinOp::Eq
                    | ast::BinOp::NotEq
                    | ast::BinOp::Lt
                    | ast::BinOp::Gt
                    | ast::BinOp::LtEq
                    | ast::BinOp::GtEq => {
                        // For SIMD vectors, return a SIMD bool vector
                        if let Some(HirType::Simd { lanes, .. }) =
                            self.module.types.get(left_hir.ty)
                        {
                            let lanes = *lanes;
                            self.module.types.register(HirType::Simd {
                                lanes,
                                element: TypeId::BOOL,
                            })
                        } else {
                            TypeId::BOOL
                        }
                    }
                    ast::BinOp::And | ast::BinOp::Or | ast::BinOp::Is | ast::BinOp::In => {
                        TypeId::BOOL
                    }
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
                            capability: ReferenceCapability::Shared, // Default capability
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
                // Check for thread_group.id and thread_group.size before lowering receiver
                if let Expr::Identifier(recv_name) = receiver.as_ref() {
                    if recv_name == "thread_group" {
                        match field.as_str() {
                            "id" => {
                                // thread_group.id → GroupId intrinsic (group index)
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::GroupId,
                                        args: vec![],
                                    },
                                    ty: TypeId::I64,
                                });
                            }
                            "size" => {
                                // thread_group.size → LocalSize intrinsic (work group size)
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::LocalSize,
                                        args: vec![],
                                    },
                                    ty: TypeId::I64,
                                });
                            }
                            _ => {
                                return Err(LowerError::Unsupported(format!(
                                    "unknown thread_group property: {}",
                                    field
                                )));
                            }
                        }
                    }
                }

                let recv_hir = Box::new(self.lower_expr(receiver, ctx)?);

                // Check for SIMD neighbor access: array.left_neighbor or array.right_neighbor
                if field == "left_neighbor" || field == "right_neighbor" {
                    // Check if receiver is an array type using helper method
                    if let Some(element_ty) = self.module.types.get_array_element(recv_hir.ty) {
                        let direction = if field == "left_neighbor" {
                            NeighborDirection::Left
                        } else {
                            NeighborDirection::Right
                        };
                        return Ok(HirExpr {
                            kind: HirExprKind::NeighborAccess {
                                array: recv_hir,
                                direction,
                            },
                            ty: element_ty,
                        });
                    }
                }

                // Check for SIMD swizzle: v.xyzw, v.xxxx, v.rgba, v.rrrr, etc.
                if let Some(HirType::Simd { lanes, element }) = self.module.types.get(recv_hir.ty) {
                    let lanes = *lanes;
                    let element = *element;
                    if let Some(indices) = self.parse_swizzle_pattern(field, lanes) {
                        // Create indices array literal
                        let indices_hir: Vec<HirExpr> = indices
                            .iter()
                            .map(|&i| HirExpr {
                                kind: HirExprKind::Integer(i as i64),
                                ty: TypeId::I64,
                            })
                            .collect();
                        let indices_len = indices_hir.len() as u32;
                        let indices_array_ty = self.module.types.register(HirType::Array {
                            element: TypeId::I64,
                            size: Some(indices_len as usize),
                        });
                        let indices_expr = HirExpr {
                            kind: HirExprKind::Array(indices_hir),
                            ty: indices_array_ty,
                        };
                        // Result type: same element type, but with number of lanes from swizzle length
                        let result_ty = self.module.types.register(HirType::Simd {
                            lanes: indices_len,
                            element,
                        });
                        return Ok(HirExpr {
                            kind: HirExprKind::GpuIntrinsic {
                                intrinsic: GpuIntrinsicKind::SimdShuffle,
                                args: vec![*recv_hir, indices_expr],
                            },
                            ty: result_ty,
                        });
                    }
                }

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
                // Look up element type from array/simd type
                let elem_ty = self.get_index_element_type(recv_hir.ty)?;

                // Check if receiver is SIMD type - use SimdExtract intrinsic
                if let Some(HirType::Simd { .. }) = self.module.types.get(recv_hir.ty) {
                    return Ok(HirExpr {
                        kind: HirExprKind::GpuIntrinsic {
                            intrinsic: GpuIntrinsicKind::SimdExtract,
                            args: vec![*recv_hir, *idx_hir],
                        },
                        ty: elem_ty,
                    });
                }

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

            Expr::VecLiteral(exprs) => {
                let mut hir_exprs = Vec::new();
                let elem_ty = if let Some(first) = exprs.first() {
                    self.infer_type(first, ctx)?
                } else {
                    // Empty vector needs explicit type annotation
                    TypeId::VOID
                };

                for e in exprs {
                    hir_exprs.push(self.lower_expr(e, ctx)?);
                }

                let vec_ty = self.module.types.register(HirType::Simd {
                    lanes: exprs.len() as u32,
                    element: elem_ty,
                });

                Ok(HirExpr {
                    kind: HirExprKind::VecLiteral(hir_exprs),
                    ty: vec_ty,
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

            // Pointer allocation: new &T(value) or new *T(value)
            Expr::New { kind, expr } => {
                let value_hir = Box::new(self.lower_expr(expr, ctx)?);
                let inner_ty = value_hir.ty;
                let ptr_kind: PointerKind = (*kind).into();
                let ptr_type = HirType::Pointer {
                    kind: ptr_kind,
                    capability: ReferenceCapability::Shared, // Default capability
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

            // Method calls: receiver.method(args)
            // Special handling for SIMD intrinsics: this.index(), this.thread_index(), this.group_index()
            // and thread_group.barrier()
            Expr::MethodCall { receiver, method, args } => {
                // Check for intrinsic calls on `this` and `thread_group`
                if let Expr::Identifier(recv_name) = receiver.as_ref() {
                    if recv_name == "this" {
                        match method.as_str() {
                            "index" => {
                                if !args.is_empty() {
                                    return Err(LowerError::Unsupported(
                                        "this.index() takes no arguments".into(),
                                    ));
                                }
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::SimdIndex,
                                        args: vec![],
                                    },
                                    ty: TypeId::I64,
                                });
                            }
                            "thread_index" => {
                                if !args.is_empty() {
                                    return Err(LowerError::Unsupported(
                                        "this.thread_index() takes no arguments".into(),
                                    ));
                                }
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::SimdThreadIndex,
                                        args: vec![],
                                    },
                                    ty: TypeId::I64,
                                });
                            }
                            "group_index" => {
                                if !args.is_empty() {
                                    return Err(LowerError::Unsupported(
                                        "this.group_index() takes no arguments".into(),
                                    ));
                                }
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::SimdGroupIndex,
                                        args: vec![],
                                    },
                                    ty: TypeId::I64,
                                });
                            }
                            _ => {} // Fall through to regular method call handling
                        }
                    } else if recv_name == "thread_group" {
                        match method.as_str() {
                            "barrier" => {
                                if !args.is_empty() {
                                    return Err(LowerError::Unsupported(
                                        "thread_group.barrier() takes no arguments".into(),
                                    ));
                                }
                                // thread_group.barrier() → Barrier intrinsic
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::Barrier,
                                        args: vec![],
                                    },
                                    ty: TypeId::VOID,
                                });
                            }
                            _ => {
                                return Err(LowerError::Unsupported(format!(
                                    "unknown thread_group method: {}",
                                    method
                                )));
                            }
                        }
                    } else if recv_name == "gpu" {
                        // gpu.* style intrinsic functions
                        match method.as_str() {
                            "global_id" => {
                                // gpu.global_id() or gpu.global_id(dim)
                                let dim_arg = self.lower_gpu_dim_arg(args, ctx)?;
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::GlobalId,
                                        args: dim_arg,
                                    },
                                    ty: TypeId::I64,
                                });
                            }
                            "local_id" => {
                                let dim_arg = self.lower_gpu_dim_arg(args, ctx)?;
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::LocalId,
                                        args: dim_arg,
                                    },
                                    ty: TypeId::I64,
                                });
                            }
                            "group_id" => {
                                let dim_arg = self.lower_gpu_dim_arg(args, ctx)?;
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::GroupId,
                                        args: dim_arg,
                                    },
                                    ty: TypeId::I64,
                                });
                            }
                            "global_size" => {
                                let dim_arg = self.lower_gpu_dim_arg(args, ctx)?;
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::GlobalSize,
                                        args: dim_arg,
                                    },
                                    ty: TypeId::I64,
                                });
                            }
                            "local_size" => {
                                let dim_arg = self.lower_gpu_dim_arg(args, ctx)?;
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::LocalSize,
                                        args: dim_arg,
                                    },
                                    ty: TypeId::I64,
                                });
                            }
                            "num_groups" => {
                                let dim_arg = self.lower_gpu_dim_arg(args, ctx)?;
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::NumGroups,
                                        args: dim_arg,
                                    },
                                    ty: TypeId::I64,
                                });
                            }
                            "barrier" => {
                                if !args.is_empty() {
                                    return Err(LowerError::Unsupported(
                                        "gpu.barrier() takes no arguments".into(),
                                    ));
                                }
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::Barrier,
                                        args: vec![],
                                    },
                                    ty: TypeId::VOID,
                                });
                            }
                            "mem_fence" => {
                                if !args.is_empty() {
                                    return Err(LowerError::Unsupported(
                                        "gpu.mem_fence() takes no arguments".into(),
                                    ));
                                }
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::MemFence,
                                        args: vec![],
                                    },
                                    ty: TypeId::VOID,
                                });
                            }
                            "atomic_add" | "atomic_sub" | "atomic_min" | "atomic_max"
                            | "atomic_and" | "atomic_or" | "atomic_xor" | "atomic_exchange" => {
                                // gpu.atomic_*(ptr, val) -> old value
                                if args.len() != 2 {
                                    return Err(LowerError::Unsupported(format!(
                                        "gpu.{}(ptr, val) requires exactly 2 arguments",
                                        method
                                    )));
                                }
                                let ptr_hir = self.lower_expr(&args[0].value, ctx)?;
                                let val_hir = self.lower_expr(&args[1].value, ctx)?;
                                let intrinsic = match method.as_str() {
                                    "atomic_add" => GpuIntrinsicKind::GpuAtomicAdd,
                                    "atomic_sub" => GpuIntrinsicKind::GpuAtomicSub,
                                    "atomic_min" => GpuIntrinsicKind::GpuAtomicMin,
                                    "atomic_max" => GpuIntrinsicKind::GpuAtomicMax,
                                    "atomic_and" => GpuIntrinsicKind::GpuAtomicAnd,
                                    "atomic_or" => GpuIntrinsicKind::GpuAtomicOr,
                                    "atomic_xor" => GpuIntrinsicKind::GpuAtomicXor,
                                    "atomic_exchange" => GpuIntrinsicKind::GpuAtomicExchange,
                                    _ => unreachable!(),
                                };
                                // Return type is I64 (the old value)
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic,
                                        args: vec![ptr_hir, val_hir],
                                    },
                                    ty: TypeId::I64,
                                });
                            }
                            "atomic_compare_exchange" => {
                                // gpu.atomic_compare_exchange(ptr, expected, desired) -> old value
                                if args.len() != 3 {
                                    return Err(LowerError::Unsupported(
                                        "gpu.atomic_compare_exchange(ptr, expected, desired) requires exactly 3 arguments".into(),
                                    ));
                                }
                                let ptr_hir = self.lower_expr(&args[0].value, ctx)?;
                                let expected_hir = self.lower_expr(&args[1].value, ctx)?;
                                let desired_hir = self.lower_expr(&args[2].value, ctx)?;
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::GpuAtomicCompareExchange,
                                        args: vec![ptr_hir, expected_hir, desired_hir],
                                    },
                                    ty: TypeId::I64, // Returns old value
                                });
                            }
                            _ => {
                                return Err(LowerError::Unsupported(format!(
                                    "unknown gpu method: {}",
                                    method
                                )));
                            }
                        }
                    } else if recv_name == "f32x4" || recv_name == "f64x4" || recv_name == "i32x4" || recv_name == "i64x4" {
                        // SIMD type static methods: f32x4.load(arr, offset), f32x4.gather(arr, indices)
                        let simd_ty = match recv_name.as_str() {
                            "f32x4" => self.module.types.register(HirType::Simd { lanes: 4, element: TypeId::F32 }),
                            "f64x4" => self.module.types.register(HirType::Simd { lanes: 4, element: TypeId::F64 }),
                            "i32x4" => self.module.types.register(HirType::Simd { lanes: 4, element: TypeId::I32 }),
                            "i64x4" => self.module.types.register(HirType::Simd { lanes: 4, element: TypeId::I64 }),
                            _ => unreachable!(),
                        };
                        match method.as_str() {
                            "load" => {
                                // f32x4.load(arr, offset) - load 4 elements from array
                                if args.len() != 2 {
                                    return Err(LowerError::Unsupported(
                                        format!("{}.load(array, offset) requires exactly 2 arguments", recv_name),
                                    ));
                                }
                                let array_hir = self.lower_expr(&args[0].value, ctx)?;
                                let offset_hir = self.lower_expr(&args[1].value, ctx)?;
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::SimdLoad,
                                        args: vec![array_hir, offset_hir],
                                    },
                                    ty: simd_ty,
                                });
                            }
                            "gather" => {
                                // f32x4.gather(arr, indices) - gather 4 elements at arbitrary indices
                                if args.len() != 2 {
                                    return Err(LowerError::Unsupported(
                                        format!("{}.gather(array, indices) requires exactly 2 arguments", recv_name),
                                    ));
                                }
                                let array_hir = self.lower_expr(&args[0].value, ctx)?;
                                let indices_hir = self.lower_expr(&args[1].value, ctx)?;
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::SimdGather,
                                        args: vec![array_hir, indices_hir],
                                    },
                                    ty: simd_ty,
                                });
                            }
                            "load_masked" => {
                                // f32x4.load_masked(arr, offset, mask, default) - load with mask
                                if args.len() != 4 {
                                    return Err(LowerError::Unsupported(
                                        format!("{}.load_masked(array, offset, mask, default) requires exactly 4 arguments", recv_name),
                                    ));
                                }
                                let array_hir = self.lower_expr(&args[0].value, ctx)?;
                                let offset_hir = self.lower_expr(&args[1].value, ctx)?;
                                let mask_hir = self.lower_expr(&args[2].value, ctx)?;
                                let default_hir = self.lower_expr(&args[3].value, ctx)?;
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::SimdMaskedLoad,
                                        args: vec![array_hir, offset_hir, mask_hir, default_hir],
                                    },
                                    ty: simd_ty,
                                });
                            }
                            _ => {
                                return Err(LowerError::Unsupported(format!(
                                    "unknown {} static method: {}",
                                    recv_name, method
                                )));
                            }
                        }
                    }

                    // Check if receiver is a type name (for static method calls like ClassName.method())
                    // This must be inside the `if let Expr::Identifier(recv_name)` block
                    if self.module.types.lookup(recv_name).is_some() {
                        // This is a static method call on a class/struct
                        // Convert to a regular function call with qualified name
                        let qualified_name = format!("{}.{}", recv_name, method);

                        // Lower arguments
                        let mut args_hir = Vec::new();
                        for arg in args {
                            args_hir.push(self.lower_expr(&arg.value, ctx)?);
                        }

                        // Create a regular Call (not BuiltinCall) so DI injection works
                        let func_expr = HirExpr {
                            kind: HirExprKind::Global(qualified_name),
                            ty: TypeId::VOID, // Function type, will be resolved
                        };

                        return Ok(HirExpr {
                            kind: HirExprKind::Call {
                                func: Box::new(func_expr),
                                args: args_hir,
                            },
                            ty: TypeId::VOID, // Return type will be inferred
                        });
                    }
                }

                // Check for SIMD vector reduction methods
                let receiver_hir = self.lower_expr(receiver, ctx)?;
                if let Some(HirType::Simd { element, .. }) = self.module.types.get(receiver_hir.ty) {
                    let element = *element;
                    let simd_ty = receiver_hir.ty; // Save the SIMD type before moving receiver_hir
                    match method.as_str() {
                        "sum" => {
                            if !args.is_empty() {
                                return Err(LowerError::Unsupported(
                                    "vec.sum() takes no arguments".into(),
                                ));
                            }
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdSum,
                                    args: vec![receiver_hir],
                                },
                                ty: element,
                            });
                        }
                        "product" => {
                            if !args.is_empty() {
                                return Err(LowerError::Unsupported(
                                    "vec.product() takes no arguments".into(),
                                ));
                            }
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdProduct,
                                    args: vec![receiver_hir],
                                },
                                ty: element,
                            });
                        }
                        "min" => {
                            if args.is_empty() {
                                // v.min() - horizontal reduction
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::SimdMin,
                                        args: vec![receiver_hir],
                                    },
                                    ty: element,
                                });
                            } else if args.len() == 1 {
                                // v.min(b) - element-wise minimum
                                let b_hir = self.lower_expr(&args[0].value, ctx)?;
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::SimdMinVec,
                                        args: vec![receiver_hir, b_hir],
                                    },
                                    ty: simd_ty,
                                });
                            } else {
                                return Err(LowerError::Unsupported(
                                    "vec.min() or vec.min(b) expected".into(),
                                ));
                            }
                        }
                        "max" => {
                            if args.is_empty() {
                                // v.max() - horizontal reduction
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::SimdMax,
                                        args: vec![receiver_hir],
                                    },
                                    ty: element,
                                });
                            } else if args.len() == 1 {
                                // v.max(b) - element-wise maximum
                                let b_hir = self.lower_expr(&args[0].value, ctx)?;
                                return Ok(HirExpr {
                                    kind: HirExprKind::GpuIntrinsic {
                                        intrinsic: GpuIntrinsicKind::SimdMaxVec,
                                        args: vec![receiver_hir, b_hir],
                                    },
                                    ty: simd_ty,
                                });
                            } else {
                                return Err(LowerError::Unsupported(
                                    "vec.max() or vec.max(b) expected".into(),
                                ));
                            }
                        }
                        "all" => {
                            if !args.is_empty() {
                                return Err(LowerError::Unsupported(
                                    "vec.all() takes no arguments".into(),
                                ));
                            }
                            // all() only valid for bool vectors
                            if element != TypeId::BOOL {
                                return Err(LowerError::Unsupported(
                                    "vec.all() only valid for bool vectors".into(),
                                ));
                            }
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdAll,
                                    args: vec![receiver_hir],
                                },
                                ty: TypeId::BOOL,
                            });
                        }
                        "any" => {
                            if !args.is_empty() {
                                return Err(LowerError::Unsupported(
                                    "vec.any() takes no arguments".into(),
                                ));
                            }
                            // any() only valid for bool vectors
                            if element != TypeId::BOOL {
                                return Err(LowerError::Unsupported(
                                    "vec.any() only valid for bool vectors".into(),
                                ));
                            }
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdAny,
                                    args: vec![receiver_hir],
                                },
                                ty: TypeId::BOOL,
                            });
                        }
                        "with" => {
                            // v.with(idx, val) -> new vector with lane replaced
                            if args.len() != 2 {
                                return Err(LowerError::Unsupported(
                                    "vec.with(idx, val) takes exactly 2 arguments".into(),
                                ));
                            }
                            let idx_hir = self.lower_expr(&args[0].value, ctx)?;
                            let val_hir = self.lower_expr(&args[1].value, ctx)?;
                            // Return the same SIMD type
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdWith,
                                    args: vec![receiver_hir, idx_hir, val_hir],
                                },
                                ty: simd_ty,
                            });
                        }
                        "sqrt" => {
                            if !args.is_empty() {
                                return Err(LowerError::Unsupported(
                                    "vec.sqrt() takes no arguments".into(),
                                ));
                            }
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdSqrt,
                                    args: vec![receiver_hir],
                                },
                                ty: simd_ty,
                            });
                        }
                        "abs" => {
                            if !args.is_empty() {
                                return Err(LowerError::Unsupported(
                                    "vec.abs() takes no arguments".into(),
                                ));
                            }
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdAbs,
                                    args: vec![receiver_hir],
                                },
                                ty: simd_ty,
                            });
                        }
                        "floor" => {
                            if !args.is_empty() {
                                return Err(LowerError::Unsupported(
                                    "vec.floor() takes no arguments".into(),
                                ));
                            }
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdFloor,
                                    args: vec![receiver_hir],
                                },
                                ty: simd_ty,
                            });
                        }
                        "ceil" => {
                            if !args.is_empty() {
                                return Err(LowerError::Unsupported(
                                    "vec.ceil() takes no arguments".into(),
                                ));
                            }
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdCeil,
                                    args: vec![receiver_hir],
                                },
                                ty: simd_ty,
                            });
                        }
                        "round" => {
                            if !args.is_empty() {
                                return Err(LowerError::Unsupported(
                                    "vec.round() takes no arguments".into(),
                                ));
                            }
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdRound,
                                    args: vec![receiver_hir],
                                },
                                ty: simd_ty,
                            });
                        }
                        "shuffle" => {
                            // v.shuffle([3, 2, 1, 0]) - reorder lanes
                            if args.len() != 1 {
                                return Err(LowerError::Unsupported(
                                    "vec.shuffle() requires exactly one argument (indices array)"
                                        .into(),
                                ));
                            }
                            let indices_hir = self.lower_expr(&args[0].value, ctx)?;
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdShuffle,
                                    args: vec![receiver_hir, indices_hir],
                                },
                                ty: simd_ty,
                            });
                        }
                        "blend" => {
                            // a.blend(b, [0, 1, 4, 5]) - merge two vectors
                            if args.len() != 2 {
                                return Err(LowerError::Unsupported(
                                    "vec.blend() requires two arguments (other vector and indices array)".into(),
                                ));
                            }
                            let other_hir = self.lower_expr(&args[0].value, ctx)?;
                            let indices_hir = self.lower_expr(&args[1].value, ctx)?;
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdBlend,
                                    args: vec![receiver_hir, other_hir, indices_hir],
                                },
                                ty: simd_ty,
                            });
                        }
                        "select" => {
                            // mask.select(a, b) - select from a where true, b where false
                            if args.len() != 2 {
                                return Err(LowerError::Unsupported(
                                    "mask.select(if_true, if_false) requires exactly two arguments"
                                        .into(),
                                ));
                            }
                            let if_true_hir = self.lower_expr(&args[0].value, ctx)?;
                            let if_false_hir = self.lower_expr(&args[1].value, ctx)?;
                            // Result type is the same as the if_true argument type
                            let result_ty = if_true_hir.ty;
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdSelect,
                                    args: vec![receiver_hir, if_true_hir, if_false_hir],
                                },
                                ty: result_ty,
                            });
                        }
                        "store" => {
                            // v.store(arr, offset) - store vector to array
                            if args.len() != 2 {
                                return Err(LowerError::Unsupported(
                                    "vec.store(array, offset) requires exactly two arguments".into(),
                                ));
                            }
                            let array_hir = self.lower_expr(&args[0].value, ctx)?;
                            let offset_hir = self.lower_expr(&args[1].value, ctx)?;
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdStore,
                                    args: vec![receiver_hir, array_hir, offset_hir],
                                },
                                ty: TypeId::VOID,
                            });
                        }
                        "scatter" => {
                            // v.scatter(arr, indices) - scatter vector to array at indices
                            if args.len() != 2 {
                                return Err(LowerError::Unsupported(
                                    "vec.scatter(array, indices) requires exactly two arguments".into(),
                                ));
                            }
                            let array_hir = self.lower_expr(&args[0].value, ctx)?;
                            let indices_hir = self.lower_expr(&args[1].value, ctx)?;
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdScatter,
                                    args: vec![receiver_hir, array_hir, indices_hir],
                                },
                                ty: TypeId::VOID,
                            });
                        }
                        "store_masked" => {
                            // v.store_masked(arr, offset, mask) - store only where mask is true
                            if args.len() != 3 {
                                return Err(LowerError::Unsupported(
                                    "vec.store_masked(array, offset, mask) requires exactly three arguments".into(),
                                ));
                            }
                            let array_hir = self.lower_expr(&args[0].value, ctx)?;
                            let offset_hir = self.lower_expr(&args[1].value, ctx)?;
                            let mask_hir = self.lower_expr(&args[2].value, ctx)?;
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdMaskedStore,
                                    args: vec![receiver_hir, array_hir, offset_hir, mask_hir],
                                },
                                ty: TypeId::VOID,
                            });
                        }
                        "fma" => {
                            // v.fma(b, c) - fused multiply-add: v * b + c
                            if args.len() != 2 {
                                return Err(LowerError::Unsupported(
                                    "vec.fma(b, c) requires exactly two arguments".into(),
                                ));
                            }
                            let b_hir = self.lower_expr(&args[0].value, ctx)?;
                            let c_hir = self.lower_expr(&args[1].value, ctx)?;
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdFma,
                                    args: vec![receiver_hir, b_hir, c_hir],
                                },
                                ty: simd_ty,
                            });
                        }
                        "recip" => {
                            // v.recip() - reciprocal: 1.0 / v
                            if !args.is_empty() {
                                return Err(LowerError::Unsupported(
                                    "vec.recip() takes no arguments".into(),
                                ));
                            }
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdRecip,
                                    args: vec![receiver_hir],
                                },
                                ty: simd_ty,
                            });
                        }
                        "clamp" => {
                            // v.clamp(lo, hi) - element-wise clamp to range
                            if args.len() != 2 {
                                return Err(LowerError::Unsupported(
                                    "vec.clamp(lo, hi) requires exactly two arguments".into(),
                                ));
                            }
                            let lo_hir = self.lower_expr(&args[0].value, ctx)?;
                            let hi_hir = self.lower_expr(&args[1].value, ctx)?;
                            return Ok(HirExpr {
                                kind: HirExprKind::GpuIntrinsic {
                                    intrinsic: GpuIntrinsicKind::SimdClamp,
                                    args: vec![receiver_hir, lo_hir, hi_hir],
                                },
                                ty: simd_ty,
                            });
                        }
                        _ => {}
                    }
                }

                // For now, regular method calls are unsupported in native compilation
                Err(LowerError::Unsupported(format!(
                    "Method call {:?}.{}() not supported in native compilation",
                    receiver, method
                )))
            }

            Expr::StructInit { name, fields } => {
                // Resolve struct type (handle "Self" keyword)
                let struct_ty = if name == "Self" {
                    if let Some(class_ty) = self.current_class_type {
                        class_ty
                    } else {
                        return Err(LowerError::UnknownType(
                            "Self used outside of class/struct context".to_string()
                        ));
                    }
                } else {
                    self.module
                        .types
                        .lookup(name)
                        .ok_or_else(|| LowerError::UnknownType(name.clone()))?
                };

                // Lower field initializers (in order)
                let mut fields_hir = Vec::new();
                for (_field_name, field_expr) in fields {
                    let field_hir = self.lower_expr(field_expr, ctx)?;
                    fields_hir.push(field_hir);
                }

                Ok(HirExpr {
                    kind: HirExprKind::StructInit {
                        ty: struct_ty,
                        fields: fields_hir,
                    },
                    ty: struct_ty,
                })
            }

            _ => Err(LowerError::Unsupported(format!("{:?}", expr))),
        }
    }
}

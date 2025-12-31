mod access;
mod calls;
mod collections;
mod contracts;
mod control;
mod helpers;
mod inference;
mod literals;
mod memory;
mod operators;

use simple_parser::{self as ast, ast::ReferenceCapability, Expr};

use crate::value::BUILTIN_SPAWN;
use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    /// Main expression lowering dispatcher
    ///
    /// This method delegates to specialized helper methods for each expression type,
    /// keeping the dispatch logic clean and maintainable.
    pub(in crate::hir::lower) fn lower_expr(&mut self, expr: &Expr, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
        match expr {
            Expr::Integer(_) | Expr::Float(_) | Expr::String(_) | Expr::Bool(_) | Expr::Nil => {
                self.lower_literal(expr)
            }
            Expr::FString(parts) => self.lower_fstring(parts),
            Expr::Identifier(name) => self.lower_identifier(name, ctx),
            Expr::Binary { op, left, right } => self.lower_binary(op, left, right, ctx),
            Expr::Unary { op, operand } => self.lower_unary(op, operand, ctx),
            Expr::Call { callee, args } => self.lower_call(callee, args, ctx),
            Expr::FieldAccess { receiver, field } => self.lower_field_access(receiver, field, ctx),
            Expr::Index { receiver, index } => self.lower_index(receiver, index, ctx),
            Expr::Tuple(exprs) => self.lower_tuple(exprs, ctx),
            Expr::Array(exprs) => self.lower_array(exprs, ctx),
            Expr::VecLiteral(exprs) => self.lower_vec_literal(exprs, ctx),
            Expr::If { condition, then_branch, else_branch } => {
                self.lower_if(condition, then_branch, else_branch.as_deref(), ctx)
            }
            Expr::Lambda { params, body, .. } => self.lower_lambda(params, body, ctx),
            Expr::Yield(value) => self.lower_yield(value.as_deref(), ctx),
            Expr::ContractResult => self.lower_contract_result(ctx),
            Expr::ContractOld(inner) => self.lower_contract_old(inner, ctx),
            Expr::New { kind, expr } => self.lower_new(kind, expr, ctx),
            Expr::MethodCall { receiver, method, args } => {
                self.lower_method_call(receiver, method, args, ctx)
            }
            Expr::StructInit { name, fields } => self.lower_struct_init(name, fields, ctx),
            // Simple Math: Grid and Tensor literals (#1920-#1929)
            Expr::GridLiteral { rows, device } => self.lower_grid_literal(rows, device, ctx),
            Expr::TensorLiteral { dtype, dims, mode, device } => {
                self.lower_tensor_literal(dtype, dims, mode, device, ctx)
            }
            _ => Err(LowerError::Unsupported(format!("{:?}", expr))),
        }
    }


    // ============================================================================
    // Identifier expressions
    // ============================================================================

    fn lower_identifier(&self, name: &str, ctx: &mut FunctionContext) -> LowerResult<HirExpr> {
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
                kind: HirExprKind::Global(name.to_string()),
                ty,
            })
        } else {
            Err(LowerError::UnknownVariable(name.to_string()))
        }
    }






    // ============================================================================
    // Method calls (largest section - GPU/SIMD intrinsics)
    // ============================================================================

    fn lower_method_call(
        &mut self,
        receiver: &Expr,
        method: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Check for intrinsic calls on special identifiers
        if let Expr::Identifier(recv_name) = receiver {
            // this.* intrinsics
            if recv_name == "this" {
                if let Some(result) = self.lower_this_method(method, args)? {
                    return Ok(result);
                }
            }
            // thread_group.* intrinsics
            else if recv_name == "thread_group" {
                if let Some(result) = self.lower_thread_group_method(method, args)? {
                    return Ok(result);
                }
            }
            // gpu.* intrinsics
            else if recv_name == "gpu" {
                if let Some(result) = self.lower_gpu_method(method, args, ctx)? {
                    return Ok(result);
                }
            }
            // SIMD type static methods: f32x4.load(), etc.
            else if matches!(recv_name.as_str(), "f32x4" | "f64x4" | "i32x4" | "i64x4") {
                if let Some(result) = self.lower_simd_static_method(recv_name, method, args, ctx)? {
                    return Ok(result);
                }
            }
            // Static method calls on classes/structs
            else if self.module.types.lookup(recv_name).is_some() {
                return self.lower_static_method_call(recv_name, method, args, ctx);
            }
        }

        // Check for SIMD vector instance methods
        let receiver_hir = self.lower_expr(receiver, ctx)?;
        if let Some(HirType::Simd { .. }) = self.module.types.get(receiver_hir.ty) {
            if let Some(result) = self.lower_simd_instance_method(&receiver_hir, method, args, ctx)? {
                return Ok(result);
            }
        }

        // For now, regular method calls are unsupported in native compilation
        Err(LowerError::Unsupported(format!(
            "Method call {:?}.{}() not supported in native compilation",
            receiver, method
        )))
    }

    /// Handle this.index(), this.thread_index(), this.group_index()
    fn lower_this_method(&self, method: &str, args: &[ast::Argument]) -> LowerResult<Option<HirExpr>> {
        if !args.is_empty() {
            return Err(LowerError::Unsupported(
                format!("this.{}() takes no arguments", method)
            ));
        }

        let intrinsic = match method {
            "index" => GpuIntrinsicKind::SimdIndex,
            "thread_index" => GpuIntrinsicKind::SimdThreadIndex,
            "group_index" => GpuIntrinsicKind::SimdGroupIndex,
            _ => return Ok(None),
        };

        Ok(Some(HirExpr {
            kind: HirExprKind::GpuIntrinsic {
                intrinsic,
                args: vec![],
            },
            ty: TypeId::I64,
        }))
    }

    /// Handle thread_group.barrier()
    fn lower_thread_group_method(&self, method: &str, args: &[ast::Argument]) -> LowerResult<Option<HirExpr>> {
        if method != "barrier" {
            return Err(LowerError::Unsupported(format!(
                "unknown thread_group method: {}",
                method
            )));
        }

        if !args.is_empty() {
            return Err(LowerError::Unsupported(
                "thread_group.barrier() takes no arguments".to_string()
            ));
        }

        Ok(Some(HirExpr {
            kind: HirExprKind::GpuIntrinsic {
                intrinsic: GpuIntrinsicKind::Barrier,
                args: vec![],
            },
            ty: TypeId::VOID,
        }))
    }

    /// Handle gpu.* methods (global_id, local_id, barrier, atomics, etc.)
    fn lower_gpu_method(
        &mut self,
        method: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        match method {
            // Dimension query intrinsics
            "global_id" | "local_id" | "group_id" | "global_size" | "local_size" | "num_groups" => {
                let intrinsic = match method {
                    "global_id" => GpuIntrinsicKind::GlobalId,
                    "local_id" => GpuIntrinsicKind::LocalId,
                    "group_id" => GpuIntrinsicKind::GroupId,
                    "global_size" => GpuIntrinsicKind::GlobalSize,
                    "local_size" => GpuIntrinsicKind::LocalSize,
                    "num_groups" => GpuIntrinsicKind::NumGroups,
                    _ => unreachable!(),
                };
                let dim_arg = self.lower_gpu_dim_arg(args, ctx)?;
                Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic,
                        args: dim_arg,
                    },
                    ty: TypeId::I64,
                }))
            }
            // Synchronization intrinsics
            "barrier" => {
                if !args.is_empty() {
                    return Err(LowerError::Unsupported(
                        "gpu.barrier() takes no arguments".to_string()
                    ));
                }
                Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::Barrier,
                        args: vec![],
                    },
                    ty: TypeId::VOID,
                }))
            }
            "mem_fence" => {
                if !args.is_empty() {
                    return Err(LowerError::Unsupported(
                        "gpu.mem_fence() takes no arguments".to_string()
                    ));
                }
                Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::MemFence,
                        args: vec![],
                    },
                    ty: TypeId::VOID,
                }))
            }
            // Atomic operations
            "atomic_add" | "atomic_sub" | "atomic_min" | "atomic_max"
            | "atomic_and" | "atomic_or" | "atomic_xor" | "atomic_exchange" => {
                self.lower_gpu_atomic_binary(method, args, ctx).map(Some)
            }
            "atomic_compare_exchange" => {
                self.lower_gpu_atomic_cas(args, ctx).map(Some)
            }
            _ => Ok(None),
        }
    }

    fn lower_gpu_atomic_binary(
        &mut self,
        method: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        if args.len() != 2 {
            return Err(LowerError::Unsupported(format!(
                "gpu.{}(ptr, val) requires exactly 2 arguments",
                method
            )));
        }
        let ptr_hir = self.lower_expr(&args[0].value, ctx)?;
        let val_hir = self.lower_expr(&args[1].value, ctx)?;
        let intrinsic = match method {
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
        Ok(HirExpr {
            kind: HirExprKind::GpuIntrinsic {
                intrinsic,
                args: vec![ptr_hir, val_hir],
            },
            ty: TypeId::I64,
        })
    }

    fn lower_gpu_atomic_cas(
        &mut self,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        if args.len() != 3 {
            return Err(LowerError::Unsupported(
                "gpu.atomic_compare_exchange(ptr, expected, desired) requires exactly 3 arguments".to_string(),
            ));
        }
        let ptr_hir = self.lower_expr(&args[0].value, ctx)?;
        let expected_hir = self.lower_expr(&args[1].value, ctx)?;
        let desired_hir = self.lower_expr(&args[2].value, ctx)?;
        Ok(HirExpr {
            kind: HirExprKind::GpuIntrinsic {
                intrinsic: GpuIntrinsicKind::GpuAtomicCompareExchange,
                args: vec![ptr_hir, expected_hir, desired_hir],
            },
            ty: TypeId::I64,
        })
    }

    /// Handle f32x4.load(), f32x4.gather(), etc.
    fn lower_simd_static_method(
        &mut self,
        type_name: &str,
        method: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        let simd_ty = match type_name {
            "f32x4" => self.module.types.register(HirType::Simd { lanes: 4, element: TypeId::F32 }),
            "f64x4" => self.module.types.register(HirType::Simd { lanes: 4, element: TypeId::F64 }),
            "i32x4" => self.module.types.register(HirType::Simd { lanes: 4, element: TypeId::I32 }),
            "i64x4" => self.module.types.register(HirType::Simd { lanes: 4, element: TypeId::I64 }),
            _ => unreachable!(),
        };

        match method {
            "load" => {
                if args.len() != 2 {
                    return Err(LowerError::Unsupported(
                        format!("{}.load(array, offset) requires exactly 2 arguments", type_name),
                    ));
                }
                let array_hir = self.lower_expr(&args[0].value, ctx)?;
                let offset_hir = self.lower_expr(&args[1].value, ctx)?;
                Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::SimdLoad,
                        args: vec![array_hir, offset_hir],
                    },
                    ty: simd_ty,
                }))
            }
            "gather" => {
                if args.len() != 2 {
                    return Err(LowerError::Unsupported(
                        format!("{}.gather(array, indices) requires exactly 2 arguments", type_name),
                    ));
                }
                let array_hir = self.lower_expr(&args[0].value, ctx)?;
                let indices_hir = self.lower_expr(&args[1].value, ctx)?;
                Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::SimdGather,
                        args: vec![array_hir, indices_hir],
                    },
                    ty: simd_ty,
                }))
            }
            "load_masked" => {
                if args.len() != 4 {
                    return Err(LowerError::Unsupported(
                        format!("{}.load_masked(array, offset, mask, default) requires exactly 4 arguments", type_name),
                    ));
                }
                let array_hir = self.lower_expr(&args[0].value, ctx)?;
                let offset_hir = self.lower_expr(&args[1].value, ctx)?;
                let mask_hir = self.lower_expr(&args[2].value, ctx)?;
                let default_hir = self.lower_expr(&args[3].value, ctx)?;
                Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::SimdMaskedLoad,
                        args: vec![array_hir, offset_hir, mask_hir, default_hir],
                    },
                    ty: simd_ty,
                }))
            }
            _ => Ok(None),
        }
    }

    /// Handle static method calls like ClassName.method()
    fn lower_static_method_call(
        &mut self,
        class_name: &str,
        method: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let qualified_name = format!("{}.{}", class_name, method);

        let mut args_hir = Vec::new();
        for arg in args {
            args_hir.push(self.lower_expr(&arg.value, ctx)?);
        }

        let func_expr = HirExpr {
            kind: HirExprKind::Global(qualified_name),
            ty: TypeId::VOID,
        };

        Ok(HirExpr {
            kind: HirExprKind::Call {
                func: Box::new(func_expr),
                args: args_hir,
            },
            ty: TypeId::VOID,
        })
    }

    /// Handle SIMD vector instance methods (sum, product, min, max, etc.)
    fn lower_simd_instance_method(
        &mut self,
        receiver_hir: &HirExpr,
        method: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        let simd_ty = receiver_hir.ty;
        if let Some(HirType::Simd { element, .. }) = self.module.types.get(simd_ty) {
            let element = *element;

            // Reduction methods
            if let Some(result) = self.lower_simd_reduction(receiver_hir, method, element, args)? {
                return Ok(Some(result));
            }

            // Element-wise operations
            if let Some(result) = self.lower_simd_elementwise(receiver_hir, method, simd_ty, element, args, ctx)? {
                return Ok(Some(result));
            }

            // Memory operations
            if let Some(result) = self.lower_simd_memory(receiver_hir, method, simd_ty, args, ctx)? {
                return Ok(Some(result));
            }
        }
        Ok(None)
    }

    fn lower_simd_reduction(
        &self,
        receiver_hir: &HirExpr,
        method: &str,
        element: TypeId,
        args: &[ast::Argument],
    ) -> LowerResult<Option<HirExpr>> {
        let (intrinsic, requires_bool) = match method {
            "sum" => (GpuIntrinsicKind::SimdSum, false),
            "product" => (GpuIntrinsicKind::SimdProduct, false),
            "min" if args.is_empty() => (GpuIntrinsicKind::SimdMin, false),
            "max" if args.is_empty() => (GpuIntrinsicKind::SimdMax, false),
            "all" => (GpuIntrinsicKind::SimdAll, true),
            "any" => (GpuIntrinsicKind::SimdAny, true),
            _ => return Ok(None),
        };

        if !args.is_empty() && method != "min" && method != "max" {
            return Err(LowerError::Unsupported(
                format!("vec.{}() takes no arguments", method)
            ));
        }

        if requires_bool && element != TypeId::BOOL {
            return Err(LowerError::Unsupported(
                format!("vec.{}() only valid for bool vectors", method)
            ));
        }

        let result_ty = if requires_bool { TypeId::BOOL } else { element };

        Ok(Some(HirExpr {
            kind: HirExprKind::GpuIntrinsic {
                intrinsic,
                args: vec![receiver_hir.clone()],
            },
            ty: result_ty,
        }))
    }

    fn lower_simd_elementwise(
        &mut self,
        receiver_hir: &HirExpr,
        method: &str,
        simd_ty: TypeId,
        _element: TypeId,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        let intrinsic = match method {
            "min" if args.len() == 1 => GpuIntrinsicKind::SimdMinVec,
            "max" if args.len() == 1 => GpuIntrinsicKind::SimdMaxVec,
            "sqrt" => GpuIntrinsicKind::SimdSqrt,
            "abs" => GpuIntrinsicKind::SimdAbs,
            "floor" => GpuIntrinsicKind::SimdFloor,
            "ceil" => GpuIntrinsicKind::SimdCeil,
            "round" => GpuIntrinsicKind::SimdRound,
            "recip" => GpuIntrinsicKind::SimdRecip,
            "with" => {
                if args.len() != 2 {
                    return Err(LowerError::Unsupported(
                        "vec.with(idx, val) takes exactly 2 arguments".to_string()
                    ));
                }
                let idx_hir = self.lower_expr(&args[0].value, ctx)?;
                let val_hir = self.lower_expr(&args[1].value, ctx)?;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::SimdWith,
                        args: vec![receiver_hir.clone(), idx_hir, val_hir],
                    },
                    ty: simd_ty,
                }));
            }
            "shuffle" => {
                if args.len() != 1 {
                    return Err(LowerError::Unsupported(
                        "vec.shuffle() requires exactly one argument (indices array)".to_string(),
                    ));
                }
                let indices_hir = self.lower_expr(&args[0].value, ctx)?;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::SimdShuffle,
                        args: vec![receiver_hir.clone(), indices_hir],
                    },
                    ty: simd_ty,
                }));
            }
            "blend" => {
                if args.len() != 2 {
                    return Err(LowerError::Unsupported(
                        "vec.blend() requires two arguments (other vector and indices array)".to_string(),
                    ));
                }
                let other_hir = self.lower_expr(&args[0].value, ctx)?;
                let indices_hir = self.lower_expr(&args[1].value, ctx)?;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::SimdBlend,
                        args: vec![receiver_hir.clone(), other_hir, indices_hir],
                    },
                    ty: simd_ty,
                }));
            }
            "select" => {
                if args.len() != 2 {
                    return Err(LowerError::Unsupported(
                        "mask.select(if_true, if_false) requires exactly two arguments".to_string(),
                    ));
                }
                let if_true_hir = self.lower_expr(&args[0].value, ctx)?;
                let if_false_hir = self.lower_expr(&args[1].value, ctx)?;
                let result_ty = if_true_hir.ty;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::SimdSelect,
                        args: vec![receiver_hir.clone(), if_true_hir, if_false_hir],
                    },
                    ty: result_ty,
                }));
            }
            "fma" => {
                if args.len() != 2 {
                    return Err(LowerError::Unsupported(
                        "vec.fma(b, c) requires exactly two arguments".to_string()
                    ));
                }
                let b_hir = self.lower_expr(&args[0].value, ctx)?;
                let c_hir = self.lower_expr(&args[1].value, ctx)?;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::SimdFma,
                        args: vec![receiver_hir.clone(), b_hir, c_hir],
                    },
                    ty: simd_ty,
                }));
            }
            "clamp" => {
                if args.len() != 2 {
                    return Err(LowerError::Unsupported(
                        "vec.clamp(lo, hi) requires exactly two arguments".to_string()
                    ));
                }
                let lo_hir = self.lower_expr(&args[0].value, ctx)?;
                let hi_hir = self.lower_expr(&args[1].value, ctx)?;
                return Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::SimdClamp,
                        args: vec![receiver_hir.clone(), lo_hir, hi_hir],
                    },
                    ty: simd_ty,
                }));
            }
            _ => return Ok(None),
        };

        // For single-argument operations (min/max with arg, or no-arg operations)
        let mut intrinsic_args = vec![receiver_hir.clone()];
        if !args.is_empty() {
            intrinsic_args.push(self.lower_expr(&args[0].value, ctx)?);
        }

        Ok(Some(HirExpr {
            kind: HirExprKind::GpuIntrinsic {
                intrinsic,
                args: intrinsic_args,
            },
            ty: simd_ty,
        }))
    }

    fn lower_simd_memory(
        &mut self,
        receiver_hir: &HirExpr,
        method: &str,
        simd_ty: TypeId,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        match method {
            "store" => {
                if args.len() != 2 {
                    return Err(LowerError::Unsupported(
                        "vec.store(array, offset) requires exactly two arguments".to_string(),
                    ));
                }
                let array_hir = self.lower_expr(&args[0].value, ctx)?;
                let offset_hir = self.lower_expr(&args[1].value, ctx)?;
                Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::SimdStore,
                        args: vec![receiver_hir.clone(), array_hir, offset_hir],
                    },
                    ty: TypeId::VOID,
                }))
            }
            "scatter" => {
                if args.len() != 2 {
                    return Err(LowerError::Unsupported(
                        "vec.scatter(array, indices) requires exactly two arguments".to_string(),
                    ));
                }
                let array_hir = self.lower_expr(&args[0].value, ctx)?;
                let indices_hir = self.lower_expr(&args[1].value, ctx)?;
                Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::SimdScatter,
                        args: vec![receiver_hir.clone(), array_hir, indices_hir],
                    },
                    ty: TypeId::VOID,
                }))
            }
            "store_masked" => {
                if args.len() != 3 {
                    return Err(LowerError::Unsupported(
                        "vec.store_masked(array, offset, mask) requires exactly three arguments".to_string(),
                    ));
                }
                let array_hir = self.lower_expr(&args[0].value, ctx)?;
                let offset_hir = self.lower_expr(&args[1].value, ctx)?;
                let mask_hir = self.lower_expr(&args[2].value, ctx)?;
                Ok(Some(HirExpr {
                    kind: HirExprKind::GpuIntrinsic {
                        intrinsic: GpuIntrinsicKind::SimdMaskedStore,
                        args: vec![receiver_hir.clone(), array_hir, offset_hir, mask_hir],
                    },
                    ty: TypeId::VOID,
                }))
            }
            _ => Ok(None),
        }
    }

    // ============================================================================
    // Struct initialization
    // ============================================================================

    fn lower_struct_init(
        &mut self,
        name: &str,
        fields: &[(String, Expr)],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
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
                .ok_or_else(|| LowerError::UnknownType(name.to_string()))?
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

    // ============================================================================
    // Simple Math: Grid and Tensor literals (#1920-#1929)
    // ============================================================================

    /// Lower grid literal to torch.tensor([[...]]) call
    ///
    /// Example:
    /// ```simple
    /// A = grid:
    ///     | 3 | 1 |
    ///     | 1 | 2 |
    /// ```
    /// Becomes: torch.tensor([[3, 1], [1, 2]])
    ///
    /// With device:
    /// ```simple
    /// A = grid device="cuda":
    ///     | 3 | 1 |
    /// ```
    /// Becomes: torch.tensor([[3, 1]], device="cuda")
    fn lower_grid_literal(
        &mut self,
        rows: &[Vec<Box<Expr>>],
        device: &Option<String>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Convert each row to an array
        let mut row_arrays = Vec::new();
        for row in rows {
            let mut cell_exprs = Vec::new();
            for cell in row {
                cell_exprs.push(self.lower_expr(cell.as_ref(), ctx)?);
            }

            // Create array type for this row
            let elem_ty = if let Some(first) = cell_exprs.first() {
                first.ty
            } else {
                TypeId::VOID
            };
            let row_ty = self.module.types.register(HirType::Array {
                element: elem_ty,
                size: Some(cell_exprs.len()),
            });

            row_arrays.push(HirExpr {
                kind: HirExprKind::Array(cell_exprs),
                ty: row_ty,
            });
        }

        // Create nested array type (array of arrays)
        let row_ty = if let Some(first) = row_arrays.first() {
            first.ty
        } else {
            TypeId::VOID
        };
        let grid_ty = self.module.types.register(HirType::Array {
            element: row_ty,
            size: Some(row_arrays.len()),
        });

        // Create the nested array expression
        let nested_array = HirExpr {
            kind: HirExprKind::Array(row_arrays),
            ty: grid_ty,
        };

        // Build arguments: [nested_array] or [nested_array, device="..."]
        let mut args = vec![nested_array];

        // Add device parameter if specified
        if let Some(dev) = device {
            // Create device named argument
            // For now, we'll just append it as a regular argument
            // The interpreter will handle the device parameter
            args.push(HirExpr {
                kind: HirExprKind::String(dev.clone()),
                ty: TypeId::STRING,
            });
        }

        // Create call to torch.tensor(...)
        let func_name = "torch.tensor".to_string();
        let func_expr = HirExpr {
            kind: HirExprKind::Global(func_name),
            ty: TypeId::VOID, // Function type, will be resolved at runtime
        };

        Ok(HirExpr {
            kind: HirExprKind::Call {
                func: Box::new(func_expr),
                args,
            },
            ty: TypeId::I64, // PyTorch tensors are represented as handles (i64/u64)
        })
    }

    /// Lower tensor literal to torch.tensor(...) call
    ///
    /// Handles both slice and flat modes:
    ///
    /// Slice mode example:
    /// ```simple
    /// tensor K: Float [d=2, h=3, w=4]
    ///     slice d=0:
    ///         | h\w | 0 | 1 | 2 | 3 |
    ///         | 0   | 1 | 2 | 3 | 4 |
    ///     slice d=1:
    ///         | h\w | 0 | 1 | 2 | 3 |
    ///         | 0   | 5 | 6 | 7 | 8 |
    /// ```
    ///
    /// Flat mode example:
    /// ```simple
    /// tensor K: Float [d=2, h=3, w=4]
    ///     default: 0
    ///     flat:
    ///         | d | h | w | value |
    ///         | 0 | 0 | 0 | 1.0   |
    ///         | 1 | 2 | 3 | 2.0   |
    /// ```
    fn lower_tensor_literal(
        &mut self,
        _dtype: &str,
        dims: &[(String, i64)],
        mode: &Box<ast::TensorMode>,
        device: &Option<String>,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        use ast::TensorMode;

        match mode.as_ref() {
            TensorMode::Slice(slices) => {
                // Reconstruct N-D tensor from 2D slices
                let tensor_data = self.reconstruct_tensor_from_slices(slices, dims, ctx)?;
                self.create_torch_tensor_call(tensor_data, device, ctx)
            }
            TensorMode::Flat { default, values } => {
                // Create sparse tensor from coordinate list
                let tensor_data = self.create_sparse_tensor(values, default.as_ref(), dims, ctx)?;
                self.create_torch_tensor_call(tensor_data, device, ctx)
            }
        }
    }

    /// Reconstruct N-dimensional tensor from slice blocks
    ///
    /// Recursively builds nested arrays from slice specifications.
    /// For example, a 3D tensor with slices along dimension 0 will
    /// create an array where each element is a 2D array (the slice content).
    fn reconstruct_tensor_from_slices(
        &mut self,
        slices: &[ast::TensorSlice],
        _dims: &[(String, i64)],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        use ast::TensorSliceContent;

        let mut slice_arrays = Vec::new();

        for slice in slices {
            let slice_expr = match &slice.content {
                TensorSliceContent::GridRows(rows) => {
                    // Base case: 2D grid rows
                    let mut row_arrays = Vec::new();
                    for row in rows {
                        let mut cell_exprs = Vec::new();
                        for cell in row {
                            cell_exprs.push(self.lower_expr(cell.as_ref(), ctx)?);
                        }

                        let elem_ty = if let Some(first) = cell_exprs.first() {
                            first.ty
                        } else {
                            TypeId::VOID
                        };
                        let row_ty = self.module.types.register(HirType::Array {
                            element: elem_ty,
                            size: Some(cell_exprs.len()),
                        });

                        row_arrays.push(HirExpr {
                            kind: HirExprKind::Array(cell_exprs),
                            ty: row_ty,
                        });
                    }

                    let row_ty = if let Some(first) = row_arrays.first() {
                        first.ty
                    } else {
                        TypeId::VOID
                    };
                    let grid_ty = self.module.types.register(HirType::Array {
                        element: row_ty,
                        size: Some(row_arrays.len()),
                    });

                    HirExpr {
                        kind: HirExprKind::Array(row_arrays),
                        ty: grid_ty,
                    }
                }
                TensorSliceContent::NestedSlices(nested) => {
                    // Recursive case: nested slices for higher dimensions
                    self.reconstruct_tensor_from_slices(nested, _dims, ctx)?
                }
            };

            slice_arrays.push(slice_expr);
        }

        // Create array type for all slices
        let slice_ty = if let Some(first) = slice_arrays.first() {
            first.ty
        } else {
            TypeId::VOID
        };
        let tensor_ty = self.module.types.register(HirType::Array {
            element: slice_ty,
            size: Some(slice_arrays.len()),
        });

        Ok(HirExpr {
            kind: HirExprKind::Array(slice_arrays),
            ty: tensor_ty,
        })
    }

    /// Create sparse tensor from flat coordinate representation
    ///
    /// Builds a dense array initialized with the default value,
    /// then fills in the specified coordinates with their values.
    ///
    /// For now, this creates a full dense array. A future optimization
    /// could use PyTorch's sparse tensor format for large tensors.
    fn create_sparse_tensor(
        &mut self,
        values: &[Vec<Box<Expr>>],
        default: Option<&Box<Expr>>,
        dims: &[(String, i64)],
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // For now, we'll convert flat mode to dense representation
        // TODO: Future optimization - use torch.sparse_coo_tensor for large sparse tensors

        // Get default value or use 0
        let default_expr = if let Some(def) = default {
            self.lower_expr(def.as_ref(), ctx)?
        } else {
            HirExpr {
                kind: HirExprKind::Integer(0),
                ty: TypeId::I64,
            }
        };

        // For now, create a simple error - full sparse tensor support will be added later
        // This allows the code to compile while we implement the feature incrementally
        Err(LowerError::Unsupported(
            "Sparse tensor (flat mode) not yet fully implemented. Use slice mode for now.".to_string()
        ))
    }

    /// Create a torch.tensor(...) call with optional device parameter
    fn create_torch_tensor_call(
        &mut self,
        data: HirExpr,
        device: &Option<String>,
        _ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        let mut args = vec![data];

        if let Some(dev) = device {
            args.push(HirExpr {
                kind: HirExprKind::String(dev.clone()),
                ty: TypeId::STRING,
            });
        }

        let func_name = "torch.tensor".to_string();
        let func_expr = HirExpr {
            kind: HirExprKind::Global(func_name),
            ty: TypeId::VOID,
        };

        Ok(HirExpr {
            kind: HirExprKind::Call {
                func: Box::new(func_expr),
                args,
            },
            ty: TypeId::I64, // Tensor handle
        })
    }
}

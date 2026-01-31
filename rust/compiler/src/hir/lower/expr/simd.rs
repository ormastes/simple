//! SIMD and GPU intrinsic expression lowering
//!
//! This module contains expression lowering logic for:
//! - GPU intrinsics (global_id, local_id, barriers, atomics)
//! - SIMD vector operations (reductions, element-wise, memory ops)
//! - SIMD static and instance methods

use simple_parser::{self as ast, Expr};

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    /// Register a SIMD type from its string name (f32x4, i32x4, etc.)
    pub(super) fn register_simd_type(&mut self, type_name: &str) -> TypeId {
        match type_name {
            "f32x4" => self.module.types.register(HirType::Simd {
                lanes: 4,
                element: TypeId::F32,
            }),
            "f64x4" => self.module.types.register(HirType::Simd {
                lanes: 4,
                element: TypeId::F64,
            }),
            "i32x4" => self.module.types.register(HirType::Simd {
                lanes: 4,
                element: TypeId::I32,
            }),
            "i64x4" => self.module.types.register(HirType::Simd {
                lanes: 4,
                element: TypeId::I64,
            }),
            _ => unreachable!(),
        }
    }

    pub(super) fn lower_gpu_method(
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
                    return Err(LowerError::Unsupported("gpu.barrier() takes no arguments".to_string()));
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
                        "gpu.mem_fence() takes no arguments".to_string(),
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
            "atomic_add" | "atomic_sub" | "atomic_min" | "atomic_max" | "atomic_and" | "atomic_or" | "atomic_xor"
            | "atomic_exchange" => self.lower_gpu_atomic_binary(method, args, ctx).map(Some),
            "atomic_compare_exchange" => self.lower_gpu_atomic_cas(args, ctx).map(Some),
            _ => Ok(None),
        }
    }

    pub(super) fn lower_gpu_atomic_binary(
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

    pub(super) fn lower_gpu_atomic_cas(
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
    pub(super) fn lower_simd_static_method(
        &mut self,
        type_name: &str,
        method: &str,
        args: &[ast::Argument],
        ctx: &mut FunctionContext,
    ) -> LowerResult<Option<HirExpr>> {
        let simd_ty = self.register_simd_type(type_name);

        match method {
            "load" => {
                if args.len() != 2 {
                    return Err(LowerError::Unsupported(format!(
                        "{}.load(array, offset) requires exactly 2 arguments",
                        type_name
                    )));
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
                    return Err(LowerError::Unsupported(format!(
                        "{}.gather(array, indices) requires exactly 2 arguments",
                        type_name
                    )));
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
                    return Err(LowerError::Unsupported(format!(
                        "{}.load_masked(array, offset, mask, default) requires exactly 4 arguments",
                        type_name
                    )));
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
    pub(super) fn lower_static_method_call(
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

        // Look up the return type from the module's functions
        let return_ty = self
            .module
            .functions
            .iter()
            .find(|f| f.name == qualified_name)
            .map(|f| f.return_type)
            .unwrap_or_else(|| {
                // If not found as a function, check if class_name is a known type
                // (constructor pattern: ClassName.factory() returns ClassName)
                self.module.types.lookup(class_name).unwrap_or(TypeId::ANY)
            });

        let func_expr = HirExpr {
            kind: HirExprKind::Global(qualified_name),
            ty: TypeId::VOID,
        };

        Ok(HirExpr {
            kind: HirExprKind::Call {
                func: Box::new(func_expr),
                args: args_hir,
            },
            ty: return_ty,
        })
    }

    /// Handle SIMD vector instance methods (sum, product, min, max, etc.)
    pub(super) fn lower_simd_instance_method(
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

    pub(super) fn lower_simd_reduction(
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
            return Err(LowerError::Unsupported(format!("vec.{}() takes no arguments", method)));
        }

        if requires_bool && element != TypeId::BOOL {
            return Err(LowerError::Unsupported(format!(
                "vec.{}() only valid for bool vectors",
                method
            )));
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

    pub(super) fn lower_simd_elementwise(
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
                        "vec.with(idx, val) takes exactly 2 arguments".to_string(),
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
                        "vec.fma(b, c) requires exactly two arguments".to_string(),
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
                        "vec.clamp(lo, hi) requires exactly two arguments".to_string(),
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

    pub(super) fn lower_simd_memory(
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
}

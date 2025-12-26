//! GPU intrinsics and utility methods for MIR lowering
//!
//! This module contains methods for lowering GPU intrinsic calls,
//! extracting GPU-specific arguments, and metadata extraction for AOP matching.

use super::lowering_core::{MirLowerer, MirLowerError, MirLowerResult};
use crate::hir::{GpuIntrinsicKind, HirExpr, HirExprKind, HirFunction, NeighborDirection};
use crate::mir::instructions::{GpuAtomicOp, GpuMemoryScope, MirInst, VReg};

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_gpu_intrinsic(&mut self, intrinsic: GpuIntrinsicKind, args: &[HirExpr]) -> MirLowerResult<VReg> {
        match intrinsic {
            GpuIntrinsicKind::GlobalId => {
                let dim = self.get_gpu_dim_arg(args)?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GpuGlobalId { dest, dim });
                    dest
                })
            }
            GpuIntrinsicKind::LocalId => {
                let dim = self.get_gpu_dim_arg(args)?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GpuLocalId { dest, dim });
                    dest
                })
            }
            GpuIntrinsicKind::GroupId => {
                let dim = self.get_gpu_dim_arg(args)?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GpuGroupId { dest, dim });
                    dest
                })
            }
            GpuIntrinsicKind::GlobalSize => {
                let dim = self.get_gpu_dim_arg(args)?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GpuGlobalSize { dest, dim });
                    dest
                })
            }
            GpuIntrinsicKind::LocalSize => {
                let dim = self.get_gpu_dim_arg(args)?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GpuLocalSize { dest, dim });
                    dest
                })
            }
            GpuIntrinsicKind::NumGroups => {
                let dim = self.get_gpu_dim_arg(args)?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GpuNumGroups { dest, dim });
                    dest
                })
            }
            GpuIntrinsicKind::Barrier => {
                // Barrier doesn't return a meaningful value, use dummy vreg
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GpuBarrier);
                    dest
                })
            }
            GpuIntrinsicKind::MemFence => {
                let scope = self.get_gpu_scope_arg(args)?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GpuMemFence { scope });
                    dest
                })
            }
            GpuIntrinsicKind::SimdIndex => {
                // SIMD linear global index - use GlobalId with dim 0
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GpuGlobalId { dest, dim: 0 });
                    dest
                })
            }
            GpuIntrinsicKind::SimdThreadIndex => {
                // SIMD thread index within group - use LocalId with dim 0
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GpuLocalId { dest, dim: 0 });
                    dest
                })
            }
            GpuIntrinsicKind::SimdGroupIndex => {
                // SIMD group index - use GroupId with dim 0
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GpuGroupId { dest, dim: 0 });
                    dest
                })
            }
            GpuIntrinsicKind::SimdSum => {
                let source = self.lower_expr(&args[0])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecSum { dest, source });
                    dest
                })
            }
            GpuIntrinsicKind::SimdProduct => {
                let source = self.lower_expr(&args[0])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecProduct { dest, source });
                    dest
                })
            }
            GpuIntrinsicKind::SimdMin => {
                let source = self.lower_expr(&args[0])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecMin { dest, source });
                    dest
                })
            }
            GpuIntrinsicKind::SimdMax => {
                let source = self.lower_expr(&args[0])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecMax { dest, source });
                    dest
                })
            }
            GpuIntrinsicKind::SimdAll => {
                let source = self.lower_expr(&args[0])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecAll { dest, source });
                    dest
                })
            }
            GpuIntrinsicKind::SimdAny => {
                let source = self.lower_expr(&args[0])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecAny { dest, source });
                    dest
                })
            }
            GpuIntrinsicKind::SimdExtract => {
                let vector = self.lower_expr(&args[0])?;
                let index = self.lower_expr(&args[1])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block
                        .instructions
                        .push(MirInst::VecExtract { dest, vector, index });
                    dest
                })
            }
            GpuIntrinsicKind::SimdWith => {
                let vector = self.lower_expr(&args[0])?;
                let index = self.lower_expr(&args[1])?;
                let value = self.lower_expr(&args[2])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecWith {
                        dest,
                        vector,
                        index,
                        value,
                    });
                    dest
                })
            }
            GpuIntrinsicKind::SimdSqrt => {
                let source = self.lower_expr(&args[0])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecSqrt { dest, source });
                    dest
                })
            }
            GpuIntrinsicKind::SimdAbs => {
                let source = self.lower_expr(&args[0])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecAbs { dest, source });
                    dest
                })
            }
            GpuIntrinsicKind::SimdFloor => {
                let source = self.lower_expr(&args[0])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecFloor { dest, source });
                    dest
                })
            }
            GpuIntrinsicKind::SimdCeil => {
                let source = self.lower_expr(&args[0])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecCeil { dest, source });
                    dest
                })
            }
            GpuIntrinsicKind::SimdRound => {
                let source = self.lower_expr(&args[0])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecRound { dest, source });
                    dest
                })
            }
            GpuIntrinsicKind::SimdShuffle => {
                // v.shuffle([3, 2, 1, 0]) - reorder lanes by indices
                let source = self.lower_expr(&args[0])?;
                let indices = self.lower_expr(&args[1])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block
                        .instructions
                        .push(MirInst::VecShuffle { dest, source, indices });
                    dest
                })
            }
            GpuIntrinsicKind::SimdBlend => {
                // a.blend(b, [0, 1, 4, 5]) - merge two vectors
                let first = self.lower_expr(&args[0])?;
                let second = self.lower_expr(&args[1])?;
                let indices = self.lower_expr(&args[2])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecBlend {
                        dest,
                        first,
                        second,
                        indices,
                    });
                    dest
                })
            }
            GpuIntrinsicKind::SimdSelect => {
                // mask.select(a, b) - select from a where true, b where false
                let mask = self.lower_expr(&args[0])?;
                let if_true = self.lower_expr(&args[1])?;
                let if_false = self.lower_expr(&args[2])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecSelect {
                        dest,
                        mask,
                        if_true,
                        if_false,
                    });
                    dest
                })
            }
            GpuIntrinsicKind::SimdLoad => {
                // vec.load(array, offset) - load vector from array
                let array = self.lower_expr(&args[0])?;
                let offset = self.lower_expr(&args[1])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecLoad {
                        dest,
                        array,
                        offset,
                    });
                    dest
                })
            }
            GpuIntrinsicKind::SimdStore => {
                // v.store(array, offset) - store vector to array
                let source = self.lower_expr(&args[0])?;
                let array = self.lower_expr(&args[1])?;
                let offset = self.lower_expr(&args[2])?;
                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecStore {
                        source,
                        array,
                        offset,
                    });
                    // VecStore has no return value, return a dummy vreg
                    func.new_vreg()
                })
            }
            GpuIntrinsicKind::SimdGather => {
                // vec.gather(array, indices) - gather from array at indices
                let array = self.lower_expr(&args[0])?;
                let indices = self.lower_expr(&args[1])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecGather {
                        dest,
                        array,
                        indices,
                    });
                    dest
                })
            }
            GpuIntrinsicKind::SimdScatter => {
                // v.scatter(array, indices) - scatter vector to array at indices
                let source = self.lower_expr(&args[0])?;
                let array = self.lower_expr(&args[1])?;
                let indices = self.lower_expr(&args[2])?;
                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecScatter {
                        source,
                        array,
                        indices,
                    });
                    // VecScatter has no return value, return a dummy vreg
                    func.new_vreg()
                })
            }
            GpuIntrinsicKind::SimdFma => {
                // v.fma(b, c) - fused multiply-add: v * b + c
                let a = self.lower_expr(&args[0])?;
                let b = self.lower_expr(&args[1])?;
                let c = self.lower_expr(&args[2])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecFma { dest, a, b, c });
                    dest
                })
            }
            GpuIntrinsicKind::SimdRecip => {
                // v.recip() - reciprocal: 1.0 / v
                let source = self.lower_expr(&args[0])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecRecip { dest, source });
                    dest
                })
            }
            GpuIntrinsicKind::SimdNeighborLeft | GpuIntrinsicKind::SimdNeighborRight => {
                // x.left_neighbor / x.right_neighbor - neighbor access
                let array = self.lower_expr(&args[0])?;
                let direction = match intrinsic {
                    GpuIntrinsicKind::SimdNeighborLeft => NeighborDirection::Left,
                    GpuIntrinsicKind::SimdNeighborRight => NeighborDirection::Right,
                    _ => unreachable!(),
                };
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::NeighborLoad {
                        dest,
                        array,
                        direction,
                    });
                    dest
                })
            }
            GpuIntrinsicKind::SimdMaskedLoad => {
                // f32x4.load_masked(arr, offset, mask, default) -> vec
                let array = self.lower_expr(&args[0])?;
                let offset = self.lower_expr(&args[1])?;
                let mask = self.lower_expr(&args[2])?;
                let default = self.lower_expr(&args[3])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecMaskedLoad {
                        dest,
                        array,
                        offset,
                        mask,
                        default,
                    });
                    dest
                })
            }
            GpuIntrinsicKind::SimdMaskedStore => {
                // v.store_masked(arr, offset, mask) - store only where mask is true
                let source = self.lower_expr(&args[0])?;
                let array = self.lower_expr(&args[1])?;
                let offset = self.lower_expr(&args[2])?;
                let mask = self.lower_expr(&args[3])?;
                self.with_func(|func, current_block| {
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecMaskedStore {
                        source,
                        array,
                        offset,
                        mask,
                    });
                    // Return dummy vreg since store has no result
                    func.new_vreg()
                })
            }
            GpuIntrinsicKind::SimdMinVec => {
                // a.min(b) - element-wise minimum of two vectors
                let a = self.lower_expr(&args[0])?;
                let b = self.lower_expr(&args[1])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecMinVec { dest, a, b });
                    dest
                })
            }
            GpuIntrinsicKind::SimdMaxVec => {
                // a.max(b) - element-wise maximum of two vectors
                let a = self.lower_expr(&args[0])?;
                let b = self.lower_expr(&args[1])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecMaxVec { dest, a, b });
                    dest
                })
            }
            GpuIntrinsicKind::SimdClamp => {
                // v.clamp(lo, hi) - element-wise clamp to range
                let source = self.lower_expr(&args[0])?;
                let lo = self.lower_expr(&args[1])?;
                let hi = self.lower_expr(&args[2])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecClamp { dest, source, lo, hi });
                    dest
                })
            }
            GpuIntrinsicKind::GpuAtomicAdd
            | GpuIntrinsicKind::GpuAtomicSub
            | GpuIntrinsicKind::GpuAtomicMin
            | GpuIntrinsicKind::GpuAtomicMax
            | GpuIntrinsicKind::GpuAtomicAnd
            | GpuIntrinsicKind::GpuAtomicOr
            | GpuIntrinsicKind::GpuAtomicXor
            | GpuIntrinsicKind::GpuAtomicExchange => {
                // gpu.atomic_*(ptr, val) -> old value
                let ptr = self.lower_expr(&args[0])?;
                let value = self.lower_expr(&args[1])?;
                let op = match intrinsic {
                    GpuIntrinsicKind::GpuAtomicAdd => GpuAtomicOp::Add,
                    GpuIntrinsicKind::GpuAtomicSub => GpuAtomicOp::Sub,
                    GpuIntrinsicKind::GpuAtomicMin => GpuAtomicOp::Min,
                    GpuIntrinsicKind::GpuAtomicMax => GpuAtomicOp::Max,
                    GpuIntrinsicKind::GpuAtomicAnd => GpuAtomicOp::And,
                    GpuIntrinsicKind::GpuAtomicOr => GpuAtomicOp::Or,
                    GpuIntrinsicKind::GpuAtomicXor => GpuAtomicOp::Xor,
                    GpuIntrinsicKind::GpuAtomicExchange => GpuAtomicOp::Xchg,
                    _ => unreachable!(),
                };
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GpuAtomic {
                        dest,
                        op,
                        ptr,
                        value,
                    });
                    dest
                })
            }
            GpuIntrinsicKind::GpuAtomicCompareExchange => {
                // gpu.atomic_compare_exchange(ptr, expected, desired) -> old value
                let ptr = self.lower_expr(&args[0])?;
                let expected = self.lower_expr(&args[1])?;
                let desired = self.lower_expr(&args[2])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GpuAtomicCmpXchg {
                        dest,
                        ptr,
                        expected,
                        desired,
                    });
                    dest
                })
            }
        }
    }

    /// Extract dimension argument (0, 1, or 2) from GPU intrinsic args
    pub(super) fn get_gpu_dim_arg(&self, args: &[HirExpr]) -> MirLowerResult<u8> {
        if args.is_empty() {
            return Ok(0); // Default to dimension 0 (x)
        }
        match &args[0].kind {
            HirExprKind::Integer(n) => {
                if *n >= 0 && *n <= 2 {
                    Ok(*n as u8)
                } else {
                    Err(MirLowerError::Unsupported("GPU dimension must be 0, 1, or 2".to_string()))
                }
            }
            _ => Err(MirLowerError::Unsupported("GPU dimension must be a constant integer".to_string())),
        }
    }

    /// Extract memory scope argument from GPU intrinsic args
    pub(super) fn get_gpu_scope_arg(&self, args: &[HirExpr]) -> MirLowerResult<GpuMemoryScope> {
        if args.is_empty() {
            return Ok(GpuMemoryScope::All); // Default to all memory
        }
        match &args[0].kind {
            HirExprKind::Integer(n) => {
                match *n {
                    0 => Ok(GpuMemoryScope::WorkGroup),
                    1 => Ok(GpuMemoryScope::Device),
                    _ => Ok(GpuMemoryScope::All),
                }
            }
            _ => Ok(GpuMemoryScope::All),
        }
    }

    /// Lower an lvalue expression to get its address
    pub(super) fn lower_lvalue(&mut self, expr: &HirExpr) -> MirLowerResult<VReg> {
        match &expr.kind {
            HirExprKind::Local(idx) => {
                let idx = *idx;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::LocalAddr {
                        dest,
                        local_index: idx,
                    });
                    dest
                })
            }
            _ => Err(MirLowerError::Unsupported("complex lvalue".to_string())),
        }
    }

    /// Get the current module path (e.g., "app.domain.user").
    /// This is extracted from the current file path or module name.
    pub(super) fn current_module_path(&self) -> String {
        // For now, return empty string. In the future, extract from self.current_file
        // or pass through from HIR module metadata.
        self.current_file
            .as_ref()
            .and_then(|path| {
                // Convert file path like "app/domain/user.spl" to "app.domain.user"
                if let Some(stem) = std::path::Path::new(path)
                    .file_stem()
                    .and_then(|s| s.to_str())
                {
                    Some(
                        path.trim_end_matches(".spl")
                            .replace('/', ".")
                            .replace('\\', "."),
                    )
                } else {
                    None
                }
            })
            .unwrap_or_default()
    }

    /// Extract function attributes for AOP matching.
    /// Includes attributes like "inject", "test", "pure", etc.
    pub(super) fn extract_function_attributes(&self, func: &HirFunction) -> Vec<String> {
        let mut attrs = func.attributes.clone();

        // Add derived attributes from function flags (if not already present)
        if func.inject && !attrs.contains(&"inject".to_string()) {
            attrs.push("inject".to_string());
        }

        if func.is_pure && !attrs.contains(&"pure".to_string()) {
            attrs.push("pure".to_string());
        }

        // Add concurrency mode as attribute
        let mode_attr = match func.concurrency_mode {
            crate::hir::ConcurrencyMode::LockBase => "lock_base",
            crate::hir::ConcurrencyMode::Unsafe => "unsafe",
            crate::hir::ConcurrencyMode::Actor => "actor", // default mode
        };
        if !mode_attr.is_empty() && !attrs.contains(&mode_attr.to_string()) {
            attrs.push(mode_attr.to_string());
        }

        attrs
    }

    /// Extract function effects for AOP matching.
    /// Includes effects like "io", "async", "net", etc.
    pub(super) fn extract_function_effects(&self, func: &HirFunction) -> Vec<String> {
        let mut effects = func.effects.clone();

        // Add inferred effects from concurrency mode (if not already present)
        match func.concurrency_mode {
            crate::hir::ConcurrencyMode::Actor => {
                if !effects.contains(&"async".to_string()) {
                    effects.push("async".to_string());
                }
            }
            _ => {}
        }

        effects
    }
}

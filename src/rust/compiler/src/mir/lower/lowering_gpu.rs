//! GPU intrinsics and utility methods for MIR lowering
//!
//! This module contains methods for lowering GPU intrinsic calls,
//! extracting GPU-specific arguments, and metadata extraction for AOP matching.

use super::lowering_core::{MirLowerError, MirLowerResult, MirLowerer};
use crate::hir::{GpuIntrinsicKind, HirExpr, HirExprKind, HirFunction, NeighborDirection};
use crate::mir::instructions::{GpuAtomicOp, GpuMemoryScope, MirInst, VReg};

/// Helper macro for GPU intrinsics with dimension argument
macro_rules! gpu_dim_op {
    ($self:expr, $args:expr, $inst:ident) => {{
        let dim = $self.get_gpu_dim_arg($args)?;
        $self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::$inst { dest, dim });
            dest
        })
    }};
}

/// Helper macro for SIMD unary operations (single source argument)
macro_rules! simd_unary_op {
    ($self:expr, $args:expr, $inst:ident) => {{
        let source = $self.lower_expr(&$args[0])?;
        $self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::$inst { dest, source });
            dest
        })
    }};
}

/// Helper macro for SIMD binary operations (two vector arguments)
macro_rules! simd_binary_op {
    ($self:expr, $args:expr, $inst:ident) => {{
        let a = $self.lower_expr(&$args[0])?;
        let b = $self.lower_expr(&$args[1])?;
        $self.with_func(|func, current_block| {
            let dest = func.new_vreg();
            let block = func.block_mut(current_block).unwrap();
            block.instructions.push(MirInst::$inst { dest, a, b });
            dest
        })
    }};
}

impl<'a> MirLowerer<'a> {
    pub(super) fn lower_gpu_intrinsic(
        &mut self,
        intrinsic: GpuIntrinsicKind,
        args: &[HirExpr],
    ) -> MirLowerResult<VReg> {
        match intrinsic {
            GpuIntrinsicKind::GlobalId => gpu_dim_op!(self, args, GpuGlobalId),
            GpuIntrinsicKind::LocalId => gpu_dim_op!(self, args, GpuLocalId),
            GpuIntrinsicKind::GroupId => gpu_dim_op!(self, args, GpuGroupId),
            GpuIntrinsicKind::GlobalSize => gpu_dim_op!(self, args, GpuGlobalSize),
            GpuIntrinsicKind::LocalSize => gpu_dim_op!(self, args, GpuLocalSize),
            GpuIntrinsicKind::NumGroups => gpu_dim_op!(self, args, GpuNumGroups),
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
            GpuIntrinsicKind::SimdSum => simd_unary_op!(self, args, VecSum),
            GpuIntrinsicKind::SimdProduct => simd_unary_op!(self, args, VecProduct),
            GpuIntrinsicKind::SimdMin => simd_unary_op!(self, args, VecMin),
            GpuIntrinsicKind::SimdMax => simd_unary_op!(self, args, VecMax),
            GpuIntrinsicKind::SimdAll => simd_unary_op!(self, args, VecAll),
            GpuIntrinsicKind::SimdAny => simd_unary_op!(self, args, VecAny),
            GpuIntrinsicKind::SimdExtract => {
                let vector = self.lower_expr(&args[0])?;
                let index = self.lower_expr(&args[1])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecExtract { dest, vector, index });
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
            GpuIntrinsicKind::SimdSqrt => simd_unary_op!(self, args, VecSqrt),
            GpuIntrinsicKind::SimdAbs => simd_unary_op!(self, args, VecAbs),
            GpuIntrinsicKind::SimdFloor => simd_unary_op!(self, args, VecFloor),
            GpuIntrinsicKind::SimdCeil => simd_unary_op!(self, args, VecCeil),
            GpuIntrinsicKind::SimdRound => simd_unary_op!(self, args, VecRound),
            GpuIntrinsicKind::SimdShuffle => {
                // v.shuffle([3, 2, 1, 0]) - reorder lanes by indices
                let source = self.lower_expr(&args[0])?;
                let indices = self.lower_expr(&args[1])?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::VecShuffle { dest, source, indices });
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
                    block.instructions.push(MirInst::VecLoad { dest, array, offset });
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
                    block.instructions.push(MirInst::VecStore { source, array, offset });
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
                    block.instructions.push(MirInst::VecGather { dest, array, indices });
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
                    block.instructions.push(MirInst::VecScatter { source, array, indices });
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
            GpuIntrinsicKind::SimdRecip => simd_unary_op!(self, args, VecRecip),
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
                    block
                        .instructions
                        .push(MirInst::NeighborLoad { dest, array, direction });
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
            GpuIntrinsicKind::SimdMinVec => simd_binary_op!(self, args, VecMinVec),
            GpuIntrinsicKind::SimdMaxVec => simd_binary_op!(self, args, VecMaxVec),
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
                    block.instructions.push(MirInst::GpuAtomic { dest, op, ptr, value });
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
                    Err(MirLowerError::Unsupported(
                        "GPU dimension must be 0, 1, or 2".to_string(),
                    ))
                }
            }
            _ => Err(MirLowerError::Unsupported(
                "GPU dimension must be a constant integer".to_string(),
            )),
        }
    }

    /// Extract memory scope argument from GPU intrinsic args
    pub(super) fn get_gpu_scope_arg(&self, args: &[HirExpr]) -> MirLowerResult<GpuMemoryScope> {
        if args.is_empty() {
            return Ok(GpuMemoryScope::All); // Default to all memory
        }
        match &args[0].kind {
            HirExprKind::Integer(n) => match *n {
                0 => Ok(GpuMemoryScope::WorkGroup),
                1 => Ok(GpuMemoryScope::Device),
                _ => Ok(GpuMemoryScope::All),
            },
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
                    block.instructions.push(MirInst::LocalAddr { dest, local_index: idx });
                    dest
                })
            }
            HirExprKind::FieldAccess { receiver, field_index } => {
                // Get the base address, then add field offset using GetElementPtr
                let base_addr = self.lower_lvalue(receiver)?;
                let field_idx = *field_index;
                self.with_func(|func, current_block| {
                    // Create a constant for the field index
                    let index_reg = func.new_vreg();
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::ConstInt {
                        dest: index_reg,
                        value: field_idx as i64,
                    });
                    block.instructions.push(MirInst::GetElementPtr {
                        dest,
                        base: base_addr,
                        index: index_reg,
                    });
                    dest
                })
            }
            HirExprKind::Index { receiver, index } => {
                // Get the array base address, then compute element address
                let base_addr = self.lower_expr(receiver)?;
                let index_val = self.lower_expr(index)?;
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    block.instructions.push(MirInst::GetElementPtr {
                        dest,
                        base: base_addr,
                        index: index_val,
                    });
                    dest
                })
            }
            HirExprKind::Global(name) => {
                // Global variable - treat as a dynamic lookup via Call
                let name = name.clone();
                self.with_func(|func, current_block| {
                    let dest = func.new_vreg();
                    let block = func.block_mut(current_block).unwrap();
                    // Use a builtin call to get global address
                    block.instructions.push(MirInst::Call {
                        dest: Some(dest),
                        target: crate::mir::CallTarget::Io(format!("__get_global_{}", name)),
                        args: vec![],
                    });
                    dest
                })
            }
            HirExprKind::MethodCall {
                receiver, method, args, ..
            } if args.is_empty() => {
                // Property access (no-paren method call) used as lvalue
                // This happens when field access falls back to method call
                // Convert back to field access by looking up the field index
                let receiver_ty = receiver.ty;

                // Try to find the field index in the receiver's type
                if let Some(type_registry) = self.type_registry {
                    if let Some(hir_type) = type_registry.get(receiver_ty) {
                        // Check both Struct and Class (classes are also structs at MIR level)
                        let fields = match hir_type {
                            crate::hir::HirType::Struct { fields, .. } => Some(fields),
                            _ => None,
                        };

                        if let Some(fields) = fields {
                            // Find the field by name
                            if let Some((field_idx, _)) =
                                fields.iter().enumerate().find(|(_, (name, _))| name == method)
                            {
                                // Found the field - use GetElementPtr
                                let base_addr = self.lower_lvalue(receiver)?;
                                return self.with_func(|func, current_block| {
                                    let index_reg = func.new_vreg();
                                    let dest = func.new_vreg();
                                    let block = func.block_mut(current_block).unwrap();
                                    block.instructions.push(MirInst::ConstInt {
                                        dest: index_reg,
                                        value: field_idx as i64,
                                    });
                                    block.instructions.push(MirInst::GetElementPtr {
                                        dest,
                                        base: base_addr,
                                        index: index_reg,
                                    });
                                    dest
                                });
                            }
                        }
                    }
                }

                // Couldn't find field statically - use runtime field setter
                // This happens when type information is lost (TypeId(0) or Any)
                eprintln!("[DEBUG lower_lvalue] MethodCall property setter: receiver type {:?}, method {} - using runtime setter", receiver.ty, method);

                // For runtime field access, we need to return something that can be stored to
                // The assignment will need to use a runtime call like rt_field_set(receiver, "field_name", value)
                // For now, we'll treat this as getting the address of a temporary that will trigger
                // a runtime field set operation in the Store instruction handler

                // Return the receiver register as a placeholder
                // The Store handler will need to detect this and emit a runtime field_set call
                let receiver_val = self.lower_expr(receiver)?;
                Ok(receiver_val)
            }
            _ => {
                eprintln!("[DEBUG lower_lvalue] Unsupported lvalue kind: {:?}", expr.kind);
                Err(MirLowerError::Unsupported(format!("complex lvalue: {:?}", expr.kind)))
            }
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
                if let Some(stem) = std::path::Path::new(path).file_stem().and_then(|s| s.to_str()) {
                    Some(path.trim_end_matches(".spl").replace('/', ".").replace('\\', "."))
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

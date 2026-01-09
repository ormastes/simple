// SPIR-V instruction lowering
//
// This module handles lowering MIR instructions to SPIR-V operations.
// Part of spirv_builder.rs, extracted for maintainability.

use crate::error::CompileError;
use crate::hir::{BinOp, TypeId};
use crate::mir::{GpuAtomicOp, MirInst};
use rspirv::spirv::{Decoration, StorageClass};

impl super::SpirvModule {
    /// Lower a single MIR instruction to SPIR-V
    ///
    /// This is the core translation logic that maps MIR instructions to SPIR-V operations.
    pub(super) fn lower_instruction(&mut self, inst: &MirInst) -> Result<(), CompileError> {
        match inst {
            // Constants
            MirInst::ConstInt { dest, value } => {
                // Determine type based on value range
                // For now, use i32 for small values, i64 for larger
                let (type_id, const_id) = if *value >= i32::MIN as i64 && *value <= i32::MAX as i64
                {
                    let i32_type = self.get_i32_type();
                    (
                        TypeId::I32,
                        self.builder.constant_bit32(i32_type, *value as u32),
                    )
                } else {
                    let i64_type = self.get_i64_type();
                    (
                        TypeId::I64,
                        self.builder.constant_bit64(i64_type, *value as u64),
                    )
                };
                self.vreg_id_map.insert(*dest, const_id);
                self.vreg_types.insert(*dest, type_id);
            }

            MirInst::ConstFloat { dest, value } => {
                // Use f32 by default
                let f32_type = self.get_f32_type();
                let const_id = self
                    .builder
                    .constant_bit32(f32_type, (*value as f32).to_bits());
                self.vreg_id_map.insert(*dest, const_id);
                self.vreg_types.insert(*dest, TypeId::F32);
            }

            MirInst::ConstBool { dest, value } => {
                let bool_type = self.get_bool_type();
                let const_id = if *value {
                    self.builder.constant_true(bool_type)
                } else {
                    self.builder.constant_false(bool_type)
                };
                self.vreg_id_map.insert(*dest, const_id);
                self.vreg_types.insert(*dest, TypeId::BOOL);
            }

            MirInst::Copy { dest, src } => {
                let src_id = *self.vreg_id_map.get(src).ok_or_else(|| {
                    CompileError::Codegen(format!("Undefined register: {:?}", src))
                })?;
                self.vreg_id_map.insert(*dest, src_id);

                // Propagate type
                if let Some(&src_type) = self.vreg_types.get(src) {
                    self.vreg_types.insert(*dest, src_type);
                }
            }

            // Binary operations
            MirInst::BinOp {
                dest,
                op,
                left,
                right,
            } => {
                self.lower_binop(*dest, *op, *left, *right)?;
            }

            // GPU built-ins
            MirInst::GpuGlobalId { dest, dim } => {
                self.lower_gpu_global_id(*dest, *dim)?;
            }

            MirInst::GpuBarrier => {
                self.lower_gpu_barrier()?;
            }

            MirInst::GpuAtomic {
                dest,
                op,
                ptr,
                value,
            } => {
                self.lower_gpu_atomic(*dest, *op, *ptr, *value)?;
            }

            MirInst::GpuLocalId { dest, dim } => {
                self.lower_gpu_local_id(*dest, *dim)?;
            }

            MirInst::GpuGroupId { dest, dim } => {
                self.lower_gpu_group_id(*dest, *dim)?;
            }

            // Memory operations
            MirInst::Load { dest, addr, ty } => {
                let addr_id = *self.vreg_id_map.get(addr).ok_or_else(|| {
                    CompileError::Codegen(format!("Undefined address register: {:?}", addr))
                })?;

                // Use TypeId to determine result type
                let result_type = self.type_id_to_spirv(*ty)?;

                let loaded = self
                    .builder
                    .load(result_type, None, addr_id, None, vec![])
                    .map_err(|e| {
                        CompileError::Codegen(format!("Failed to load from memory: {}", e))
                    })?;

                self.vreg_id_map.insert(*dest, loaded);
                self.vreg_types.insert(*dest, *ty);
            }

            MirInst::Store { addr, value, ty } => {
                let addr_id = *self.vreg_id_map.get(addr).ok_or_else(|| {
                    CompileError::Codegen(format!("Undefined address register: {:?}", addr))
                })?;
                let value_id = *self.vreg_id_map.get(value).ok_or_else(|| {
                    CompileError::Codegen(format!("Undefined value register: {:?}", value))
                })?;

                // Type is used to ensure proper storage (though SPIR-V doesn't explicitly need it for OpStore)
                let _ = self.type_id_to_spirv(*ty)?; // Validate type exists

                self.builder
                    .store(addr_id, value_id, None, vec![])
                    .map_err(|e| {
                        CompileError::Codegen(format!("Failed to store to memory: {}", e))
                    })?;

                // Store has no destination register
            }

            // Buffer/Array access
            MirInst::LocalAddr { dest, local_index } => {
                // Get pointer to a local variable or parameter
                // For parameters, we return the global variable ID directly
                if let Some(&var_id) = self.param_var_map.get(local_index) {
                    self.vreg_id_map.insert(*dest, var_id);
                    // Track that this VReg holds a parameter reference
                    self.vreg_param_map.insert(*dest, *local_index);
                } else {
                    // TODO: [codegen][P1] Handle local variables (would need to track OpVariable for locals)
                    return Err(CompileError::Codegen(format!(
                        "LocalAddr for non-parameter local {} not yet implemented",
                        local_index
                    )));
                }
            }

            MirInst::GetElementPtr { dest, base, index } => {
                self.lower_get_element_ptr(*dest, *base, *index)?;
            }

            _ => {
                // Other instructions not yet implemented
                return Err(CompileError::Codegen(format!(
                    "SPIR-V lowering not implemented for instruction: {:?}",
                    inst
                )));
            }
        }

        Ok(())
    }

    /// Lower binary operation to SPIR-V
    fn lower_binop(
        &mut self,
        dest: crate::mir::VReg,
        op: BinOp,
        left: crate::mir::VReg,
        right: crate::mir::VReg,
    ) -> Result<(), CompileError> {
        let left_id = *self
            .vreg_id_map
            .get(&left)
            .ok_or_else(|| CompileError::Codegen(format!("Undefined register: {:?}", left)))?;
        let right_id = *self
            .vreg_id_map
            .get(&right)
            .ok_or_else(|| CompileError::Codegen(format!("Undefined register: {:?}", right)))?;

        // Get operand type (default to i32 if not tracked)
        let left_type = self.vreg_types.get(&left).copied().unwrap_or(TypeId::I32);

        // Select SPIR-V type and operation based on operand type
        let (result_type_id, _result_spirv_type, result) = match (op, left_type) {
            // Arithmetic operations
            (BinOp::Add, TypeId::I32 | TypeId::I64) => {
                let ty = self.type_id_to_spirv(left_type)?;
                (
                    left_type,
                    ty,
                    self.builder.i_add(ty, None, left_id, right_id)?,
                )
            }
            (BinOp::Add, TypeId::U32 | TypeId::U64) => {
                let ty = self.type_id_to_spirv(left_type)?;
                (
                    left_type,
                    ty,
                    self.builder.i_add(ty, None, left_id, right_id)?,
                )
            }
            (BinOp::Add, TypeId::F32 | TypeId::F64) => {
                let ty = self.type_id_to_spirv(left_type)?;
                (
                    left_type,
                    ty,
                    self.builder.f_add(ty, None, left_id, right_id)?,
                )
            }

            (BinOp::Sub, TypeId::I32 | TypeId::I64 | TypeId::U32 | TypeId::U64) => {
                let ty = self.type_id_to_spirv(left_type)?;
                (
                    left_type,
                    ty,
                    self.builder.i_sub(ty, None, left_id, right_id)?,
                )
            }
            (BinOp::Sub, TypeId::F32 | TypeId::F64) => {
                let ty = self.type_id_to_spirv(left_type)?;
                (
                    left_type,
                    ty,
                    self.builder.f_sub(ty, None, left_id, right_id)?,
                )
            }

            (BinOp::Mul, TypeId::I32 | TypeId::I64 | TypeId::U32 | TypeId::U64) => {
                let ty = self.type_id_to_spirv(left_type)?;
                (
                    left_type,
                    ty,
                    self.builder.i_mul(ty, None, left_id, right_id)?,
                )
            }
            (BinOp::Mul, TypeId::F32 | TypeId::F64) => {
                let ty = self.type_id_to_spirv(left_type)?;
                (
                    left_type,
                    ty,
                    self.builder.f_mul(ty, None, left_id, right_id)?,
                )
            }

            (BinOp::Div, TypeId::I32 | TypeId::I64) => {
                let ty = self.type_id_to_spirv(left_type)?;
                (
                    left_type,
                    ty,
                    self.builder.s_div(ty, None, left_id, right_id)?,
                )
            }
            (BinOp::Div, TypeId::U32 | TypeId::U64) => {
                let ty = self.type_id_to_spirv(left_type)?;
                (
                    left_type,
                    ty,
                    self.builder.u_div(ty, None, left_id, right_id)?,
                )
            }
            (BinOp::Div, TypeId::F32 | TypeId::F64) => {
                let ty = self.type_id_to_spirv(left_type)?;
                (
                    left_type,
                    ty,
                    self.builder.f_div(ty, None, left_id, right_id)?,
                )
            }

            (BinOp::Mod, TypeId::I32 | TypeId::I64) => {
                let ty = self.type_id_to_spirv(left_type)?;
                (
                    left_type,
                    ty,
                    self.builder.s_mod(ty, None, left_id, right_id)?,
                )
            }
            (BinOp::Mod, TypeId::U32 | TypeId::U64) => {
                let ty = self.type_id_to_spirv(left_type)?;
                (
                    left_type,
                    ty,
                    self.builder.u_mod(ty, None, left_id, right_id)?,
                )
            }
            (BinOp::Mod, TypeId::F32 | TypeId::F64) => {
                let ty = self.type_id_to_spirv(left_type)?;
                (
                    left_type,
                    ty,
                    self.builder.f_mod(ty, None, left_id, right_id)?,
                )
            }

            // Comparison operations (return bool)
            (BinOp::Lt, TypeId::I32 | TypeId::I64) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .s_less_than(bool_type, None, left_id, right_id)?,
                )
            }
            (BinOp::Lt, TypeId::U32 | TypeId::U64) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .u_less_than(bool_type, None, left_id, right_id)?,
                )
            }
            (BinOp::Lt, TypeId::F32 | TypeId::F64) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .f_ord_less_than(bool_type, None, left_id, right_id)?,
                )
            }

            (BinOp::LtEq, TypeId::I32 | TypeId::I64) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .s_less_than_equal(bool_type, None, left_id, right_id)?,
                )
            }
            (BinOp::LtEq, TypeId::U32 | TypeId::U64) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .u_less_than_equal(bool_type, None, left_id, right_id)?,
                )
            }
            (BinOp::LtEq, TypeId::F32 | TypeId::F64) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .f_ord_less_than_equal(bool_type, None, left_id, right_id)?,
                )
            }

            (BinOp::Gt, TypeId::I32 | TypeId::I64) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .s_greater_than(bool_type, None, left_id, right_id)?,
                )
            }
            (BinOp::Gt, TypeId::U32 | TypeId::U64) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .u_greater_than(bool_type, None, left_id, right_id)?,
                )
            }
            (BinOp::Gt, TypeId::F32 | TypeId::F64) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .f_ord_greater_than(bool_type, None, left_id, right_id)?,
                )
            }

            (BinOp::GtEq, TypeId::I32 | TypeId::I64) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .s_greater_than_equal(bool_type, None, left_id, right_id)?,
                )
            }
            (BinOp::GtEq, TypeId::U32 | TypeId::U64) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .u_greater_than_equal(bool_type, None, left_id, right_id)?,
                )
            }
            (BinOp::GtEq, TypeId::F32 | TypeId::F64) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .f_ord_greater_than_equal(bool_type, None, left_id, right_id)?,
                )
            }

            (BinOp::Eq, TypeId::F32 | TypeId::F64) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .f_ord_equal(bool_type, None, left_id, right_id)?,
                )
            }
            (BinOp::Eq, _) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder.i_equal(bool_type, None, left_id, right_id)?,
                )
            }

            (BinOp::NotEq, TypeId::F32 | TypeId::F64) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .f_ord_not_equal(bool_type, None, left_id, right_id)?,
                )
            }
            (BinOp::NotEq, _) => {
                let bool_type = self.get_bool_type();
                (
                    TypeId::BOOL,
                    bool_type,
                    self.builder
                        .i_not_equal(bool_type, None, left_id, right_id)?,
                )
            }

            // Bitwise operations (integer only)
            (BinOp::BitAnd, ty @ (TypeId::I32 | TypeId::I64 | TypeId::U32 | TypeId::U64)) => {
                let spirv_ty = self.type_id_to_spirv(ty)?;
                (
                    ty,
                    spirv_ty,
                    self.builder
                        .bitwise_and(spirv_ty, None, left_id, right_id)?,
                )
            }
            (BinOp::BitOr, ty @ (TypeId::I32 | TypeId::I64 | TypeId::U32 | TypeId::U64)) => {
                let spirv_ty = self.type_id_to_spirv(ty)?;
                (
                    ty,
                    spirv_ty,
                    self.builder.bitwise_or(spirv_ty, None, left_id, right_id)?,
                )
            }
            (BinOp::BitXor, ty @ (TypeId::I32 | TypeId::I64 | TypeId::U32 | TypeId::U64)) => {
                let spirv_ty = self.type_id_to_spirv(ty)?;
                (
                    ty,
                    spirv_ty,
                    self.builder
                        .bitwise_xor(spirv_ty, None, left_id, right_id)?,
                )
            }

            _ => {
                return Err(CompileError::Codegen(format!(
                    "Unsupported binary op {:?} for type {:?}",
                    op, left_type
                )))
            }
        };

        self.vreg_id_map.insert(dest, result);
        self.vreg_types.insert(dest, result_type_id);
        Ok(())
    }

    /// Lower GPU global ID instruction
    fn lower_gpu_global_id(&mut self, dest: crate::mir::VReg, dim: u8) -> Result<(), CompileError> {
        // gl_GlobalInvocationID is a built-in vec3<u32>
        let u32_type = self.get_u32_type();
        let vec3_u32_type = self.get_vec3_u32_type();
        let ptr_type = self.get_ptr_input_vec3_u32_type();

        // Create variable for gl_GlobalInvocationID
        let global_id_var = self
            .builder
            .variable(ptr_type, None, StorageClass::Input, None);

        // Decorate it as GlobalInvocationId built-in
        self.builder.decorate(
            global_id_var,
            Decoration::BuiltIn,
            vec![rspirv::dr::Operand::BuiltIn(
                rspirv::spirv::BuiltIn::GlobalInvocationId,
            )],
        );

        // Load the vec3
        let loaded = self
            .builder
            .load(vec3_u32_type, None, global_id_var, None, vec![])
            .map_err(|e| {
                CompileError::Codegen(format!("Failed to load GlobalInvocationId: {}", e))
            })?;

        // Extract component
        let component = self
            .builder
            .composite_extract(u32_type, None, loaded, vec![dim as u32])
            .map_err(|e| CompileError::Codegen(format!("Failed to extract component: {}", e)))?;

        self.vreg_id_map.insert(dest, component);
        self.vreg_types.insert(dest, TypeId::U32);
        Ok(())
    }

    /// Lower GPU barrier instruction
    fn lower_gpu_barrier(&mut self) -> Result<(), CompileError> {
        let u32_type = self.get_u32_type();

        // Scope::Workgroup = 2
        let scope_workgroup = self.builder.constant_bit32(u32_type, 2);

        // MemorySemantics: AcquireRelease (0x8) | WorkgroupMemory (0x100) = 0x108
        let semantics = self.builder.constant_bit32(u32_type, 0x108);

        self.builder
            .control_barrier(scope_workgroup, scope_workgroup, semantics)
            .map_err(|e| CompileError::Codegen(format!("Failed to emit barrier: {}", e)))?;
        Ok(())
    }

    /// Lower GPU atomic operation
    fn lower_gpu_atomic(
        &mut self,
        dest: crate::mir::VReg,
        op: GpuAtomicOp,
        ptr: crate::mir::VReg,
        value: crate::mir::VReg,
    ) -> Result<(), CompileError> {
        let ptr_id = *self
            .vreg_id_map
            .get(&ptr)
            .ok_or_else(|| CompileError::Codegen(format!("Undefined register: {:?}", ptr)))?;
        let value_id = *self
            .vreg_id_map
            .get(&value)
            .ok_or_else(|| CompileError::Codegen(format!("Undefined register: {:?}", value)))?;

        let u32_type = self.get_u32_type();

        // Scope: Workgroup (2)
        let scope = self.builder.constant_bit32(u32_type, 2);

        // Semantics: Relaxed (0)
        let semantics = self.builder.constant_bit32(u32_type, 0);

        let result = match op {
            GpuAtomicOp::Add => self
                .builder
                .atomic_i_add(u32_type, None, ptr_id, scope, semantics, value_id),
            GpuAtomicOp::Sub => self
                .builder
                .atomic_i_sub(u32_type, None, ptr_id, scope, semantics, value_id),
            GpuAtomicOp::Min => self
                .builder
                .atomic_u_min(u32_type, None, ptr_id, scope, semantics, value_id),
            GpuAtomicOp::Max => self
                .builder
                .atomic_u_max(u32_type, None, ptr_id, scope, semantics, value_id),
            GpuAtomicOp::And => self
                .builder
                .atomic_and(u32_type, None, ptr_id, scope, semantics, value_id),
            GpuAtomicOp::Or => self
                .builder
                .atomic_or(u32_type, None, ptr_id, scope, semantics, value_id),
            GpuAtomicOp::Xor => self
                .builder
                .atomic_xor(u32_type, None, ptr_id, scope, semantics, value_id),
            GpuAtomicOp::Xchg => self
                .builder
                .atomic_exchange(u32_type, None, ptr_id, scope, semantics, value_id),
        }
        .map_err(|e| CompileError::Codegen(format!("Failed to emit atomic: {}", e)))?;

        self.vreg_id_map.insert(dest, result);
        Ok(())
    }

    /// Lower GPU local ID instruction
    fn lower_gpu_local_id(&mut self, dest: crate::mir::VReg, dim: u8) -> Result<(), CompileError> {
        let u32_type = self.get_u32_type();
        let vec3_u32_type = self.get_vec3_u32_type();
        let ptr_type = self.get_ptr_input_vec3_u32_type();

        let local_id_var = self
            .builder
            .variable(ptr_type, None, StorageClass::Input, None);
        self.builder.decorate(
            local_id_var,
            Decoration::BuiltIn,
            vec![rspirv::dr::Operand::BuiltIn(
                rspirv::spirv::BuiltIn::LocalInvocationId,
            )],
        );

        let loaded = self
            .builder
            .load(vec3_u32_type, None, local_id_var, None, vec![])
            .map_err(|e| {
                CompileError::Codegen(format!("Failed to load LocalInvocationId: {}", e))
            })?;

        let component = self
            .builder
            .composite_extract(u32_type, None, loaded, vec![dim as u32])
            .map_err(|e| CompileError::Codegen(format!("Failed to extract component: {}", e)))?;

        self.vreg_id_map.insert(dest, component);
        self.vreg_types.insert(dest, TypeId::U32);
        Ok(())
    }

    /// Lower GPU group ID instruction
    fn lower_gpu_group_id(&mut self, dest: crate::mir::VReg, dim: u8) -> Result<(), CompileError> {
        let u32_type = self.get_u32_type();
        let vec3_u32_type = self.get_vec3_u32_type();
        let ptr_type = self.get_ptr_input_vec3_u32_type();

        let group_id_var = self
            .builder
            .variable(ptr_type, None, StorageClass::Input, None);
        self.builder.decorate(
            group_id_var,
            Decoration::BuiltIn,
            vec![rspirv::dr::Operand::BuiltIn(
                rspirv::spirv::BuiltIn::WorkgroupId,
            )],
        );

        let loaded = self
            .builder
            .load(vec3_u32_type, None, group_id_var, None, vec![])
            .map_err(|e| CompileError::Codegen(format!("Failed to load WorkgroupId: {}", e)))?;

        let component = self
            .builder
            .composite_extract(u32_type, None, loaded, vec![dim as u32])
            .map_err(|e| CompileError::Codegen(format!("Failed to extract component: {}", e)))?;

        self.vreg_id_map.insert(dest, component);
        self.vreg_types.insert(dest, TypeId::U32);
        Ok(())
    }

    /// Lower GetElementPtr instruction
    fn lower_get_element_ptr(
        &mut self,
        dest: crate::mir::VReg,
        base: crate::mir::VReg,
        index: crate::mir::VReg,
    ) -> Result<(), CompileError> {
        let base_id = *self
            .vreg_id_map
            .get(&base)
            .ok_or_else(|| CompileError::Codegen(format!("Undefined base register: {:?}", base)))?;
        let index_id = *self.vreg_id_map.get(&index).ok_or_else(|| {
            CompileError::Codegen(format!("Undefined index register: {:?}", index))
        })?;

        // Determine element type from the base parameter
        let element_type = if let Some(&param_idx) = self.vreg_param_map.get(&base) {
            // Base is a parameter, get its element type
            let ty = *self.param_elem_type_map.get(&param_idx).ok_or_else(|| {
                CompileError::Codegen(format!("Parameter {} element type not found", param_idx))
            })?;
            self.type_id_to_spirv(ty)?
        } else {
            // Not a parameter, default to i32
            tracing::warn!("GetElementPtr on non-parameter base, defaulting to i32");
            self.get_i32_type()
        };

        // Create pointer type to the element
        let element_ptr_type =
            self.builder
                .type_pointer(None, StorageClass::StorageBuffer, element_type);

        // OpAccessChain to compute element pointer
        // Indices: struct member 0 (the array), then the array index
        let u32_type = self.get_u32_type();
        let zero = self.builder.constant_bit32(u32_type, 0);
        let ptr_id = self
            .builder
            .access_chain(element_ptr_type, None, base_id, vec![zero, index_id])
            .map_err(|e| CompileError::Codegen(format!("Failed to emit access chain: {}", e)))?;

        self.vreg_id_map.insert(dest, ptr_id);
        Ok(())
    }
}

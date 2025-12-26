//! SPIR-V module builder
//!
//! This module provides functionality to construct SPIR-V bytecode from Simple's MIR.

use crate::error::CompileError;
use crate::hir::{BinOp, TypeId};
use crate::mir::{BlockId, GpuAtomicOp, GpuMemoryScope, MirFunction, MirInst, MirModule, Terminator, VReg};
use rspirv::dr::{Builder, Module};
use rspirv::spirv::{
    AddressingModel, Capability, Decoration, ExecutionMode, ExecutionModel, MemoryModel, StorageClass, Word,
};
use std::collections::HashMap;

/// SPIR-V module builder
///
/// Translates Simple's MIR (Mid-level IR) to SPIR-V bytecode for Vulkan compute shaders.
///
/// # Architecture
///
/// ```text
/// MirModule → SpirvModule
///   ├─ Initialize SPIR-V module (version 1.3, Vulkan memory model)
///   ├─ Register capabilities (Shader, VulkanMemoryModel, Int64, Float64)
///   ├─ Lower each MIR function:
///   │   ├─ Map Simple types → SPIR-V types
///   │   ├─ Allocate SPIR-V IDs for registers (VReg → Word)
///   │   ├─ Translate MIR instructions:
///   │   │   ├─ GpuGlobalId → OpLoad(gl_GlobalInvocationID) + OpCompositeExtract
///   │   │   ├─ GpuBarrier → OpControlBarrier
///   │   │   ├─ GpuAtomic → OpAtomicIAdd/ISub/UMin/UMax/And/Or/Xor/Exchange
///   │   │   ├─ BinOp → OpIAdd/FAdd/IMul/FMul/etc.
///   │   │   └─ Store/Load → OpStore/OpLoad
///   │   └─ Emit OpReturn
///   └─ Serialize to bytecode (Vec<u8>)
/// ```
pub struct SpirvModule {
    /// rspirv builder for constructing SPIR-V
    builder: Builder,

    /// Module being built
    module: Module,

    /// Map from MIR function name to SPIR-V function ID
    func_id_map: HashMap<String, Word>,

    /// Map from MIR virtual register to SPIR-V ID (per function)
    vreg_id_map: HashMap<VReg, Word>,

    /// Map from MIR block ID to SPIR-V label ID (per function)
    block_id_map: HashMap<BlockId, Word>,

    /// Map from parameter index to SPIR-V global variable ID
    param_var_map: HashMap<usize, Word>,

    /// Map from parameter index to element TypeId (for accessing array elements)
    param_elem_type_map: HashMap<usize, TypeId>,

    /// Map from VReg to parameter index (for tracking which VReg holds which parameter reference)
    vreg_param_map: HashMap<VReg, usize>,

    /// Map from VReg to TypeId (for type-aware operation selection)
    vreg_types: HashMap<VReg, TypeId>,

    /// Type IDs cache (to avoid recreating identical types)
    type_cache: TypeCache,
}

/// Cache for SPIR-V type IDs to avoid duplication
#[derive(Default)]
struct TypeCache {
    void_type: Option<Word>,
    bool_type: Option<Word>,
    i32_type: Option<Word>,
    i64_type: Option<Word>,
    u32_type: Option<Word>,
    u64_type: Option<Word>,
    f32_type: Option<Word>,
    f64_type: Option<Word>,
    vec3_u32_type: Option<Word>,
    ptr_input_vec3_u32: Option<Word>,
}

impl SpirvModule {
    /// Create a new SPIR-V module builder
    ///
    /// Initializes:
    /// - SPIR-V version 1.3 (for Vulkan 1.1+)
    /// - Capabilities: Shader, VulkanMemoryModel
    /// - Memory model: Logical, Vulkan
    pub fn new() -> Result<Self, CompileError> {
        let mut builder = Builder::new();
        builder.set_version(1, 3); // SPIR-V 1.3 for Vulkan 1.1+

        // Required capabilities for compute shaders
        builder.capability(Capability::Shader);
        builder.capability(Capability::VulkanMemoryModel);

        // Optional capabilities for extended types
        builder.capability(Capability::Int64);
        builder.capability(Capability::Float64);

        // Set memory model (Logical addressing, Vulkan memory model)
        builder.memory_model(AddressingModel::Logical, MemoryModel::Vulkan);

        Ok(Self {
            builder,
            module: Module::new(),
            func_id_map: HashMap::new(),
            vreg_id_map: HashMap::new(),
            block_id_map: HashMap::new(),
            param_var_map: HashMap::new(),
            param_elem_type_map: HashMap::new(),
            vreg_param_map: HashMap::new(),
            vreg_types: HashMap::new(),
            type_cache: TypeCache::default(),
        })
    }

    /// Compile a MIR module to SPIR-V
    pub fn compile_module(&mut self, mir_module: &MirModule) -> Result<(), CompileError> {
        // First pass: register all functions and create entry points
        for func in &mir_module.functions {
            if func.attributes.contains(&"gpu".to_string()) {
                self.register_kernel_function(func)?;
            }
        }

        // Second pass: compile function bodies
        for func in &mir_module.functions {
            if func.attributes.contains(&"gpu".to_string()) {
                self.compile_kernel_function(func)?;
            }
        }

        Ok(())
    }

    /// Register a GPU kernel function (creates entry point)
    fn register_kernel_function(&mut self, func: &MirFunction) -> Result<(), CompileError> {
        let void_type = self.get_void_type();
        let func_type = self.builder.type_function(void_type, vec![]);

        // Create function
        let func_id = self.builder.begin_function(
            void_type,
            None,
            rspirv::spirv::FunctionControl::NONE,
            func_type,
        ).map_err(|e| CompileError::Codegen(format!("Failed to create SPIR-V function: {}", e)))?;

        self.func_id_map.insert(func.name.clone(), func_id);

        // Create buffer parameters as global variables
        let mut interface_vars = Vec::new();
        for (i, param) in func.params.iter().enumerate() {
            let var_id = self.create_buffer_parameter(i, param)?;
            interface_vars.push(var_id);
        }

        // Mark as entry point for compute shader
        self.builder.entry_point(
            ExecutionModel::GLCompute,
            func_id,
            &func.name,
            interface_vars,
        );

        // Set execution mode (local size will be set from kernel launch parameters)
        // For now, use a default 1x1x1 (will be overridden at runtime)
        self.builder.execution_mode(func_id, ExecutionMode::LocalSize, vec![1, 1, 1]);

        Ok(())
    }

    /// Create a buffer parameter as a global SPIR-V variable
    ///
    /// In SPIR-V compute shaders, kernel parameters are represented as global variables
    /// in the StorageBuffer storage class, bound via descriptor sets.
    fn create_buffer_parameter(&mut self, index: usize, param: &crate::mir::MirLocal) -> Result<Word, CompileError> {
        // Determine element type from parameter TypeId
        // For array/pointer types, we'd need to extract the element type
        // For now, use the parameter type directly (assumes primitive type buffers)
        let element_type = self.type_id_to_spirv(param.ty)?;

        // Create runtime array type: OpTypeRuntimeArray %element_type
        let runtime_array_type = self.builder.type_runtime_array(element_type);

        // Create struct containing the runtime array (required for StorageBuffer)
        // struct BufferBlock { data: i32[] }
        let struct_type = self.builder.type_struct(vec![runtime_array_type]);

        // Decorate the struct
        self.builder.decorate(
            struct_type,
            Decoration::Block,
            vec![],
        );

        // Decorate the member (offset 0)
        self.builder.member_decorate(
            struct_type,
            0,
            Decoration::Offset,
            vec![rspirv::dr::Operand::LiteralBit32(0)],
        );

        // Create pointer type to the struct in StorageBuffer storage class
        let ptr_type = self.builder.type_pointer(None, StorageClass::StorageBuffer, struct_type);

        // Create the global variable
        let var_id = self.builder.variable(ptr_type, None, StorageClass::StorageBuffer, None);

        // Decorate with descriptor set and binding
        self.builder.decorate(
            var_id,
            Decoration::DescriptorSet,
            vec![rspirv::dr::Operand::LiteralBit32(0)],
        );

        self.builder.decorate(
            var_id,
            Decoration::Binding,
            vec![rspirv::dr::Operand::LiteralBit32(index as u32)],
        );

        // Store the mapping
        self.param_var_map.insert(index, var_id);
        self.param_elem_type_map.insert(index, param.ty);

        Ok(var_id)
    }

    /// Compile a GPU kernel function body
    fn compile_kernel_function(&mut self, func: &MirFunction) -> Result<(), CompileError> {
        // Clear maps for this function
        self.vreg_id_map.clear();
        self.block_id_map.clear();
        self.vreg_types.clear();

        // Pre-allocate labels for all blocks
        for (i, _) in func.blocks.iter().enumerate() {
            let block_id = BlockId(i.try_into().unwrap());
            let label = self.builder.id();
            self.block_id_map.insert(block_id, label);
        }

        // Compile all blocks
        for (i, block) in func.blocks.iter().enumerate() {
            let block_id = BlockId(i.try_into().unwrap());

            // Start the block with its pre-allocated label
            let label = *self.block_id_map.get(&block_id)
                .ok_or_else(|| CompileError::Codegen(format!("Missing label for block {:?}", block_id)))?;

            self.builder.begin_block(Some(label))
                .map_err(|e| CompileError::Codegen(format!("Failed to begin block: {}", e)))?;

            // Compile instructions
            for inst in &block.instructions {
                self.lower_instruction(inst)?;
            }

            // Compile terminator
            self.lower_terminator(&block.terminator)?;
        }

        // End function
        self.builder.end_function()
            .map_err(|e| CompileError::Codegen(format!("Failed to end function: {}", e)))?;

        Ok(())
    }

    /// Lower a block terminator to SPIR-V control flow
    fn lower_terminator(&mut self, term: &Terminator) -> Result<(), CompileError> {
        match term {
            Terminator::Return(None) => {
                self.builder.ret()
                    .map_err(|e| CompileError::Codegen(format!("Failed to emit return: {}", e)))?;
            }

            Terminator::Return(Some(vreg)) => {
                let value_id = *self.vreg_id_map.get(vreg)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined return value register: {:?}", vreg)))?;

                self.builder.ret_value(value_id)
                    .map_err(|e| CompileError::Codegen(format!("Failed to emit return value: {}", e)))?;
            }

            Terminator::Jump(target) => {
                let target_label = *self.block_id_map.get(target)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined jump target: {:?}", target)))?;

                self.builder.branch(target_label)
                    .map_err(|e| CompileError::Codegen(format!("Failed to emit branch: {}", e)))?;
            }

            Terminator::Branch { cond, then_block, else_block } => {
                let cond_id = *self.vreg_id_map.get(cond)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined condition register: {:?}", cond)))?;

                let then_label = *self.block_id_map.get(then_block)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined then block: {:?}", then_block)))?;

                let else_label = *self.block_id_map.get(else_block)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined else block: {:?}", else_block)))?;

                self.builder.branch_conditional(cond_id, then_label, else_label, vec![])
                    .map_err(|e| CompileError::Codegen(format!("Failed to emit conditional branch: {}", e)))?;
            }

            Terminator::Unreachable => {
                self.builder.unreachable()
                    .map_err(|e| CompileError::Codegen(format!("Failed to emit unreachable: {}", e)))?;
            }
        }

        Ok(())
    }

    /// Lower a single MIR instruction to SPIR-V
    ///
    /// This is the core translation logic that maps MIR instructions to SPIR-V operations.
    fn lower_instruction(&mut self, inst: &MirInst) -> Result<(), CompileError> {
        match inst {
            // Constants
            MirInst::ConstInt { dest, value } => {
                // Determine type based on value range
                // For now, use i32 for small values, i64 for larger
                let (type_id, const_id) = if *value >= i32::MIN as i64 && *value <= i32::MAX as i64 {
                    let i32_type = self.get_i32_type();
                    (TypeId::I32, self.builder.constant_bit32(i32_type, *value as u32))
                } else {
                    let i64_type = self.get_i64_type();
                    (TypeId::I64, self.builder.constant_bit64(i64_type, *value as u64))
                };
                self.vreg_id_map.insert(*dest, const_id);
                self.vreg_types.insert(*dest, type_id);
            }

            MirInst::ConstFloat { dest, value } => {
                // Use f32 by default
                let f32_type = self.get_f32_type();
                let const_id = self.builder.constant_bit32(f32_type, (*value as f32).to_bits());
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
                let src_id = *self.vreg_id_map.get(src)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined register: {:?}", src)))?;
                self.vreg_id_map.insert(*dest, src_id);

                // Propagate type
                if let Some(&src_type) = self.vreg_types.get(src) {
                    self.vreg_types.insert(*dest, src_type);
                }
            }

            // Binary operations
            MirInst::BinOp { dest, op, left, right } => {
                let left_id = *self.vreg_id_map.get(left)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined register: {:?}", left)))?;
                let right_id = *self.vreg_id_map.get(right)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined register: {:?}", right)))?;

                // Get operand type (default to i32 if not tracked)
                let left_type = self.vreg_types.get(left).copied().unwrap_or(TypeId::I32);

                // Select SPIR-V type and operation based on operand type
                let (result_type_id, result_spirv_type, result) = match (op, left_type) {
                    // Arithmetic operations
                    (BinOp::Add, TypeId::I32 | TypeId::I64) => {
                        let ty = self.type_id_to_spirv(left_type)?;
                        (left_type, ty, self.builder.i_add(ty, None, left_id, right_id)?)
                    }
                    (BinOp::Add, TypeId::U32 | TypeId::U64) => {
                        let ty = self.type_id_to_spirv(left_type)?;
                        (left_type, ty, self.builder.i_add(ty, None, left_id, right_id)?)
                    }
                    (BinOp::Add, TypeId::F32 | TypeId::F64) => {
                        let ty = self.type_id_to_spirv(left_type)?;
                        (left_type, ty, self.builder.f_add(ty, None, left_id, right_id)?)
                    }

                    (BinOp::Sub, TypeId::I32 | TypeId::I64 | TypeId::U32 | TypeId::U64) => {
                        let ty = self.type_id_to_spirv(left_type)?;
                        (left_type, ty, self.builder.i_sub(ty, None, left_id, right_id)?)
                    }
                    (BinOp::Sub, TypeId::F32 | TypeId::F64) => {
                        let ty = self.type_id_to_spirv(left_type)?;
                        (left_type, ty, self.builder.f_sub(ty, None, left_id, right_id)?)
                    }

                    (BinOp::Mul, TypeId::I32 | TypeId::I64 | TypeId::U32 | TypeId::U64) => {
                        let ty = self.type_id_to_spirv(left_type)?;
                        (left_type, ty, self.builder.i_mul(ty, None, left_id, right_id)?)
                    }
                    (BinOp::Mul, TypeId::F32 | TypeId::F64) => {
                        let ty = self.type_id_to_spirv(left_type)?;
                        (left_type, ty, self.builder.f_mul(ty, None, left_id, right_id)?)
                    }

                    (BinOp::Div, TypeId::I32 | TypeId::I64) => {
                        let ty = self.type_id_to_spirv(left_type)?;
                        (left_type, ty, self.builder.s_div(ty, None, left_id, right_id)?)
                    }
                    (BinOp::Div, TypeId::U32 | TypeId::U64) => {
                        let ty = self.type_id_to_spirv(left_type)?;
                        (left_type, ty, self.builder.u_div(ty, None, left_id, right_id)?)
                    }
                    (BinOp::Div, TypeId::F32 | TypeId::F64) => {
                        let ty = self.type_id_to_spirv(left_type)?;
                        (left_type, ty, self.builder.f_div(ty, None, left_id, right_id)?)
                    }

                    (BinOp::Mod, TypeId::I32 | TypeId::I64) => {
                        let ty = self.type_id_to_spirv(left_type)?;
                        (left_type, ty, self.builder.s_mod(ty, None, left_id, right_id)?)
                    }
                    (BinOp::Mod, TypeId::U32 | TypeId::U64) => {
                        let ty = self.type_id_to_spirv(left_type)?;
                        (left_type, ty, self.builder.u_mod(ty, None, left_id, right_id)?)
                    }
                    (BinOp::Mod, TypeId::F32 | TypeId::F64) => {
                        let ty = self.type_id_to_spirv(left_type)?;
                        (left_type, ty, self.builder.f_mod(ty, None, left_id, right_id)?)
                    }

                    // Comparison operations (return bool)
                    (BinOp::Lt, TypeId::I32 | TypeId::I64) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.s_less_than(bool_type, None, left_id, right_id)?)
                    }
                    (BinOp::Lt, TypeId::U32 | TypeId::U64) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.u_less_than(bool_type, None, left_id, right_id)?)
                    }
                    (BinOp::Lt, TypeId::F32 | TypeId::F64) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.f_ord_less_than(bool_type, None, left_id, right_id)?)
                    }

                    (BinOp::LtEq, TypeId::I32 | TypeId::I64) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.s_less_than_equal(bool_type, None, left_id, right_id)?)
                    }
                    (BinOp::LtEq, TypeId::U32 | TypeId::U64) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.u_less_than_equal(bool_type, None, left_id, right_id)?)
                    }
                    (BinOp::LtEq, TypeId::F32 | TypeId::F64) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.f_ord_less_than_equal(bool_type, None, left_id, right_id)?)
                    }

                    (BinOp::Gt, TypeId::I32 | TypeId::I64) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.s_greater_than(bool_type, None, left_id, right_id)?)
                    }
                    (BinOp::Gt, TypeId::U32 | TypeId::U64) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.u_greater_than(bool_type, None, left_id, right_id)?)
                    }
                    (BinOp::Gt, TypeId::F32 | TypeId::F64) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.f_ord_greater_than(bool_type, None, left_id, right_id)?)
                    }

                    (BinOp::GtEq, TypeId::I32 | TypeId::I64) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.s_greater_than_equal(bool_type, None, left_id, right_id)?)
                    }
                    (BinOp::GtEq, TypeId::U32 | TypeId::U64) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.u_greater_than_equal(bool_type, None, left_id, right_id)?)
                    }
                    (BinOp::GtEq, TypeId::F32 | TypeId::F64) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.f_ord_greater_than_equal(bool_type, None, left_id, right_id)?)
                    }

                    (BinOp::Eq, TypeId::F32 | TypeId::F64) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.f_ord_equal(bool_type, None, left_id, right_id)?)
                    }
                    (BinOp::Eq, _) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.i_equal(bool_type, None, left_id, right_id)?)
                    }

                    (BinOp::NotEq, TypeId::F32 | TypeId::F64) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.f_ord_not_equal(bool_type, None, left_id, right_id)?)
                    }
                    (BinOp::NotEq, _) => {
                        let bool_type = self.get_bool_type();
                        (TypeId::BOOL, bool_type, self.builder.i_not_equal(bool_type, None, left_id, right_id)?)
                    }

                    // Bitwise operations (integer only)
                    (BinOp::BitAnd, ty @ (TypeId::I32 | TypeId::I64 | TypeId::U32 | TypeId::U64)) => {
                        let spirv_ty = self.type_id_to_spirv(ty)?;
                        (ty, spirv_ty, self.builder.bitwise_and(spirv_ty, None, left_id, right_id)?)
                    }
                    (BinOp::BitOr, ty @ (TypeId::I32 | TypeId::I64 | TypeId::U32 | TypeId::U64)) => {
                        let spirv_ty = self.type_id_to_spirv(ty)?;
                        (ty, spirv_ty, self.builder.bitwise_or(spirv_ty, None, left_id, right_id)?)
                    }
                    (BinOp::BitXor, ty @ (TypeId::I32 | TypeId::I64 | TypeId::U32 | TypeId::U64)) => {
                        let spirv_ty = self.type_id_to_spirv(ty)?;
                        (ty, spirv_ty, self.builder.bitwise_xor(spirv_ty, None, left_id, right_id)?)
                    }

                    _ => return Err(CompileError::Codegen(format!(
                        "Unsupported binary op {:?} for type {:?}",
                        op, left_type
                    ))),
                };

                self.vreg_id_map.insert(*dest, result);
                self.vreg_types.insert(*dest, result_type_id);
            }

            // GPU built-ins
            MirInst::GpuGlobalId { dest, dim } => {
                // gl_GlobalInvocationID is a built-in vec3<u32>
                // We need to:
                // 1. Declare gl_GlobalInvocationID as Input variable
                // 2. Load it
                // 3. Extract the requested component (x=0, y=1, z=2)

                let u32_type = self.get_u32_type();
                let vec3_u32_type = self.get_vec3_u32_type();
                let ptr_type = self.get_ptr_input_vec3_u32_type();

                // Create variable for gl_GlobalInvocationID (this should be done once per module)
                // TODO: Cache this to avoid recreating
                let global_id_var = self.builder.variable(
                    ptr_type,
                    None,
                    StorageClass::Input,
                    None,
                );

                // Decorate it as GlobalInvocationId built-in
                self.builder.decorate(
                    global_id_var,
                    Decoration::BuiltIn,
                    vec![rspirv::dr::Operand::BuiltIn(rspirv::spirv::BuiltIn::GlobalInvocationId)],
                );

                // Load the vec3
                let loaded = self.builder.load(vec3_u32_type, None, global_id_var, None, vec![])
                    .map_err(|e| CompileError::Codegen(format!("Failed to load GlobalInvocationId: {}", e)))?;

                // Extract component
                let component = self.builder.composite_extract(u32_type, None, loaded, vec![*dim as u32])
                    .map_err(|e| CompileError::Codegen(format!("Failed to extract component: {}", e)))?;

                self.vreg_id_map.insert(*dest, component);
                self.vreg_types.insert(*dest, TypeId::U32);
            }

            MirInst::GpuBarrier => {
                // OpControlBarrier(execution, memory, semantics)
                // execution: Workgroup scope
                // memory: Workgroup scope
                // semantics: Acquire | Release | WorkgroupMemory

                let u32_type = self.get_u32_type();

                // Scope::Workgroup = 2
                let scope_workgroup = self.builder.constant_bit32(u32_type, 2);

                // MemorySemantics: AcquireRelease (0x8) | WorkgroupMemory (0x100) = 0x108
                let semantics = self.builder.constant_bit32(u32_type, 0x108);

                self.builder.control_barrier(scope_workgroup, scope_workgroup, semantics)
                    .map_err(|e| CompileError::Codegen(format!("Failed to emit barrier: {}", e)))?;
            }

            MirInst::GpuAtomic { dest, op, ptr, value } => {
                let ptr_id = *self.vreg_id_map.get(ptr)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined register: {:?}", ptr)))?;
                let value_id = *self.vreg_id_map.get(value)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined register: {:?}", value)))?;

                let u32_type = self.get_u32_type();

                // Scope: Workgroup (2)
                let scope = self.builder.constant_bit32(u32_type, 2);

                // Semantics: Relaxed (0)
                let semantics = self.builder.constant_bit32(u32_type, 0);

                let result = match op {
                    GpuAtomicOp::Add => {
                        self.builder.atomic_i_add(u32_type, None, ptr_id, scope, semantics, value_id)
                    }
                    GpuAtomicOp::Sub => {
                        self.builder.atomic_i_sub(u32_type, None, ptr_id, scope, semantics, value_id)
                    }
                    GpuAtomicOp::Min => {
                        self.builder.atomic_u_min(u32_type, None, ptr_id, scope, semantics, value_id)
                    }
                    GpuAtomicOp::Max => {
                        self.builder.atomic_u_max(u32_type, None, ptr_id, scope, semantics, value_id)
                    }
                    GpuAtomicOp::And => {
                        self.builder.atomic_and(u32_type, None, ptr_id, scope, semantics, value_id)
                    }
                    GpuAtomicOp::Or => {
                        self.builder.atomic_or(u32_type, None, ptr_id, scope, semantics, value_id)
                    }
                    GpuAtomicOp::Xor => {
                        self.builder.atomic_xor(u32_type, None, ptr_id, scope, semantics, value_id)
                    }
                    GpuAtomicOp::Xchg => {
                        self.builder.atomic_exchange(u32_type, None, ptr_id, scope, semantics, value_id)
                    }
                }.map_err(|e| CompileError::Codegen(format!("Failed to emit atomic: {}", e)))?;

                self.vreg_id_map.insert(*dest, result);
            }

            MirInst::GpuLocalId { dest, dim } => {
                // gl_LocalInvocationID
                let u32_type = self.get_u32_type();
                let vec3_u32_type = self.get_vec3_u32_type();
                let ptr_type = self.get_ptr_input_vec3_u32_type();

                let local_id_var = self.builder.variable(ptr_type, None, StorageClass::Input, None);
                self.builder.decorate(
                    local_id_var,
                    Decoration::BuiltIn,
                    vec![rspirv::dr::Operand::BuiltIn(rspirv::spirv::BuiltIn::LocalInvocationId)],
                );

                let loaded = self.builder.load(vec3_u32_type, None, local_id_var, None, vec![])
                    .map_err(|e| CompileError::Codegen(format!("Failed to load LocalInvocationId: {}", e)))?;

                let component = self.builder.composite_extract(u32_type, None, loaded, vec![*dim as u32])
                    .map_err(|e| CompileError::Codegen(format!("Failed to extract component: {}", e)))?;

                self.vreg_id_map.insert(*dest, component);
                self.vreg_types.insert(*dest, TypeId::U32);
            }

            MirInst::GpuGroupId { dest, dim } => {
                // gl_WorkGroupID
                let u32_type = self.get_u32_type();
                let vec3_u32_type = self.get_vec3_u32_type();
                let ptr_type = self.get_ptr_input_vec3_u32_type();

                let group_id_var = self.builder.variable(ptr_type, None, StorageClass::Input, None);
                self.builder.decorate(
                    group_id_var,
                    Decoration::BuiltIn,
                    vec![rspirv::dr::Operand::BuiltIn(rspirv::spirv::BuiltIn::WorkgroupId)],
                );

                let loaded = self.builder.load(vec3_u32_type, None, group_id_var, None, vec![])
                    .map_err(|e| CompileError::Codegen(format!("Failed to load WorkgroupId: {}", e)))?;

                let component = self.builder.composite_extract(u32_type, None, loaded, vec![*dim as u32])
                    .map_err(|e| CompileError::Codegen(format!("Failed to extract component: {}", e)))?;

                self.vreg_id_map.insert(*dest, component);
                self.vreg_types.insert(*dest, TypeId::U32);
            }

            // Memory operations
            MirInst::Load { dest, addr, ty } => {
                let addr_id = *self.vreg_id_map.get(addr)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined address register: {:?}", addr)))?;

                // Use TypeId to determine result type
                let result_type = self.type_id_to_spirv(*ty)?;

                let loaded = self.builder.load(result_type, None, addr_id, None, vec![])
                    .map_err(|e| CompileError::Codegen(format!("Failed to load from memory: {}", e)))?;

                self.vreg_id_map.insert(*dest, loaded);
                self.vreg_types.insert(*dest, *ty);
            }

            MirInst::Store { addr, value, ty } => {
                let addr_id = *self.vreg_id_map.get(addr)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined address register: {:?}", addr)))?;
                let value_id = *self.vreg_id_map.get(value)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined value register: {:?}", value)))?;

                // Type is used to ensure proper storage (though SPIR-V doesn't explicitly need it for OpStore)
                let _ = self.type_id_to_spirv(*ty)?; // Validate type exists

                self.builder.store(addr_id, value_id, None, vec![])
                    .map_err(|e| CompileError::Codegen(format!("Failed to store to memory: {}", e)))?;

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
                    // TODO: Handle local variables (would need to track OpVariable for locals)
                    return Err(CompileError::Codegen(format!(
                        "LocalAddr for non-parameter local {} not yet implemented",
                        local_index
                    )));
                }
            }

            MirInst::GetElementPtr { dest, base, index } => {
                // OpAccessChain - compute pointer to array element
                let base_id = *self.vreg_id_map.get(base)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined base register: {:?}", base)))?;
                let index_id = *self.vreg_id_map.get(index)
                    .ok_or_else(|| CompileError::Codegen(format!("Undefined index register: {:?}", index)))?;

                // Determine element type from the base parameter
                let element_type = if let Some(&param_idx) = self.vreg_param_map.get(base) {
                    // Base is a parameter, get its element type
                    let ty = *self.param_elem_type_map.get(&param_idx)
                        .ok_or_else(|| CompileError::Codegen(format!("Parameter {} element type not found", param_idx)))?;
                    self.type_id_to_spirv(ty)?
                } else {
                    // Not a parameter, default to i32
                    // TODO: Track types for non-parameter pointers
                    tracing::warn!("GetElementPtr on non-parameter base, defaulting to i32");
                    self.get_i32_type()
                };

                // Create pointer type to the element
                let element_ptr_type = self.builder.type_pointer(None, StorageClass::StorageBuffer, element_type);

                // OpAccessChain to compute element pointer
                // Indices: struct member 0 (the array), then the array index
                let u32_type = self.get_u32_type();
                let zero = self.builder.constant_bit32(u32_type, 0);
                let ptr_id = self.builder.access_chain(element_ptr_type, None, base_id, vec![zero, index_id])
                    .map_err(|e| CompileError::Codegen(format!("Failed to emit access chain: {}", e)))?;

                self.vreg_id_map.insert(*dest, ptr_id);
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

    // Type getters with caching

    fn get_void_type(&mut self) -> Word {
        *self.type_cache.void_type.get_or_insert_with(|| {
            self.builder.type_void()
        })
    }

    fn get_bool_type(&mut self) -> Word {
        *self.type_cache.bool_type.get_or_insert_with(|| {
            self.builder.type_bool()
        })
    }

    fn get_i32_type(&mut self) -> Word {
        *self.type_cache.i32_type.get_or_insert_with(|| {
            self.builder.type_int(32, 1) // signed 32-bit
        })
    }

    fn get_f32_type(&mut self) -> Word {
        *self.type_cache.f32_type.get_or_insert_with(|| {
            self.builder.type_float(32)
        })
    }

    fn get_u32_type(&mut self) -> Word {
        *self.type_cache.u32_type.get_or_insert_with(|| {
            self.builder.type_int(32, 0) // unsigned 32-bit
        })
    }

    fn get_i64_type(&mut self) -> Word {
        *self.type_cache.i64_type.get_or_insert_with(|| {
            self.builder.type_int(64, 1) // signed 64-bit
        })
    }

    fn get_u64_type(&mut self) -> Word {
        *self.type_cache.u64_type.get_or_insert_with(|| {
            self.builder.type_int(64, 0) // unsigned 64-bit
        })
    }

    fn get_f64_type(&mut self) -> Word {
        *self.type_cache.f64_type.get_or_insert_with(|| {
            self.builder.type_float(64)
        })
    }

    /// Map TypeId to SPIR-V type Word
    ///
    /// Converts Simple's TypeId to the corresponding SPIR-V type ID.
    /// Currently supports primitive types only.
    fn type_id_to_spirv(&mut self, ty: TypeId) -> Result<Word, CompileError> {
        match ty {
            TypeId::VOID => Ok(self.get_void_type()),
            TypeId::BOOL => Ok(self.get_bool_type()),
            TypeId::I32 => Ok(self.get_i32_type()),
            TypeId::I64 => Ok(self.get_i64_type()),
            TypeId::U32 => Ok(self.get_u32_type()),
            TypeId::U64 => Ok(self.get_u64_type()),
            TypeId::F32 => Ok(self.get_f32_type()),
            TypeId::F64 => Ok(self.get_f64_type()),
            _ => {
                // For complex types, we'd need to query the type registry
                // For now, default to i32 for unknown types
                tracing::warn!("Unsupported TypeId {:?}, defaulting to i32", ty);
                Ok(self.get_i32_type())
            }
        }
    }

    fn get_vec3_u32_type(&mut self) -> Word {
        if let Some(id) = self.type_cache.vec3_u32_type {
            return id;
        }
        let u32_type = self.get_u32_type();
        let id = self.builder.type_vector(u32_type, 3);
        self.type_cache.vec3_u32_type = Some(id);
        id
    }

    fn get_ptr_input_vec3_u32_type(&mut self) -> Word {
        if let Some(id) = self.type_cache.ptr_input_vec3_u32 {
            return id;
        }
        let vec3_u32 = self.get_vec3_u32_type();
        let id = self.builder.type_pointer(None, StorageClass::Input, vec3_u32);
        self.type_cache.ptr_input_vec3_u32 = Some(id);
        id
    }

    /// Finalize and return SPIR-V bytecode
    ///
    /// Serializes the constructed SPIR-V module to bytecode (32-bit words).
    pub fn into_bytes(self) -> Result<Vec<u8>, CompileError> {
        // Validate the module
        // TODO: Add SPIR-V validation using spirv-val or rspirv's built-in validation

        // The Builder's module() returns the internal Module
        // We need to use binary::Assemble trait to convert it to words
        use rspirv::binary::Assemble;

        let module = self.builder.module();
        let words: Vec<u32> = module.assemble();

        // Convert to bytes (SPIR-V is little-endian)
        let bytes: Vec<u8> = words.iter()
            .flat_map(|word| word.to_le_bytes())
            .collect();

        Ok(bytes)
    }
}

impl Default for SpirvModule {
    fn default() -> Self {
        Self::new().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spirv_module_creation() {
        let module = SpirvModule::new();
        assert!(module.is_ok(), "Failed to create SPIR-V module");
    }

    #[test]
    fn test_spirv_module_serialization() {
        let module = SpirvModule::new().unwrap();
        let bytes = module.into_bytes();
        assert!(bytes.is_ok(), "Failed to serialize SPIR-V module");

        let bytes = bytes.unwrap();
        // SPIR-V files start with magic number 0x07230203
        assert!(bytes.len() >= 20, "SPIR-V module too small"); // At least header

        // Check magic number (little-endian)
        let magic = u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
        assert_eq!(magic, 0x07230203, "Invalid SPIR-V magic number");
    }

    #[test]
    fn test_type_caching() {
        let mut module = SpirvModule::new().unwrap();

        let u32_1 = module.get_u32_type();
        let u32_2 = module.get_u32_type();
        assert_eq!(u32_1, u32_2, "Type IDs should be cached");

        let vec3_1 = module.get_vec3_u32_type();
        let vec3_2 = module.get_vec3_u32_type();
        assert_eq!(vec3_1, vec3_2, "Vector type IDs should be cached");
    }
}

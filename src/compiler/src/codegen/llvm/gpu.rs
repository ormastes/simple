//! LLVM GPU backend for CUDA/PTX code generation.
//!
//! This module provides GPU kernel compilation using LLVM's NVPTX backend to generate
//! PTX (Parallel Thread Execution) code that can be executed on NVIDIA GPUs via CUDA.
//!
//! # Architecture
//!
//! ```text
//! MIR GPU Instructions
//!        │
//!        ▼
//! ┌─────────────────┐
//! │  LlvmGpuBackend │  ← This module
//! └────────┬────────┘
//!          │
//!          ▼
//! ┌─────────────────┐
//! │   NVVM IR       │  ← LLVM IR with NVPTX intrinsics
//! └────────┬────────┘
//!          │
//!          ▼
//! ┌─────────────────┐
//! │   PTX Code      │  ← Assembly for NVIDIA GPUs
//! └────────┬────────┘
//!          │
//!          ▼
//! ┌─────────────────┐
//! │  CUDA Runtime   │  ← cuModuleLoadData, cuLaunchKernel
//! └─────────────────┘
//! ```
//!
//! # Usage
//!
//! ```ignore
//! let gpu_backend = LlvmGpuBackend::new()?;
//! gpu_backend.create_kernel_module("my_kernel")?;
//! gpu_backend.compile_kernel(&mir_function)?;
//! let ptx = gpu_backend.emit_ptx()?;
//! ```

use crate::error::CompileError;
use crate::mir::MirFunction;

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::context::Context;
#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target as LlvmTarget, TargetMachine,
    TargetTriple,
};
#[cfg(feature = "llvm")]
use inkwell::types::BasicTypeEnum;
#[cfg(feature = "llvm")]
use inkwell::values::{BasicValueEnum, FunctionValue, IntValue, PointerValue};
#[cfg(feature = "llvm")]
use inkwell::{AddressSpace, IntPredicate, OptimizationLevel};
#[cfg(feature = "llvm")]
use std::cell::RefCell;
#[cfg(feature = "llvm")]
use std::collections::HashMap;

/// GPU compute capability version
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GpuComputeCapability {
    /// SM 5.0 (Maxwell)
    Sm50,
    /// SM 6.0 (Pascal)
    Sm60,
    /// SM 7.0 (Volta)
    Sm70,
    /// SM 7.5 (Turing)
    Sm75,
    /// SM 8.0 (Ampere)
    Sm80,
    /// SM 8.6 (Ampere GA102)
    Sm86,
    /// SM 8.9 (Ada Lovelace)
    Sm89,
    /// SM 9.0 (Hopper)
    Sm90,
}

impl GpuComputeCapability {
    /// Get the PTX version string for this compute capability
    pub fn ptx_version(&self) -> &'static str {
        match self {
            GpuComputeCapability::Sm50 => "50",
            GpuComputeCapability::Sm60 => "60",
            GpuComputeCapability::Sm70 => "70",
            GpuComputeCapability::Sm75 => "75",
            GpuComputeCapability::Sm80 => "80",
            GpuComputeCapability::Sm86 => "86",
            GpuComputeCapability::Sm89 => "89",
            GpuComputeCapability::Sm90 => "90",
        }
    }

    /// Get the target CPU string for LLVM
    pub fn llvm_cpu(&self) -> &'static str {
        match self {
            GpuComputeCapability::Sm50 => "sm_50",
            GpuComputeCapability::Sm60 => "sm_60",
            GpuComputeCapability::Sm70 => "sm_70",
            GpuComputeCapability::Sm75 => "sm_75",
            GpuComputeCapability::Sm80 => "sm_80",
            GpuComputeCapability::Sm86 => "sm_86",
            GpuComputeCapability::Sm89 => "sm_89",
            GpuComputeCapability::Sm90 => "sm_90",
        }
    }
}

impl Default for GpuComputeCapability {
    fn default() -> Self {
        // Default to SM 7.0 (Volta) for wide compatibility
        GpuComputeCapability::Sm70
    }
}

/// LLVM-based GPU code generator for CUDA/PTX
pub struct LlvmGpuBackend {
    /// Target compute capability
    compute_capability: GpuComputeCapability,
    /// Enable debug info in PTX
    debug_info: bool,
    #[cfg(feature = "llvm")]
    context: &'static Context,
    #[cfg(feature = "llvm")]
    module: RefCell<Option<Module<'static>>>,
    #[cfg(feature = "llvm")]
    builder: RefCell<Option<Builder<'static>>>,
    #[cfg(feature = "llvm")]
    kernel_functions: RefCell<Vec<String>>,
}

impl std::fmt::Debug for LlvmGpuBackend {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("LlvmGpuBackend")
            .field("compute_capability", &self.compute_capability)
            .field("debug_info", &self.debug_info)
            .finish()
    }
}

impl LlvmGpuBackend {
    /// Create a new GPU backend with default compute capability
    pub fn new() -> Result<Self, CompileError> {
        Self::with_compute_capability(GpuComputeCapability::default())
    }

    /// Create a new GPU backend with specified compute capability
    pub fn with_compute_capability(cc: GpuComputeCapability) -> Result<Self, CompileError> {
        #[cfg(not(feature = "llvm"))]
        {
            let _ = cc;
            Err(CompileError::Semantic(
                "LLVM GPU backend requires 'llvm' feature flag".to_string(),
            ))
        }

        #[cfg(feature = "llvm")]
        {
            // Initialize NVPTX target
            LlvmTarget::initialize_native(&InitializationConfig::default())
                .map_err(|e| CompileError::Semantic(format!("Failed to initialize LLVM: {}", e)))?;

            let context = Box::leak(Box::new(Context::create()));
            Ok(Self {
                compute_capability: cc,
                debug_info: false,
                context,
                module: RefCell::new(None),
                builder: RefCell::new(None),
                kernel_functions: RefCell::new(Vec::new()),
            })
        }
    }

    /// Enable debug information in generated PTX
    pub fn with_debug_info(mut self, enabled: bool) -> Self {
        self.debug_info = enabled;
        self
    }

    /// Get the NVPTX target triple
    pub fn get_target_triple(&self) -> String {
        // nvptx64-nvidia-cuda for 64-bit CUDA
        "nvptx64-nvidia-cuda".to_string()
    }

    /// Create a new LLVM module for GPU kernels
    #[cfg(feature = "llvm")]
    pub fn create_kernel_module(&self, name: &str) -> Result<(), CompileError> {
        let module = self.context.create_module(name);

        // Set target triple for NVPTX
        let triple = self.get_target_triple();
        module.set_triple(&TargetTriple::create(&triple));

        *self.module.borrow_mut() = Some(module);

        // Create builder
        let builder = self.context.create_builder();
        *self.builder.borrow_mut() = Some(builder);

        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn create_kernel_module(&self, _name: &str) -> Result<(), CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }

    /// Declare NVPTX intrinsics in the module
    #[cfg(feature = "llvm")]
    fn declare_nvptx_intrinsics(&self) -> Result<(), CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        let i32_type = self.context.i32_type();

        // Thread ID intrinsics: @llvm.nvvm.read.ptx.sreg.tid.{x,y,z}
        let tid_type = i32_type.fn_type(&[], false);
        module.add_function("llvm.nvvm.read.ptx.sreg.tid.x", tid_type, None);
        module.add_function("llvm.nvvm.read.ptx.sreg.tid.y", tid_type, None);
        module.add_function("llvm.nvvm.read.ptx.sreg.tid.z", tid_type, None);

        // Block ID intrinsics: @llvm.nvvm.read.ptx.sreg.ctaid.{x,y,z}
        module.add_function("llvm.nvvm.read.ptx.sreg.ctaid.x", tid_type, None);
        module.add_function("llvm.nvvm.read.ptx.sreg.ctaid.y", tid_type, None);
        module.add_function("llvm.nvvm.read.ptx.sreg.ctaid.z", tid_type, None);

        // Block dimension intrinsics: @llvm.nvvm.read.ptx.sreg.ntid.{x,y,z}
        module.add_function("llvm.nvvm.read.ptx.sreg.ntid.x", tid_type, None);
        module.add_function("llvm.nvvm.read.ptx.sreg.ntid.y", tid_type, None);
        module.add_function("llvm.nvvm.read.ptx.sreg.ntid.z", tid_type, None);

        // Grid dimension intrinsics: @llvm.nvvm.read.ptx.sreg.nctaid.{x,y,z}
        module.add_function("llvm.nvvm.read.ptx.sreg.nctaid.x", tid_type, None);
        module.add_function("llvm.nvvm.read.ptx.sreg.nctaid.y", tid_type, None);
        module.add_function("llvm.nvvm.read.ptx.sreg.nctaid.z", tid_type, None);

        // Barrier intrinsic: @llvm.nvvm.barrier0
        let void_type = self.context.void_type();
        let barrier_type = void_type.fn_type(&[], false);
        module.add_function("llvm.nvvm.barrier0", barrier_type, None);

        // Memory fence intrinsics
        module.add_function("llvm.nvvm.membar.cta", barrier_type, None);
        module.add_function("llvm.nvvm.membar.gl", barrier_type, None);
        module.add_function("llvm.nvvm.membar.sys", barrier_type, None);

        Ok(())
    }

    /// Create a GPU kernel function
    #[cfg(feature = "llvm")]
    pub fn create_kernel_function(
        &self,
        name: &str,
        param_types: &[BasicTypeEnum<'static>],
    ) -> Result<FunctionValue<'static>, CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        // Kernel functions return void
        let void_type = self.context.void_type();
        let param_types: Vec<_> = param_types.iter().map(|t| (*t).into()).collect();
        let fn_type = void_type.fn_type(&param_types, false);

        let function = module.add_function(name, fn_type, None);

        // Mark as kernel entry point with nvvm.annotations metadata
        // This is done via LLVM metadata: !nvvm.annotations = !{!0}
        // !0 = !{ptr @kernel_name, !"kernel", i32 1}
        self.add_kernel_metadata(module, function)?;

        // Track kernel function
        self.kernel_functions.borrow_mut().push(name.to_string());

        Ok(function)
    }

    #[cfg(not(feature = "llvm"))]
    pub fn create_kernel_function(
        &self,
        _name: &str,
        _param_types: &[()],
    ) -> Result<(), CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }

    /// Add kernel metadata for NVPTX
    #[cfg(feature = "llvm")]
    fn add_kernel_metadata(
        &self,
        module: &Module<'static>,
        function: FunctionValue<'static>,
    ) -> Result<(), CompileError> {
        // Create metadata nodes for kernel annotation
        let i32_type = self.context.i32_type();

        // Create "kernel" string metadata
        let kernel_str = self.context.metadata_string("kernel");

        // Create i32 1 for the annotation value
        let one = i32_type.const_int(1, false);

        // Create the annotation tuple: {function, "kernel", 1}
        let annotation = self.context.metadata_node(&[
            function.as_global_value().as_pointer_value().into(),
            kernel_str.into(),
            one.into(),
        ]);

        // Add to nvvm.annotations named metadata
        module
            .add_global_metadata("nvvm.annotations", &annotation)
            .map_err(|e| CompileError::Semantic(format!("Failed to add kernel metadata: {}", e)))?;

        Ok(())
    }

    /// Emit a call to get thread ID for a dimension
    #[cfg(feature = "llvm")]
    pub fn emit_thread_id(
        &self,
        builder: &Builder<'static>,
        dim: u8,
    ) -> Result<IntValue<'static>, CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        let intrinsic_name = match dim {
            0 => "llvm.nvvm.read.ptx.sreg.tid.x",
            1 => "llvm.nvvm.read.ptx.sreg.tid.y",
            2 => "llvm.nvvm.read.ptx.sreg.tid.z",
            _ => return Err(CompileError::Semantic("Invalid dimension".to_string())),
        };

        let func = module.get_function(intrinsic_name).ok_or_else(|| {
            CompileError::Semantic(format!("Intrinsic {} not declared", intrinsic_name))
        })?;

        let call = builder.build_call(func, &[], "tid").map_err(|e| {
            CompileError::Semantic(format!("Failed to call thread ID intrinsic: {}", e))
        })?;

        call.try_as_basic_value()
            .left()
            .and_then(|v| v.into_int_value().into())
            .ok_or_else(|| {
                CompileError::Semantic("Thread ID intrinsic returned unexpected type".to_string())
            })
    }

    /// Emit a call to get block ID for a dimension
    #[cfg(feature = "llvm")]
    pub fn emit_block_id(
        &self,
        builder: &Builder<'static>,
        dim: u8,
    ) -> Result<IntValue<'static>, CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        let intrinsic_name = match dim {
            0 => "llvm.nvvm.read.ptx.sreg.ctaid.x",
            1 => "llvm.nvvm.read.ptx.sreg.ctaid.y",
            2 => "llvm.nvvm.read.ptx.sreg.ctaid.z",
            _ => return Err(CompileError::Semantic("Invalid dimension".to_string())),
        };

        let func = module.get_function(intrinsic_name).ok_or_else(|| {
            CompileError::Semantic(format!("Intrinsic {} not declared", intrinsic_name))
        })?;

        let call = builder.build_call(func, &[], "ctaid").map_err(|e| {
            CompileError::Semantic(format!("Failed to call block ID intrinsic: {}", e))
        })?;

        call.try_as_basic_value()
            .left()
            .and_then(|v| v.into_int_value().into())
            .ok_or_else(|| {
                CompileError::Semantic("Block ID intrinsic returned unexpected type".to_string())
            })
    }

    /// Emit a call to get block dimension for a dimension
    #[cfg(feature = "llvm")]
    pub fn emit_block_dim(
        &self,
        builder: &Builder<'static>,
        dim: u8,
    ) -> Result<IntValue<'static>, CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        let intrinsic_name = match dim {
            0 => "llvm.nvvm.read.ptx.sreg.ntid.x",
            1 => "llvm.nvvm.read.ptx.sreg.ntid.y",
            2 => "llvm.nvvm.read.ptx.sreg.ntid.z",
            _ => return Err(CompileError::Semantic("Invalid dimension".to_string())),
        };

        let func = module.get_function(intrinsic_name).ok_or_else(|| {
            CompileError::Semantic(format!("Intrinsic {} not declared", intrinsic_name))
        })?;

        let call = builder.build_call(func, &[], "ntid").map_err(|e| {
            CompileError::Semantic(format!("Failed to call block dim intrinsic: {}", e))
        })?;

        call.try_as_basic_value()
            .left()
            .and_then(|v| v.into_int_value().into())
            .ok_or_else(|| {
                CompileError::Semantic("Block dim intrinsic returned unexpected type".to_string())
            })
    }

    /// Emit a call to get grid dimension for a dimension
    #[cfg(feature = "llvm")]
    pub fn emit_grid_dim(
        &self,
        builder: &Builder<'static>,
        dim: u8,
    ) -> Result<IntValue<'static>, CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        let intrinsic_name = match dim {
            0 => "llvm.nvvm.read.ptx.sreg.nctaid.x",
            1 => "llvm.nvvm.read.ptx.sreg.nctaid.y",
            2 => "llvm.nvvm.read.ptx.sreg.nctaid.z",
            _ => return Err(CompileError::Semantic("Invalid dimension".to_string())),
        };

        let func = module.get_function(intrinsic_name).ok_or_else(|| {
            CompileError::Semantic(format!("Intrinsic {} not declared", intrinsic_name))
        })?;

        let call = builder.build_call(func, &[], "nctaid").map_err(|e| {
            CompileError::Semantic(format!("Failed to call grid dim intrinsic: {}", e))
        })?;

        call.try_as_basic_value()
            .left()
            .and_then(|v| v.into_int_value().into())
            .ok_or_else(|| {
                CompileError::Semantic("Grid dim intrinsic returned unexpected type".to_string())
            })
    }

    /// Compute global thread ID: blockIdx * blockDim + threadIdx
    #[cfg(feature = "llvm")]
    pub fn emit_global_id(
        &self,
        builder: &Builder<'static>,
        dim: u8,
    ) -> Result<IntValue<'static>, CompileError> {
        let block_id = self.emit_block_id(builder, dim)?;
        let block_dim = self.emit_block_dim(builder, dim)?;
        let thread_id = self.emit_thread_id(builder, dim)?;

        // global_id = block_id * block_dim + thread_id
        let block_offset = builder
            .build_int_mul(block_id, block_dim, "block_offset")
            .map_err(|e| CompileError::Semantic(format!("Failed to build mul: {}", e)))?;
        let global_id = builder
            .build_int_add(block_offset, thread_id, "global_id")
            .map_err(|e| CompileError::Semantic(format!("Failed to build add: {}", e)))?;

        Ok(global_id)
    }

    /// Emit a thread block barrier (__syncthreads)
    #[cfg(feature = "llvm")]
    pub fn emit_barrier(&self, builder: &Builder<'static>) -> Result<(), CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        let func = module
            .get_function("llvm.nvvm.barrier0")
            .ok_or_else(|| CompileError::Semantic("Barrier intrinsic not declared".to_string()))?;

        builder.build_call(func, &[], "").map_err(|e| {
            CompileError::Semantic(format!("Failed to call barrier intrinsic: {}", e))
        })?;

        Ok(())
    }

    /// Emit a memory fence
    #[cfg(feature = "llvm")]
    pub fn emit_mem_fence(
        &self,
        builder: &Builder<'static>,
        scope: crate::mir::GpuMemoryScope,
    ) -> Result<(), CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        let intrinsic_name = match scope {
            crate::mir::GpuMemoryScope::WorkGroup => "llvm.nvvm.membar.cta",
            crate::mir::GpuMemoryScope::Device => "llvm.nvvm.membar.gl",
            crate::mir::GpuMemoryScope::All => "llvm.nvvm.membar.sys",
        };

        let func = module.get_function(intrinsic_name).ok_or_else(|| {
            CompileError::Semantic(format!(
                "Memory fence intrinsic {} not declared",
                intrinsic_name
            ))
        })?;

        builder.build_call(func, &[], "").map_err(|e| {
            CompileError::Semantic(format!("Failed to call memory fence intrinsic: {}", e))
        })?;

        Ok(())
    }

    /// Allocate shared memory (local to thread block)
    #[cfg(feature = "llvm")]
    pub fn emit_shared_alloc(
        &self,
        builder: &Builder<'static>,
        element_type: BasicTypeEnum<'static>,
        size: u32,
    ) -> Result<PointerValue<'static>, CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        // Create array type for shared memory
        let array_type = match element_type {
            BasicTypeEnum::IntType(t) => t.array_type(size),
            BasicTypeEnum::FloatType(t) => t.array_type(size),
            _ => {
                return Err(CompileError::Semantic(
                    "Unsupported shared memory element type".to_string(),
                ))
            }
        };

        // Create global variable in address space 3 (shared memory)
        // NVPTX address spaces: 0=generic, 1=global, 3=shared, 4=constant, 5=local
        let shared_addr_space = AddressSpace::try_from(3u16)
            .map_err(|_| CompileError::Semantic("Invalid address space".to_string()))?;

        // Generate unique name for shared memory
        let name = format!("__shared_mem_{}", self.kernel_functions.borrow().len());
        let global = module.add_global(array_type, Some(shared_addr_space), &name);
        global.set_linkage(inkwell::module::Linkage::Internal);
        global.set_initializer(&array_type.const_zero());

        Ok(global.as_pointer_value())
    }

    /// Get LLVM IR as string
    #[cfg(feature = "llvm")]
    pub fn get_ir(&self) -> Result<String, CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;
        Ok(module.print_to_string().to_string())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn get_ir(&self) -> Result<String, CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }

    /// Emit PTX code from the module
    #[cfg(feature = "llvm")]
    pub fn emit_ptx(&self) -> Result<String, CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        // Initialize NVPTX targets
        inkwell::targets::Target::initialize_all(&InitializationConfig::default());

        // Get target triple
        let triple = TargetTriple::create(&self.get_target_triple());

        // Get target
        let target = LlvmTarget::from_triple(&triple)
            .map_err(|e| CompileError::Semantic(format!("Failed to get NVPTX target: {}", e)))?;

        // Create target machine
        let target_machine = target
            .create_target_machine(
                &triple,
                self.compute_capability.llvm_cpu(),
                "+ptx70", // PTX 7.0 features
                OptimizationLevel::Default,
                RelocMode::Default,
                CodeModel::Default,
            )
            .ok_or_else(|| {
                CompileError::Semantic("Failed to create NVPTX target machine".to_string())
            })?;

        // Emit assembly (PTX)
        let buffer = target_machine
            .write_to_memory_buffer(module, FileType::Assembly)
            .map_err(|e| CompileError::Semantic(format!("Failed to emit PTX: {}", e)))?;

        // Convert to string
        let ptx = std::str::from_utf8(buffer.as_slice())
            .map_err(|e| CompileError::Semantic(format!("Invalid UTF-8 in PTX: {}", e)))?
            .to_string();

        Ok(ptx)
    }

    #[cfg(not(feature = "llvm"))]
    pub fn emit_ptx(&self) -> Result<String, CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }

    /// Verify the module
    #[cfg(feature = "llvm")]
    pub fn verify(&self) -> Result<(), CompileError> {
        let module = self.module.borrow();
        let module = module
            .as_ref()
            .ok_or_else(|| CompileError::Semantic("Module not created".to_string()))?;

        module
            .verify()
            .map_err(|e| CompileError::Semantic(format!("LLVM verification failed: {}", e)))?;
        Ok(())
    }

    #[cfg(not(feature = "llvm"))]
    pub fn verify(&self) -> Result<(), CompileError> {
        Err(CompileError::Semantic(
            "LLVM feature not enabled".to_string(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_compute_capability_cpu_string() {
        assert_eq!(GpuComputeCapability::Sm70.llvm_cpu(), "sm_70");
        assert_eq!(GpuComputeCapability::Sm80.llvm_cpu(), "sm_80");
    }

    #[test]
    fn test_target_triple() {
        let backend = LlvmGpuBackend {
            compute_capability: GpuComputeCapability::default(),
            debug_info: false,
            #[cfg(feature = "llvm")]
            context: Box::leak(Box::new(Context::create())),
            #[cfg(feature = "llvm")]
            module: RefCell::new(None),
            #[cfg(feature = "llvm")]
            builder: RefCell::new(None),
            #[cfg(feature = "llvm")]
            kernel_functions: RefCell::new(Vec::new()),
        };

        assert_eq!(backend.get_target_triple(), "nvptx64-nvidia-cuda");
    }
}

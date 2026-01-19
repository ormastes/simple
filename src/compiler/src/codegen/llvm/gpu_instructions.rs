/// LLVM GPU instruction compilation - GPU intrinsics and operations
use super::LlvmBackend;
use crate::error::CompileError;

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::module::Module;

impl LlvmBackend {
    /// Compile GPU global_id intrinsic - returns global work item ID for dimension
    #[cfg(feature = "llvm")]
    pub(super) fn compile_gpu_global_id(
        &self,
        dim: u8,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();

        // Declare rt_gpu_global_id if not exists
        let gpu_global_id = module.get_function("rt_gpu_global_id").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i32_type.into()], false);
            module.add_function("rt_gpu_global_id", fn_type, None)
        });

        let dim_val = i32_type.const_int(dim as u64, false);
        let call_site = builder
            .build_call(gpu_global_id, &[dim_val.into()], "global_id")
            .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("rt_gpu_global_id returned void".to_string()))
    }

    /// Compile GPU local_id intrinsic - returns local work item ID within workgroup
    #[cfg(feature = "llvm")]
    pub(super) fn compile_gpu_local_id(
        &self,
        dim: u8,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();

        let gpu_local_id = module.get_function("rt_gpu_local_id").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i32_type.into()], false);
            module.add_function("rt_gpu_local_id", fn_type, None)
        });

        let dim_val = i32_type.const_int(dim as u64, false);
        let call_site = builder
            .build_call(gpu_local_id, &[dim_val.into()], "local_id")
            .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("rt_gpu_local_id returned void".to_string()))
    }

    /// Compile GPU group_id intrinsic - returns workgroup ID
    #[cfg(feature = "llvm")]
    pub(super) fn compile_gpu_group_id(
        &self,
        dim: u8,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();

        let gpu_group_id = module.get_function("rt_gpu_group_id").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i32_type.into()], false);
            module.add_function("rt_gpu_group_id", fn_type, None)
        });

        let dim_val = i32_type.const_int(dim as u64, false);
        let call_site = builder
            .build_call(gpu_group_id, &[dim_val.into()], "group_id")
            .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("rt_gpu_group_id returned void".to_string()))
    }

    /// Compile GPU global_size intrinsic - returns total number of work items
    #[cfg(feature = "llvm")]
    pub(super) fn compile_gpu_global_size(
        &self,
        dim: u8,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();

        let gpu_global_size = module.get_function("rt_gpu_global_size").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i32_type.into()], false);
            module.add_function("rt_gpu_global_size", fn_type, None)
        });

        let dim_val = i32_type.const_int(dim as u64, false);
        let call_site = builder
            .build_call(gpu_global_size, &[dim_val.into()], "global_size")
            .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("rt_gpu_global_size returned void".to_string()))
    }

    /// Compile GPU local_size intrinsic - returns workgroup size
    #[cfg(feature = "llvm")]
    pub(super) fn compile_gpu_local_size(
        &self,
        dim: u8,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();

        let gpu_local_size = module.get_function("rt_gpu_local_size").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i32_type.into()], false);
            module.add_function("rt_gpu_local_size", fn_type, None)
        });

        let dim_val = i32_type.const_int(dim as u64, false);
        let call_site = builder
            .build_call(gpu_local_size, &[dim_val.into()], "local_size")
            .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("rt_gpu_local_size returned void".to_string()))
    }

    /// Compile GPU num_groups intrinsic - returns number of workgroups
    #[cfg(feature = "llvm")]
    pub(super) fn compile_gpu_num_groups(
        &self,
        dim: u8,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i32_type = self.context.i32_type();

        let gpu_num_groups = module.get_function("rt_gpu_num_groups").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i32_type.into()], false);
            module.add_function("rt_gpu_num_groups", fn_type, None)
        });

        let dim_val = i32_type.const_int(dim as u64, false);
        let call_site = builder
            .build_call(gpu_num_groups, &[dim_val.into()], "num_groups")
            .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("rt_gpu_num_groups returned void".to_string()))
    }

    /// Compile GPU barrier intrinsic - synchronize all threads in workgroup
    #[cfg(feature = "llvm")]
    pub(super) fn compile_gpu_barrier(
        &self,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let void_type = self.context.void_type();

        let gpu_barrier = module.get_function("rt_gpu_barrier").unwrap_or_else(|| {
            let fn_type = void_type.fn_type(&[], false);
            module.add_function("rt_gpu_barrier", fn_type, None)
        });

        builder
            .build_call(gpu_barrier, &[], "barrier")
            .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?;

        Ok(())
    }

    /// Compile GPU mem_fence intrinsic - memory fence with given scope
    #[cfg(feature = "llvm")]
    pub(super) fn compile_gpu_mem_fence(
        &self,
        scope: crate::mir::GpuMemoryScope,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        use crate::mir::GpuMemoryScope;

        let void_type = self.context.void_type();
        let i32_type = self.context.i32_type();

        let gpu_mem_fence = module.get_function("rt_gpu_mem_fence").unwrap_or_else(|| {
            let fn_type = void_type.fn_type(&[i32_type.into()], false);
            module.add_function("rt_gpu_mem_fence", fn_type, None)
        });

        let scope_val = match scope {
            GpuMemoryScope::WorkGroup => i32_type.const_int(0, false),
            GpuMemoryScope::Device => i32_type.const_int(1, false),
            GpuMemoryScope::All => i32_type.const_int(2, false),
        };

        builder
            .build_call(gpu_mem_fence, &[scope_val.into()], "mem_fence")
            .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?;

        Ok(())
    }

    /// Compile GPU atomic operation
    #[cfg(feature = "llvm")]
    pub(super) fn compile_gpu_atomic(
        &self,
        op: crate::mir::GpuAtomicOp,
        ptr: inkwell::values::BasicValueEnum<'static>,
        value: inkwell::values::BasicValueEnum<'static>,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        use crate::mir::GpuAtomicOp;

        let i64_type = self.context.i64_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

        // Select the appropriate atomic function based on operation
        let func_name = match op {
            GpuAtomicOp::Add => "rt_gpu_atomic_add_i64",
            GpuAtomicOp::Sub => "rt_gpu_atomic_sub_i64",
            GpuAtomicOp::Xchg => "rt_gpu_atomic_xchg_i64",
            GpuAtomicOp::Min => "rt_gpu_atomic_min_i64",
            GpuAtomicOp::Max => "rt_gpu_atomic_max_i64",
            GpuAtomicOp::And => "rt_gpu_atomic_and_i64",
            GpuAtomicOp::Or => "rt_gpu_atomic_or_i64",
            GpuAtomicOp::Xor => "rt_gpu_atomic_xor_i64",
        };

        // All atomics take 2 arguments: ptr, value
        let atomic_fn = module.get_function(func_name).unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i8_ptr_type.into(), i64_type.into()], false);
            module.add_function(func_name, fn_type, None)
        });

        let call_site = builder
            .build_call(atomic_fn, &[ptr.into(), value.into()], "atomic")
            .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("Atomic operation returned void".to_string()))
    }

    /// Compile GPU atomic compare-exchange operation
    #[cfg(feature = "llvm")]
    pub(super) fn compile_gpu_atomic_cmpxchg(
        &self,
        ptr: inkwell::values::BasicValueEnum<'static>,
        expected: inkwell::values::BasicValueEnum<'static>,
        desired: inkwell::values::BasicValueEnum<'static>,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

        // CmpXchg takes 3 arguments: ptr, expected, desired
        let cmpxchg_fn = module.get_function("rt_gpu_atomic_cmpxchg_i64").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i8_ptr_type.into(), i64_type.into(), i64_type.into()], false);
            module.add_function("rt_gpu_atomic_cmpxchg_i64", fn_type, None)
        });

        let call_site = builder
            .build_call(cmpxchg_fn, &[ptr.into(), expected.into(), desired.into()], "cmpxchg")
            .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("CmpXchg operation returned void".to_string()))
    }

    /// Compile GPU shared memory allocation
    #[cfg(feature = "llvm")]
    pub(super) fn compile_gpu_shared_alloc(
        &self,
        size: u32,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        let i64_type = self.context.i64_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

        let gpu_shared_alloc = module.get_function("rt_gpu_shared_alloc").unwrap_or_else(|| {
            let fn_type = i8_ptr_type.fn_type(&[i64_type.into()], false);
            module.add_function("rt_gpu_shared_alloc", fn_type, None)
        });

        let size_val = i64_type.const_int(size as u64, false);
        let call_site = builder
            .build_call(gpu_shared_alloc, &[size_val.into()], "shared_alloc")
            .map_err(|e| crate::error::factory::llvm_build_failed("call", &e))?;

        call_site
            .try_as_basic_value()
            .left()
            .ok_or_else(|| CompileError::Semantic("rt_gpu_shared_alloc returned void".to_string()))
    }
}

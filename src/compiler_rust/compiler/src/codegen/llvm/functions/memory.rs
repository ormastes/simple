use super::{LlvmBackend, VRegMap};
use crate::error::CompileError;

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;

impl LlvmBackend {
    // ============================================================================
    // Memory Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_load(
        &self,
        dest: crate::mir::VReg,
        addr: crate::mir::VReg,
        ty: &crate::hir::TypeId,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let addr_val = self.get_vreg(&addr, vreg_map)?;

        // Coerce address to pointer if needed
        let ptr = match addr_val {
            inkwell::values::BasicValueEnum::PointerValue(p) => p,
            inkwell::values::BasicValueEnum::IntValue(iv) => {
                let ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
                builder
                    .build_int_to_ptr(iv, ptr_type, "load_ptr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?
            }
            _ => {
                let default_val = self.runtime_int_type().const_int(0, false);
                vreg_map.insert(dest, default_val.into());
                return Ok(());
            }
        };

        let loaded = builder
            .build_load(self.llvm_type(ty)?, ptr, "load")
            .map_err(|e| crate::error::factory::llvm_build_failed("load", &e))?;
        vreg_map.insert(dest, loaded);
        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_store(
        &self,
        addr: crate::mir::VReg,
        value: crate::mir::VReg,
        ty: &crate::hir::TypeId,
        vreg_map: &VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let addr_val = self.get_vreg(&addr, vreg_map)?;
        let value_val = self.get_vreg(&value, vreg_map)?;

        // Coerce address to pointer if needed
        let ptr = match addr_val {
            inkwell::values::BasicValueEnum::PointerValue(p) => p,
            inkwell::values::BasicValueEnum::IntValue(iv) => {
                let ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
                builder
                    .build_int_to_ptr(iv, ptr_type, "store_ptr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?
            }
            _ => return Ok(()), // Fallback: no-op
        };

        let stored = self.coerce_value_to_type(value_val, Some(self.llvm_type(ty)?), builder)?;
        builder
            .build_store(ptr, stored)
            .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;
        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_gc_alloc(
        &self,
        dest: crate::mir::VReg,
        ty: &crate::hir::TypeId,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        // Allocate on stack for now (proper GC integration later)
        let llvm_ty = self.llvm_type(ty)?;
        let alloc = builder
            .build_alloca(llvm_ty, "gc_alloc")
            .map_err(|e| crate::error::factory::llvm_build_failed("alloca", &e))?;
        vreg_map.insert(dest, alloc.into());
        Ok(())
    }
}

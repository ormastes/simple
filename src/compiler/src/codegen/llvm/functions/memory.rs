use super::{LlvmBackend, VRegMap};
use crate::error::CompileError;

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;

impl LlvmBackend {
    // ============================================================================
    // Memory Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    fn compile_load(
        &self,
        dest: crate::mir::VReg,
        addr: crate::mir::VReg,
        ty: &crate::hir::TypeId,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let addr_val = self.get_vreg(&addr, vreg_map)?;

        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = addr_val {
            let loaded = builder
                .build_load(self.llvm_type(ty)?, ptr, "load")
                .map_err(|e| crate::error::factory::llvm_build_failed("load", &e))?;
            vreg_map.insert(dest, loaded);
            Ok(())
        } else {
            Err(CompileError::Semantic("Load requires pointer".to_string()))
        }
    }

    #[cfg(feature = "llvm")]
    fn compile_store(
        &self,
        addr: crate::mir::VReg,
        value: crate::mir::VReg,
        _ty: &crate::hir::TypeId,
        vreg_map: &VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let addr_val = self.get_vreg(&addr, vreg_map)?;
        let value_val = self.get_vreg(&value, vreg_map)?;

        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = addr_val {
            builder
                .build_store(ptr, value_val)
                .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;
            Ok(())
        } else {
            Err(CompileError::Semantic("Store requires pointer".to_string()))
        }
    }

    #[cfg(feature = "llvm")]
    fn compile_gc_alloc(
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

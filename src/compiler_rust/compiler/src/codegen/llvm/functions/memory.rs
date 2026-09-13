use super::{LlvmBackend, VRegMap};
use crate::error::CompileError;

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::values::BasicValue;

impl LlvmBackend {
    // ============================================================================
    // Memory Instructions
    // ============================================================================

    /// LLVM type to use for a raw Load/Store of a native local slot.
    ///
    /// `llvm_type()` always returns the tagged RuntimeValue int width (i64 on
    /// 64-bit targets) — correct for the general "everything is a boxed
    /// RuntimeValue" ABI used at call boundaries, but WRONG for a plain
    /// unboxed `f64`/`f32` local: MIR keeps such locals as native floats
    /// (Store/Load with `ty` = F64, boxing only at an explicit `BoxFloat`
    /// right before a value needs to become a RuntimeValue, e.g. for
    /// `print()`). Loading that memory back as i64 reinterprets the double's
    /// raw bits as an integer, so a subsequent `BinOp` picks the INTEGER add
    /// path and sums the two doubles' bit patterns instead of their values.
    ///
    /// Measured before this fix (`zz_sum.spl`, `1.5 + 2.5`, native
    /// `core-c-bootstrap`, `aarch64-apple-darwin`): the loaded `x` came back
    /// as `IntValue(bits(1.5))`, `BinOp::Add` computed
    /// `bits(1.5) + bits(2.5) = 0x7ffc000000000000` (verified byte for byte:
    /// `bits(1.5)=0x3ff8000000000000`, `bits(2.5)=0x4004000000000000`), and
    /// the program printed `NaN`. After returning the true `f64`/`f32` type
    /// here for a Load/Store of that type, `x + 2.5` prints `4` and
    /// `dotp([1.0,2.0],[3.0,4.0])` prints `11`, matching the interpreter.
    #[cfg(feature = "llvm")]
    fn memory_element_type(
        &self,
        ty: &crate::hir::TypeId,
    ) -> Result<inkwell::types::BasicTypeEnum<'static>, CompileError> {
        use crate::hir::TypeId as T;
        match *ty {
            T::F64 => Ok(self.context_ref().f64_type().into()),
            T::F32 => Ok(self.context_ref().f32_type().into()),
            _ => self.llvm_type(ty),
        }
    }

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
                let ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
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
            .build_load(self.memory_element_type(ty)?, ptr, "load")
            .map_err(|e| crate::error::factory::llvm_build_failed("load", &e))?;
        if self.mem_access_is_volatile() {
            // `@volatile` / `@no_reorder` fn: never elided, merged or widened.
            if let Some(inst) = loaded.as_instruction_value() {
                inst.set_volatile(true)
                    .map_err(|e| crate::error::factory::llvm_build_failed("load_volatile", e))?;
            }
        }
        vreg_map.insert(dest, loaded);
        self.emit_no_reorder_fence(builder)?;
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
                let ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
                builder
                    .build_int_to_ptr(iv, ptr_type, "store_ptr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?
            }
            _ => return Ok(()), // Fallback: no-op
        };

        let stored = self.coerce_value_to_type(value_val, Some(self.memory_element_type(ty)?), builder)?;
        let store = builder
            .build_store(ptr, stored)
            .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;
        if self.mem_access_is_volatile() {
            store
                .set_volatile(true)
                .map_err(|e| crate::error::factory::llvm_build_failed("store_volatile", e))?;
        }
        self.emit_no_reorder_fence(builder)?;
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

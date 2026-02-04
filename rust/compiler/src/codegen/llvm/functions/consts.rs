use super::{LlvmBackend, VRegMap};
use crate::error::CompileError;

#[cfg(feature = "llvm")]
use inkwell::module::Module;

impl LlvmBackend {
    // ============================================================================
    // Constant Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_const_int(
        &self,
        dest: crate::mir::VReg,
        value: i64,
        vreg_map: &mut VRegMap,
    ) -> Result<(), CompileError> {
        let const_val = self.context.i64_type().const_int(value as u64, true);
        vreg_map.insert(dest, const_val.into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_const_bool(
        &self,
        dest: crate::mir::VReg,
        value: bool,
        vreg_map: &mut VRegMap,
    ) -> Result<(), CompileError> {
        let const_val = self.context.bool_type().const_int(value as u64, false);
        vreg_map.insert(dest, const_val.into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_const_float(
        &self,
        dest: crate::mir::VReg,
        value: f64,
        vreg_map: &mut VRegMap,
    ) -> Result<(), CompileError> {
        let const_val = self.context.f64_type().const_float(value);
        vreg_map.insert(dest, const_val.into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_const_string(
        &self,
        dest: crate::mir::VReg,
        value: &str,
        vreg_map: &mut VRegMap,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        // Create global string constant
        let str_val = self.context.const_string(value.as_bytes(), false);
        let global = module.add_global(str_val.get_type(), None, "str");
        global.set_initializer(&str_val);
        global.set_constant(true);
        vreg_map.insert(dest, global.as_pointer_value().into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_const_symbol(
        &self,
        dest: crate::mir::VReg,
        value: &str,
        vreg_map: &mut VRegMap,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        // Symbols are represented as interned string pointers
        let str_val = self.context.const_string(value.as_bytes(), false);
        let global = module.add_global(str_val.get_type(), None, &format!("sym_{}", value));
        global.set_initializer(&str_val);
        global.set_constant(true);
        vreg_map.insert(dest, global.as_pointer_value().into());
        Ok(())
    }
}

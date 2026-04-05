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
        let const_val = self.runtime_int_type().const_int(value as u64, true);
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
        // Use i64 to match the runtime's tagged-value ABI (0 = false, 1 = true)
        let const_val = self.runtime_int_type().const_int(value as u64, false);
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
        let i64_type = self.runtime_int_type();

        // Declare rt_string_new if not exists: fn(i64, i64) -> i64
        // First arg is ptr-as-i64 (matching the tagged-value ABI).
        let string_new = module.get_function("rt_string_new").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
            module.add_function("rt_string_new", fn_type, None)
        });

        let builder = self.builder.borrow();
        let builder = builder
            .as_ref()
            .ok_or_else(crate::error::factory::llvm_builder_not_created)?;

        if value.is_empty() {
            let zero = i64_type.const_int(0, false);
            let call = builder
                .build_call(string_new, &[zero.into(), zero.into()], "str_new")
                .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_new", &e))?;
            if let Some(ret) = call.try_as_basic_value().left() {
                vreg_map.insert(dest, ret);
            }
        } else {
            // Create global string constant with private linkage to avoid cross-module collisions
            let str_val = self.context.const_string(value.as_bytes(), false);
            let global = module.add_global(str_val.get_type(), None, "str");
            global.set_initializer(&str_val);
            global.set_constant(true);
            global.set_linkage(inkwell::module::Linkage::Private);
            let str_ptr = global.as_pointer_value();
            // Convert ptr to i64 to match the ABI
            let str_ptr_int = builder
                .build_ptr_to_int(str_ptr, i64_type, "str_ptr_int")
                .map_err(|e| crate::error::factory::llvm_build_failed("ptrtoint", &e))?;
            let str_len = i64_type.const_int(value.len() as u64, false);
            let call = builder
                .build_call(string_new, &[str_ptr_int.into(), str_len.into()], "str_new")
                .map_err(|e| crate::error::factory::llvm_build_failed("rt_string_new", &e))?;
            if let Some(ret) = call.try_as_basic_value().left() {
                vreg_map.insert(dest, ret);
            }
        }
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
        // Symbols are represented as runtime strings (same as const_string)
        self.compile_const_string(dest, value, vreg_map, module)
    }
}

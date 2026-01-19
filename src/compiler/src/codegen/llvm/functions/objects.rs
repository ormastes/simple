use super::{LlvmBackend, VRegMap};
use crate::error::CompileError;

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::module::Module;

impl LlvmBackend {
    // ============================================================================
    // Object Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    fn compile_struct_init(
        &self,
        dest: crate::mir::VReg,
        struct_size: u32,
        field_offsets: &[u32],
        field_types: &[crate::hir::TypeId],
        field_values: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let i8_type = self.context.i8_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
        let array_type = i8_type.array_type(struct_size);
        let alloc = builder
            .build_alloca(array_type, "struct")
            .map_err(|e| crate::error::factory::llvm_build_failed("alloca", &e))?;
        let struct_ptr = builder
            .build_pointer_cast(alloc, i8_ptr_type, "struct_ptr")
            .map_err(|e| crate::error::factory::llvm_cast_failed("cast struct ptr", &e))?;

        for ((offset, field_type), value) in field_offsets.iter().zip(field_types.iter()).zip(field_values.iter()) {
            let field_val = self.get_vreg(value, vreg_map)?;
            let offset_val = self.context.i32_type().const_int(*offset as u64, false);
            let field_ptr = unsafe { builder.build_gep(i8_type, struct_ptr, &[offset_val], "field_ptr") }
                .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;
            let llvm_field_ty = self.llvm_type(field_type)?;
            let typed_ptr = builder
                .build_pointer_cast(
                    field_ptr,
                    self.context.ptr_type(inkwell::AddressSpace::default()),
                    "field_typed_ptr",
                )
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast field ptr", &e))?;
            builder
                .build_store(typed_ptr, field_val)
                .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;
        }

        vreg_map.insert(dest, struct_ptr.into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    fn compile_field_get(
        &self,
        dest: crate::mir::VReg,
        object: crate::mir::VReg,
        byte_offset: u32,
        field_type: &crate::hir::TypeId,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let obj_val = self.get_vreg(&object, vreg_map)?;

        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = obj_val {
            let i8_type = self.context.i8_type();
            let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
            let base_ptr = builder
                .build_pointer_cast(ptr, i8_ptr_type, "struct_ptr")
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast struct ptr", &e))?;
            let offset_val = self.context.i32_type().const_int(byte_offset as u64, false);
            let field_ptr = unsafe { builder.build_gep(i8_type, base_ptr, &[offset_val], "field_ptr") }
                .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;
            let llvm_field_ty = self.llvm_type(field_type)?;
            let typed_ptr = builder
                .build_pointer_cast(
                    field_ptr,
                    self.context.ptr_type(inkwell::AddressSpace::default()),
                    "field_typed_ptr",
                )
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast field ptr", &e))?;
            let loaded = builder
                .build_load(llvm_field_ty, typed_ptr, "field")
                .map_err(|e| crate::error::factory::llvm_build_failed("load", &e))?;

            vreg_map.insert(dest, loaded);
            Ok(())
        } else {
            Err(CompileError::Semantic(
                "FieldGet requires pointer to struct".to_string(),
            ))
        }
    }

    #[cfg(feature = "llvm")]
    fn compile_field_set(
        &self,
        object: crate::mir::VReg,
        byte_offset: u32,
        field_type: &crate::hir::TypeId,
        value: crate::mir::VReg,
        vreg_map: &VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let obj_val = self.get_vreg(&object, vreg_map)?;
        let val = self.get_vreg(&value, vreg_map)?;

        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = obj_val {
            let i8_type = self.context.i8_type();
            let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
            let base_ptr = builder
                .build_pointer_cast(ptr, i8_ptr_type, "struct_ptr")
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast struct ptr", &e))?;
            let offset_val = self.context.i32_type().const_int(byte_offset as u64, false);
            let field_ptr = unsafe { builder.build_gep(i8_type, base_ptr, &[offset_val], "field_ptr") }
                .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;
            let llvm_field_ty = self.llvm_type(field_type)?;
            let typed_ptr = builder
                .build_pointer_cast(
                    field_ptr,
                    self.context.ptr_type(inkwell::AddressSpace::default()),
                    "field_typed_ptr",
                )
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast field ptr", &e))?;
            builder
                .build_store(typed_ptr, val)
                .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;
            Ok(())
        } else {
            Err(CompileError::Semantic(
                "FieldSet requires pointer to struct".to_string(),
            ))
        }
    }

    #[cfg(feature = "llvm")]
    fn compile_closure_create(
        &self,
        dest: crate::mir::VReg,
        func_name: &str,
        closure_size: u32,
        capture_offsets: &[u32],
        capture_types: &[crate::hir::TypeId],
        captures: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let i8_type = self.context.i8_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
        let array_type = i8_type.array_type(closure_size);
        let alloc = builder
            .build_alloca(array_type, "closure")
            .map_err(|e| crate::error::factory::llvm_build_failed("alloca", &e))?;
        let closure_ptr = builder
            .build_pointer_cast(alloc, i8_ptr_type, "closure_ptr")
            .map_err(|e| crate::error::factory::llvm_cast_failed("cast closure ptr", &e))?;

        let func_ptr = module
            .get_function(func_name)
            .map(|f| f.as_global_value().as_pointer_value())
            .unwrap_or_else(|| i8_ptr_type.const_null());
        let func_ptr_cast = builder
            .build_pointer_cast(func_ptr, i8_ptr_type, "fn_ptr_cast")
            .map_err(|e| crate::error::factory::llvm_cast_failed("cast fn ptr", &e))?;
        let fn_slot = builder
            .build_pointer_cast(
                closure_ptr,
                i8_ptr_type.ptr_type(inkwell::AddressSpace::default()),
                "fn_slot",
            )
            .map_err(|e| crate::error::factory::llvm_cast_failed("cast fn slot", &e))?;
        builder
            .build_store(fn_slot, func_ptr_cast)
            .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;

        for ((offset, field_type), value) in capture_offsets.iter().zip(capture_types.iter()).zip(captures.iter()) {
            let capture_val = self.get_vreg(value, vreg_map)?;
            let offset_val = self.context.i32_type().const_int(*offset as u64, false);
            let field_ptr = unsafe { builder.build_gep(i8_type, closure_ptr, &[offset_val], "cap_ptr") }
                .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;
            let llvm_field_ty = self.llvm_type(field_type)?;
            let typed_ptr = builder
                .build_pointer_cast(
                    field_ptr,
                    self.context.ptr_type(inkwell::AddressSpace::default()),
                    "cap_typed_ptr",
                )
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast cap ptr", &e))?;
            builder
                .build_store(typed_ptr, capture_val)
                .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;
        }

        vreg_map.insert(dest, closure_ptr.into());
        Ok(())
    }
}

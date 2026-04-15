use super::{LlvmBackend, VRegMap};
use crate::error::{codes, CompileError, ErrorContext};

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::module::Module;

impl LlvmBackend {
    // ============================================================================
    // Object Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_struct_init(
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
        let i64_type = self.runtime_int_type();

        // Allocate struct on the HEAP via rt_alloc (matching Cranelift behavior).
        // Stack alloca would create dangling pointers when passed cross-module.
        let module_ref = self.module.borrow();
        let module = module_ref.as_ref().unwrap();
        let alloc_fn_type = i8_ptr_type.fn_type(&[i64_type.into()], false);
        let alloc_fn = module
            .get_function("rt_alloc")
            .unwrap_or_else(|| module.add_function("rt_alloc", alloc_fn_type, None));
        let size_val = i64_type.const_int(struct_size as u64, false);
        let alloc_call = builder
            .build_call(alloc_fn, &[size_val.into()], "struct_alloc")
            .map_err(|e| crate::error::factory::llvm_build_failed("rt_alloc call", &e))?;
        let alloc_value = alloc_call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| crate::error::factory::llvm_build_failed("rt_alloc result", &"missing return value"))?;
        let struct_ptr = match alloc_value {
            inkwell::values::BasicValueEnum::PointerValue(ptr) => builder
                .build_pointer_cast(ptr, i8_ptr_type, "alloc_ptr")
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast alloc ptr", &e))?,
            inkwell::values::BasicValueEnum::IntValue(iv) => builder
                .build_int_to_ptr(iv, i8_ptr_type, "alloc_ptr")
                .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?,
            _ => {
                return Err(crate::error::factory::llvm_build_failed(
                    "rt_alloc result",
                    &"unsupported return value kind",
                ))
            }
        };

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

        // Convert struct pointer to i64 (tagged-value ABI)
        let struct_i64 = builder
            .build_ptr_to_int(struct_ptr, self.runtime_int_type(), "struct_i64")
            .map_err(|e| crate::error::factory::llvm_build_failed("ptr_to_int", &e))?;
        vreg_map.insert(dest, struct_i64.into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_field_get(
        &self,
        dest: crate::mir::VReg,
        object: crate::mir::VReg,
        byte_offset: u32,
        field_type: &crate::hir::TypeId,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let obj_val = self.get_vreg(&object, vreg_map)?;

        // Coerce object to pointer: i64 values are inttoptr'd
        let ptr = match obj_val {
            inkwell::values::BasicValueEnum::PointerValue(p) => p,
            inkwell::values::BasicValueEnum::IntValue(iv) => {
                let ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
                builder
                    .build_int_to_ptr(iv, ptr_type, "obj_ptr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?
            }
            _ => {
                // Fallback: insert default value
                let default_val = self.runtime_int_type().const_int(0, false);
                vreg_map.insert(dest, default_val.into());
                return Ok(());
            }
        };

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
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_field_set(
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

        // Coerce object to pointer: i64 values are inttoptr'd
        let ptr = match obj_val {
            inkwell::values::BasicValueEnum::PointerValue(p) => p,
            inkwell::values::BasicValueEnum::IntValue(iv) => {
                let ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
                builder
                    .build_int_to_ptr(iv, ptr_type, "obj_ptr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?
            }
            _ => return Ok(()), // Fallback: no-op
        };

        let i8_type = self.context.i8_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());
        let base_ptr = builder
            .build_pointer_cast(ptr, i8_ptr_type, "struct_ptr")
            .map_err(|e| crate::error::factory::llvm_cast_failed("cast struct ptr", &e))?;
        let offset_val = self.context.i32_type().const_int(byte_offset as u64, false);
        let field_ptr = unsafe { builder.build_gep(i8_type, base_ptr, &[offset_val], "field_ptr") }
            .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;
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
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_closure_create(
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

        // Convert closure pointer to i64 (tagged-value ABI)
        let closure_i64 = builder
            .build_ptr_to_int(closure_ptr, self.runtime_int_type(), "closure_i64")
            .map_err(|e| crate::error::factory::llvm_build_failed("ptr_to_int", &e))?;
        vreg_map.insert(dest, closure_i64.into());
        Ok(())
    }
}

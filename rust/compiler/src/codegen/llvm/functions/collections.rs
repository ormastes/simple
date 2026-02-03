use super::{LlvmBackend, VRegMap};
use crate::error::{codes, CompileError, ErrorContext};

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::types::BasicTypeEnum;

impl LlvmBackend {
    // ============================================================================
    // Collection Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_array_lit(
        &self,
        dest: crate::mir::VReg,
        elements: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        // Create array on stack and initialize elements
        let i64_type = self.context.i64_type();
        let array_type = i64_type.array_type(elements.len() as u32);
        let alloc = builder
            .build_alloca(array_type, "array")
            .map_err(|e| crate::error::factory::llvm_build_failed("alloca", &e))?;

        // Store each element
        for (i, elem) in elements.iter().enumerate() {
            let elem_val = self.get_vreg(elem, vreg_map)?;

            let indices = [
                self.context.i32_type().const_int(0, false),
                self.context.i32_type().const_int(i as u64, false),
            ];
            let gep = unsafe { builder.build_gep(array_type, alloc, &indices, "elem_ptr") }
                .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;

            builder
                .build_store(gep, elem_val)
                .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;
        }

        vreg_map.insert(dest, alloc.into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_tuple_lit(
        &self,
        dest: crate::mir::VReg,
        elements: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        // Tuples are similar to arrays - create struct on stack
        let i64_type = self.context.i64_type();
        let field_types: Vec<BasicTypeEnum> = elements.iter().map(|_| i64_type.into()).collect();
        let struct_type = self.context.struct_type(&field_types, false);
        let alloc = builder
            .build_alloca(struct_type, "tuple")
            .map_err(|e| crate::error::factory::llvm_build_failed("alloca", &e))?;

        // Store each element
        for (i, elem) in elements.iter().enumerate() {
            let elem_val = self.get_vreg(elem, vreg_map)?;

            let gep = builder
                .build_struct_gep(struct_type, alloc, i as u32, "tuple_elem")
                .map_err(|e| crate::error::factory::llvm_build_failed("struct gep", &e))?;

            builder
                .build_store(gep, elem_val)
                .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;
        }

        vreg_map.insert(dest, alloc.into());
        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_dict_lit(
        &self,
        dest: crate::mir::VReg,
        keys: &[crate::mir::VReg],
        values: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        // Dictionaries are represented as a struct with keys array and values array
        let i64_type = self.context.i64_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

        // Declare rt_dict_new if not exists
        let dict_new = module.get_function("rt_dict_new").unwrap_or_else(|| {
            let fn_type = i8_ptr_type.fn_type(&[i64_type.into()], false);
            module.add_function("rt_dict_new", fn_type, None)
        });

        // Declare rt_dict_insert if not exists
        let dict_insert = module.get_function("rt_dict_insert").unwrap_or_else(|| {
            let fn_type = self
                .context
                .void_type()
                .fn_type(&[i8_ptr_type.into(), i64_type.into(), i64_type.into()], false);
            module.add_function("rt_dict_insert", fn_type, None)
        });

        // Create new dict with initial capacity
        let capacity = i64_type.const_int(keys.len() as u64, false);
        let dict_ptr = builder
            .build_call(dict_new, &[capacity.into()], "dict")
            .map_err(|e| crate::error::factory::llvm_build_failed("dict_new call", &e))?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("dict_new should return a pointer value, not void");
                CompileError::semantic_with_context("dict_new returned void instead of pointer".to_string(), ctx)
            })?;

        // Insert each key-value pair
        for (key, value) in keys.iter().zip(values.iter()) {
            let key_val = self.get_vreg(key, vreg_map)?;
            let value_val = self.get_vreg(value, vreg_map)?;

            builder
                .build_call(dict_insert, &[dict_ptr.into(), key_val.into(), value_val.into()], "")
                .map_err(|e| crate::error::factory::llvm_build_failed("dict_insert call", &e))?;
        }

        vreg_map.insert(dest, dict_ptr);
        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_index_get(
        &self,
        dest: crate::mir::VReg,
        collection: crate::mir::VReg,
        index: crate::mir::VReg,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let coll_val = self.get_vreg(&collection, vreg_map)?;
        let idx_val = self.get_vreg(&index, vreg_map)?;

        // Collection should be a pointer to array
        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = coll_val {
            if let inkwell::values::BasicValueEnum::IntValue(idx) = idx_val {
                let i64_type = self.context.i64_type();
                let arr_type = i64_type.array_type(0); // Dynamic size

                let indices = [self.context.i32_type().const_int(0, false), idx];
                let gep = unsafe { builder.build_gep(arr_type, ptr, &indices, "elem_ptr") }
                    .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;

                let loaded = builder
                    .build_load(i64_type, gep, "elem")
                    .map_err(|e| crate::error::factory::llvm_build_failed("load", &e))?;

                vreg_map.insert(dest, loaded);
            }
        }
        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_index_set(
        &self,
        collection: crate::mir::VReg,
        index: crate::mir::VReg,
        value: crate::mir::VReg,
        vreg_map: &VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let coll_val = self.get_vreg(&collection, vreg_map)?;
        let idx_val = self.get_vreg(&index, vreg_map)?;
        let val = self.get_vreg(&value, vreg_map)?;

        // Collection should be a pointer to array
        if let inkwell::values::BasicValueEnum::PointerValue(ptr) = coll_val {
            if let inkwell::values::BasicValueEnum::IntValue(idx) = idx_val {
                let i64_type = self.context.i64_type();
                let arr_type = i64_type.array_type(0);

                let indices = [self.context.i32_type().const_int(0, false), idx];
                let gep = unsafe { builder.build_gep(arr_type, ptr, &indices, "elem_ptr") }
                    .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;

                builder
                    .build_store(gep, val)
                    .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;
            }
        }
        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_slice_op(
        &self,
        dest: crate::mir::VReg,
        collection: crate::mir::VReg,
        start: Option<crate::mir::VReg>,
        end: Option<crate::mir::VReg>,
        step: Option<crate::mir::VReg>,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let i64_type = self.context.i64_type();
        let i8_ptr_type = self.context.ptr_type(inkwell::AddressSpace::default());

        // Declare rt_slice if not exists
        let slice_fn = module.get_function("rt_slice").unwrap_or_else(|| {
            let fn_type = i8_ptr_type.fn_type(
                &[i8_ptr_type.into(), i64_type.into(), i64_type.into(), i64_type.into()],
                false,
            );
            module.add_function("rt_slice", fn_type, None)
        });

        let coll_val = self.get_vreg(&collection, vreg_map)?;

        // Get start index (default to 0 if None)
        let start_val = if let Some(s) = start {
            self.get_vreg(&s, vreg_map)?
        } else {
            inkwell::values::BasicValueEnum::IntValue(i64_type.const_int(0, false))
        };

        // Get end index (default to -1 meaning end of collection)
        let end_val = if let Some(e) = end {
            self.get_vreg(&e, vreg_map)?
        } else {
            inkwell::values::BasicValueEnum::IntValue(i64_type.const_int(i64::MAX as u64, false))
        };

        // Get step (default to 1)
        let step_val = if let Some(s) = step {
            self.get_vreg(&s, vreg_map)?
        } else {
            inkwell::values::BasicValueEnum::IntValue(i64_type.const_int(1, false))
        };

        let call_site = builder
            .build_call(
                slice_fn,
                &[coll_val.into(), start_val.into(), end_val.into(), step_val.into()],
                "slice",
            )
            .map_err(|e| crate::error::factory::llvm_build_failed("slice call", &e))?;

        if let Some(ret_val) = call_site.try_as_basic_value().left() {
            vreg_map.insert(dest, ret_val);
        }

        Ok(())
    }
}

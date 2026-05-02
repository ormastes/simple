use super::{LlvmBackend, VRegMap};
use crate::error::{codes, CompileError, ErrorContext};

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::module::Module;

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
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let i64_type = self.runtime_int_type();

        // Use minimum capacity of 16 for empty arrays to allow push operations
        let capacity = if elements.is_empty() { 16 } else { elements.len() };

        // Call rt_array_new(capacity) to create a proper heap-allocated RuntimeValue array.
        // Runtime functions are pre-declared with correct signatures in compile(),
        // so get_function will find the correct (1-param) declaration.
        let array_new = module.get_function("rt_array_new").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
            module.add_function("rt_array_new", fn_type, None)
        });
        let cap_val = i64_type.const_int(capacity as u64, false);
        let call_site = builder
            .build_call(array_new, &[cap_val.into()], "array_new")
            .map_err(|e| crate::error::factory::llvm_build_failed("rt_array_new", &e))?;
        let collection = call_site
            .try_as_basic_value()
            .left()
            .unwrap_or_else(|| i64_type.const_int(0, false).into());

        // Push each element via rt_array_push(array, element)
        let array_push = module.get_function("rt_array_push").unwrap_or_else(|| {
            let fn_type = self
                .context
                .bool_type()
                .fn_type(&[i64_type.into(), i64_type.into()], false);
            module.add_function("rt_array_push", fn_type, None)
        });
        for elem in elements.iter() {
            let elem_val = self.get_vreg(elem, vreg_map)?;
            let elem_i64 = self.coerce_value_to_type(elem_val, Some(i64_type.into()), builder)?;
            builder
                .build_call(array_push, &[collection.into(), elem_i64.into()], "")
                .map_err(|e| crate::error::factory::llvm_build_failed("rt_array_push", &e))?;
        }

        vreg_map.insert(dest, collection);
        Ok(())
    }

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_tuple_lit(
        &self,
        dest: crate::mir::VReg,
        elements: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let i64_type = self.runtime_int_type();

        // Call rt_tuple_new(size) to create a proper heap-allocated RuntimeValue tuple
        let tuple_new = module.get_function("rt_tuple_new").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
            module.add_function("rt_tuple_new", fn_type, None)
        });
        let size_val = i64_type.const_int(elements.len() as u64, false);
        let call_site = builder
            .build_call(tuple_new, &[size_val.into()], "tuple_new")
            .map_err(|e| crate::error::factory::llvm_build_failed("rt_tuple_new", &e))?;
        let collection = call_site
            .try_as_basic_value()
            .left()
            .unwrap_or_else(|| i64_type.const_int(0, false).into());

        // Set each element via rt_tuple_set(tuple, index, value)
        let tuple_set = module.get_function("rt_tuple_set").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
            module.add_function("rt_tuple_set", fn_type, None)
        });
        for (i, elem) in elements.iter().enumerate() {
            let elem_val = self.get_vreg(elem, vreg_map)?;
            let elem_i64 = self.coerce_value_to_type(elem_val, Some(i64_type.into()), builder)?;
            let idx_val = i64_type.const_int(i as u64, false);
            builder
                .build_call(tuple_set, &[collection.into(), idx_val.into(), elem_i64.into()], "")
                .map_err(|e| crate::error::factory::llvm_build_failed("rt_tuple_set", &e))?;
        }

        vreg_map.insert(dest, collection);
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
        let i64_type = self.runtime_int_type();

        // Declare rt_dict_new if not exists — all i64 to match tagged-value ABI
        let dict_new = module.get_function("rt_dict_new").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
            module.add_function("rt_dict_new", fn_type, None)
        });

        // Declare rt_dict_set if not exists (rt_dict_insert is not in the runtime spec)
        let dict_set = module.get_function("rt_dict_set").unwrap_or_else(|| {
            let fn_type = self
                .context
                .i8_type()
                .fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
            module.add_function("rt_dict_set", fn_type, None)
        });

        // Create new dict with initial capacity
        let capacity = i64_type.const_int(keys.len() as u64, false);
        let dict_val = builder
            .build_call(dict_new, &[capacity.into()], "dict")
            .map_err(|e| crate::error::factory::llvm_build_failed("dict_new call", &e))?
            .try_as_basic_value()
            .left()
            .ok_or_else(|| {
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("dict_new should return a value, not void");
                CompileError::semantic_with_context("dict_new returned void".to_string(), ctx)
            })?;
        let dict_i64 = self.coerce_value_to_type(dict_val, Some(i64_type.into()), builder)?;

        // Insert each key-value pair
        for (key, value) in keys.iter().zip(values.iter()) {
            let key_val = self.get_vreg(key, vreg_map)?;
            let value_val = self.get_vreg(value, vreg_map)?;
            let key_i64 = self.coerce_value_to_type(key_val, Some(i64_type.into()), builder)?;
            let val_i64 = self.coerce_value_to_type(value_val, Some(i64_type.into()), builder)?;

            builder
                .build_call(dict_set, &[dict_i64.into(), key_i64.into(), val_i64.into()], "")
                .map_err(|e| crate::error::factory::llvm_build_failed("dict_set call", &e))?;
        }

        vreg_map.insert(dest, dict_i64.into());
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
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let i64_type = self.runtime_int_type();
        let coll_val = self.get_vreg(&collection, vreg_map)?;
        let idx_val = self.get_vreg(&index, vreg_map)?;

        let coll_i64 = self.coerce_value_to_type(coll_val, Some(i64_type.into()), builder)?;
        let idx_i64 = self.coerce_value_to_type(idx_val, Some(i64_type.into()), builder)?;

        // Call rt_index_get(collection, index) runtime function
        let rt_func = module.get_function("rt_index_get").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
            module.add_function("rt_index_get", fn_type, None)
        });
        let call_site = builder
            .build_call(rt_func, &[coll_i64.into(), idx_i64.into()], "idx_get")
            .map_err(|e| crate::error::factory::llvm_build_failed("rt_index_get", &e))?;

        if let Some(ret_val) = call_site.try_as_basic_value().left() {
            vreg_map.insert(dest, ret_val);
        } else {
            vreg_map.insert(dest, i64_type.const_int(0, false).into());
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
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let i64_type = self.runtime_int_type();
        let coll_val = self.get_vreg(&collection, vreg_map)?;
        let idx_val = self.get_vreg(&index, vreg_map)?;
        let val = self.get_vreg(&value, vreg_map)?;

        let coll_i64 = self.coerce_value_to_type(coll_val, Some(i64_type.into()), builder)?;
        let idx_i64 = self.coerce_value_to_type(idx_val, Some(i64_type.into()), builder)?;
        let val_i64 = self.coerce_value_to_type(val, Some(i64_type.into()), builder)?;

        // Call rt_index_set(collection, index, value) runtime function
        let rt_func = module.get_function("rt_index_set").unwrap_or_else(|| {
            let fn_type = self
                .context
                .bool_type()
                .fn_type(&[i64_type.into(), i64_type.into(), i64_type.into()], false);
            module.add_function("rt_index_set", fn_type, None)
        });
        builder
            .build_call(rt_func, &[coll_i64.into(), idx_i64.into(), val_i64.into()], "")
            .map_err(|e| crate::error::factory::llvm_build_failed("rt_index_set", &e))?;
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
        let i64_type = self.runtime_int_type();

        // Declare rt_slice if not exists — all i64 to match tagged-value ABI
        let slice_fn = module.get_function("rt_slice").unwrap_or_else(|| {
            let fn_type = i64_type.fn_type(
                &[i64_type.into(), i64_type.into(), i64_type.into(), i64_type.into()],
                false,
            );
            module.add_function("rt_slice", fn_type, None)
        });

        let coll_val = self.get_vreg(&collection, vreg_map)?;
        let coll_i64 = self.coerce_value_to_type(coll_val, Some(i64_type.into()), builder)?;

        // Get start index (default to 0 if None)
        let start_i64 = if let Some(s) = start {
            let v = self.get_vreg(&s, vreg_map)?;
            self.coerce_value_to_type(v, Some(i64_type.into()), builder)?
        } else {
            i64_type.const_int(0, false).into()
        };

        // Get end index (default to -1 meaning end of collection)
        let end_i64 = if let Some(e) = end {
            let v = self.get_vreg(&e, vreg_map)?;
            self.coerce_value_to_type(v, Some(i64_type.into()), builder)?
        } else {
            i64_type.const_int(i64::MAX as u64, false).into()
        };

        // Get step (default to 1)
        let step_i64 = if let Some(s) = step {
            let v = self.get_vreg(&s, vreg_map)?;
            self.coerce_value_to_type(v, Some(i64_type.into()), builder)?
        } else {
            i64_type.const_int(1, false).into()
        };

        let call_site = builder
            .build_call(
                slice_fn,
                &[coll_i64.into(), start_i64.into(), end_i64.into(), step_i64.into()],
                "slice",
            )
            .map_err(|e| crate::error::factory::llvm_build_failed("slice call", &e))?;

        if let Some(ret_val) = call_site.try_as_basic_value().left() {
            vreg_map.insert(dest, ret_val);
        } else {
            let default_val = self.runtime_int_type().const_int(0, false);
            vreg_map.insert(dest, default_val.into());
        }

        Ok(())
    }
}

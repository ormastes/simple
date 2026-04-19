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
            let coerced_field_val = self.coerce_value_to_type(field_val, Some(llvm_field_ty), builder)?;
            let typed_ptr = builder
                .build_pointer_cast(
                    field_ptr,
                    self.context.ptr_type(inkwell::AddressSpace::default()),
                    "field_typed_ptr",
                )
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast field ptr", &e))?;
            builder
                .build_store(typed_ptr, coerced_field_val)
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
        let llvm_field_ty = self.llvm_type(field_type)?;
        let coerced_val = self.coerce_value_to_type(val, Some(llvm_field_ty), builder)?;
        let typed_ptr = builder
            .build_pointer_cast(
                field_ptr,
                self.context.ptr_type(inkwell::AddressSpace::default()),
                "field_typed_ptr",
            )
            .map_err(|e| crate::error::factory::llvm_cast_failed("cast field ptr", &e))?;
        builder
            .build_store(typed_ptr, coerced_val)
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
            let coerced_capture_val = self.coerce_value_to_type(capture_val, Some(llvm_field_ty), builder)?;
            let typed_ptr = builder
                .build_pointer_cast(
                    field_ptr,
                    self.context.ptr_type(inkwell::AddressSpace::default()),
                    "cap_typed_ptr",
                )
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast cap ptr", &e))?;
            builder
                .build_store(typed_ptr, coerced_capture_val)
                .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;
        }

        // Convert closure pointer to i64 (tagged-value ABI)
        let closure_i64 = builder
            .build_ptr_to_int(closure_ptr, self.runtime_int_type(), "closure_i64")
            .map_err(|e| crate::error::factory::llvm_build_failed("ptr_to_int", &e))?;
        vreg_map.insert(dest, closure_i64.into());
        Ok(())
    }

    // ============================================================================
    // Enum / Union / Option / Result / Pattern helpers
    // ============================================================================

    /// Compile EnumUnit: create an enum with no payload using rt_enum_new.
    #[cfg(feature = "llvm")]
    pub(super) fn compile_enum_unit(
        &self,
        dest: crate::mir::VReg,
        variant_name: &str,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let i64_t = self.runtime_int_type();
        let i32_t = self.context.i32_type();
        let disc = {
            let mut hasher = DefaultHasher::new();
            variant_name.hash(&mut hasher);
            (hasher.finish() & 0xFFFFFFFF) as u32
        };
        let rt_fn = module.get_function("rt_enum_new").unwrap_or_else(|| {
            let fn_type = i64_t.fn_type(&[i32_t.into(), i32_t.into(), i64_t.into()], false);
            module.add_function("rt_enum_new", fn_type, None)
        });
        let nil_val = i64_t.const_int(3, false);
        let result = builder
            .build_call(
                rt_fn,
                &[i32_t.const_int(0, false).into(), i32_t.const_int(disc as u64, false).into(), nil_val.into()],
                "enum_unit",
            )
            .map_err(|e| CompileError::Semantic(format!("enum unit call: {e}")))?
            .try_as_basic_value()
            .left()
            .unwrap_or_else(|| i64_t.const_int(0, false).into());
        vreg_map.insert(dest, result);
        Ok(())
    }

    /// Compile EnumWith: create an enum with a payload using rt_enum_new.
    #[cfg(feature = "llvm")]
    pub(super) fn compile_enum_with(
        &self,
        dest: crate::mir::VReg,
        variant_name: &str,
        payload: crate::mir::VReg,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let i64_t = self.runtime_int_type();
        let i32_t = self.context.i32_type();
        let disc = {
            let mut hasher = DefaultHasher::new();
            variant_name.hash(&mut hasher);
            (hasher.finish() & 0xFFFFFFFF) as u32
        };
        let rt_fn = module.get_function("rt_enum_new").unwrap_or_else(|| {
            let fn_type = i64_t.fn_type(&[i32_t.into(), i32_t.into(), i64_t.into()], false);
            module.add_function("rt_enum_new", fn_type, None)
        });
        let payload_val = vreg_map.get(&payload).copied().unwrap_or_else(|| i64_t.const_int(3, false).into());
        let payload_val = self.coerce_value_to_type(payload_val, Some(i64_t.into()), builder)?;
        let result = builder
            .build_call(
                rt_fn,
                &[i32_t.const_int(0, false).into(), i32_t.const_int(disc as u64, false).into(), payload_val.into()],
                "enum_with",
            )
            .map_err(|e| CompileError::Semantic(format!("enum with call: {e}")))?
            .try_as_basic_value()
            .left()
            .unwrap_or_else(|| i64_t.const_int(0, false).into());
        vreg_map.insert(dest, result);
        Ok(())
    }

    /// Compile UnionWrap: wrap a value in a union using rt_enum_new.
    #[cfg(feature = "llvm")]
    pub(super) fn compile_union_wrap(
        &self,
        dest: crate::mir::VReg,
        value: crate::mir::VReg,
        type_index: u32,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let i64_t = self.runtime_int_type();
        let i32_t = self.context.i32_type();
        let rt_fn = module.get_function("rt_enum_new").unwrap_or_else(|| {
            let fn_type = i64_t.fn_type(&[i32_t.into(), i32_t.into(), i64_t.into()], false);
            module.add_function("rt_enum_new", fn_type, None)
        });
        let val = vreg_map.get(&value).copied().unwrap_or_else(|| i64_t.const_int(3, false).into());
        let result = builder
            .build_call(
                rt_fn,
                &[i32_t.const_int(type_index as u64, false).into(), i32_t.const_int(0, false).into(), val.into()],
                "union_wrap",
            )
            .map_err(|e| CompileError::Semantic(format!("union wrap call: {e}")))?
            .try_as_basic_value()
            .left()
            .unwrap_or_else(|| i64_t.const_int(0, false).into());
        vreg_map.insert(dest, result);
        Ok(())
    }

    /// Compile OptionSome / ResultOk / ResultErr using rt_enum_new with named variant.
    #[cfg(feature = "llvm")]
    pub(super) fn compile_tagged_enum_value(
        &self,
        dest: crate::mir::VReg,
        enum_id: u32,
        variant_name: &str,
        value: crate::mir::VReg,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
        call_label: &str,
    ) -> Result<(), CompileError> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let i64_t = self.runtime_int_type();
        let i32_t = self.context.i32_type();
        let disc = {
            let mut h = DefaultHasher::new();
            variant_name.hash(&mut h);
            (h.finish() & 0xFFFFFFFF) as u32
        };
        let rt_fn = module.get_function("rt_enum_new").unwrap_or_else(|| {
            let fn_type = i64_t.fn_type(&[i32_t.into(), i32_t.into(), i64_t.into()], false);
            module.add_function("rt_enum_new", fn_type, None)
        });
        let val = self.get_vreg(&value, vreg_map)?;
        let val = self.coerce_value_to_type(val, Some(i64_t.into()), builder)?;
        let result = builder
            .build_call(
                rt_fn,
                &[i32_t.const_int(enum_id as u64, false).into(), i32_t.const_int(disc as u64, false).into(), val.into()],
                call_label,
            )
            .map_err(|e| CompileError::Semantic(format!("{call_label} call: {e}")))?
            .try_as_basic_value()
            .left()
            .unwrap_or_else(|| i64_t.const_int(0, false).into());
        vreg_map.insert(dest, result);
        Ok(())
    }

    /// Compile OptionNone: enum with nil payload.
    #[cfg(feature = "llvm")]
    pub(super) fn compile_option_none(
        &self,
        dest: crate::mir::VReg,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};
        let i64_t = self.runtime_int_type();
        let i32_t = self.context.i32_type();
        let disc = {
            let mut h = DefaultHasher::new();
            "None".hash(&mut h);
            (h.finish() & 0xFFFFFFFF) as u32
        };
        let rt_fn = module.get_function("rt_enum_new").unwrap_or_else(|| {
            let fn_type = i64_t.fn_type(&[i32_t.into(), i32_t.into(), i64_t.into()], false);
            module.add_function("rt_enum_new", fn_type, None)
        });
        let nil_val = i64_t.const_int(3, false);
        let result = builder
            .build_call(
                rt_fn,
                &[i32_t.const_int(1, false).into(), i32_t.const_int(disc as u64, false).into(), nil_val.into()],
                "opt_none",
            )
            .map_err(|e| CompileError::Semantic(format!("option none: {e}")))?
            .try_as_basic_value()
            .left()
            .unwrap_or_else(|| i64_t.const_int(0, false).into());
        vreg_map.insert(dest, result);
        Ok(())
    }

    /// Compile PatternTest: test subject against a MirPattern.
    #[cfg(feature = "llvm")]
    pub(super) fn compile_pattern_test(
        &self,
        dest: crate::mir::VReg,
        subject: &crate::mir::VReg,
        pattern: &crate::mir::MirPattern,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let i64_type = self.runtime_int_type();
        let subject_val = self.get_vreg_val(subject, vreg_map, i64_type);
        let result = match pattern {
            crate::mir::MirPattern::Wildcard | crate::mir::MirPattern::Binding(_) => {
                i64_type.const_int(1, false)
            }
            crate::mir::MirPattern::Literal(lit) => match lit {
                crate::mir::MirLiteral::Int(n) => {
                    let lit_val = i64_type.const_int(*n as u64, false);
                    let cmp = builder
                        .build_int_compare(inkwell::IntPredicate::EQ, subject_val.into_int_value(), lit_val, "pat_int_eq")
                        .map_err(|e| format!("pattern icmp: {e}"))?;
                    builder.build_int_z_extend(cmp, i64_type, "pat_ext").map_err(|e| format!("pattern zext: {e}"))?
                }
                crate::mir::MirLiteral::Bool(b) => {
                    let lit_val = i64_type.const_int(if *b { 1 } else { 0 }, false);
                    let cmp = builder
                        .build_int_compare(inkwell::IntPredicate::EQ, subject_val.into_int_value(), lit_val, "pat_bool_eq")
                        .map_err(|e| format!("pattern icmp: {e}"))?;
                    builder.build_int_z_extend(cmp, i64_type, "pat_ext").map_err(|e| format!("pattern zext: {e}"))?
                }
                crate::mir::MirLiteral::Nil => {
                    let nil_val = i64_type.const_int(3, false);
                    let cmp = builder
                        .build_int_compare(inkwell::IntPredicate::EQ, subject_val.into_int_value(), nil_val, "pat_nil_eq")
                        .map_err(|e| format!("pattern icmp: {e}"))?;
                    builder.build_int_z_extend(cmp, i64_type, "pat_ext").map_err(|e| format!("pattern zext: {e}"))?
                }
                crate::mir::MirLiteral::String(s) => {
                    let bytes = s.as_bytes();
                    let global_val = self.context.const_string(bytes, false);
                    let global = module.add_global(global_val.get_type(), None, "pat_str_const");
                    global.set_initializer(&global_val);
                    global.set_constant(true);
                    let str_ptr = builder
                        .build_pointer_cast(global.as_pointer_value(), self.context.ptr_type(inkwell::AddressSpace::default()), "str_ptr")
                        .map_err(|e| format!("pattern str ptr: {e}"))?;
                    let str_ptr_int = builder.build_ptr_to_int(str_ptr, i64_type, "str_ptr_int").map_err(|e| format!("pattern ptrtoint: {e}"))?;
                    let str_len = i64_type.const_int(bytes.len() as u64, false);
                    let rt_string_new = module.get_function("rt_string_new").unwrap_or_else(|| {
                        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
                        module.add_function("rt_string_new", fn_type, None)
                    });
                    let lit_str = builder
                        .build_call(rt_string_new, &[str_ptr_int.into(), str_len.into()], "lit_str")
                        .map_err(|e| format!("pattern string_new: {e}"))?
                        .try_as_basic_value().left().unwrap_or_else(|| i64_type.const_int(0, false).into());
                    let rt_string_eq = module.get_function("rt_string_eq").unwrap_or_else(|| {
                        let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
                        module.add_function("rt_string_eq", fn_type, None)
                    });
                    builder
                        .build_call(rt_string_eq, &[subject_val.into(), lit_str.into()], "pat_str_eq")
                        .map_err(|e| format!("pattern string_eq: {e}"))?
                        .try_as_basic_value().left().unwrap_or_else(|| i64_type.const_int(0, false).into())
                        .into_int_value()
                }
                crate::mir::MirLiteral::Float(f) => {
                    let lit_bits = f.to_bits() as u64;
                    let lit_val = i64_type.const_int(lit_bits, false);
                    let cmp = builder
                        .build_int_compare(inkwell::IntPredicate::EQ, subject_val.into_int_value(), lit_val, "pat_float_eq")
                        .map_err(|e| format!("pattern icmp: {e}"))?;
                    builder.build_int_z_extend(cmp, i64_type, "pat_ext").map_err(|e| format!("pattern zext: {e}"))?
                }
            },
            crate::mir::MirPattern::Variant { variant_name, .. } => {
                use std::collections::hash_map::DefaultHasher;
                use std::hash::{Hash, Hasher};
                let rt_enum_disc = module.get_function("rt_enum_discriminant").unwrap_or_else(|| {
                    let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                    module.add_function("rt_enum_discriminant", fn_type, None)
                });
                let disc = builder
                    .build_call(rt_enum_disc, &[subject_val.into()], "disc")
                    .map_err(|e| format!("pattern disc: {e}"))?
                    .try_as_basic_value().left().unwrap_or_else(|| i64_type.const_int(0, false).into())
                    .into_int_value();
                let expected = {
                    let mut hasher = DefaultHasher::new();
                    variant_name.hash(&mut hasher);
                    (hasher.finish() & 0xFFFFFFFF) as u64
                };
                let expected_val = i64_type.const_int(expected, false);
                let cmp = builder
                    .build_int_compare(inkwell::IntPredicate::EQ, disc, expected_val, "pat_var_eq")
                    .map_err(|e| format!("pattern var icmp: {e}"))?;
                builder.build_int_z_extend(cmp, i64_type, "pat_ext").map_err(|e| format!("pattern zext: {e}"))?
            }
            _ => i64_type.const_int(1, false),
        };
        vreg_map.insert(dest, result.into());
        Ok(())
    }

    /// Compile PatternBind: extract a value by following binding path steps.
    #[cfg(feature = "llvm")]
    pub(super) fn compile_pattern_bind(
        &self,
        dest: crate::mir::VReg,
        subject: &crate::mir::VReg,
        binding: &crate::mir::PatternBinding,
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<(), CompileError> {
        let i64_type = self.runtime_int_type();
        let subject_val = self.get_vreg_val(subject, vreg_map, i64_type);
        let result = if binding.path.is_empty() {
            subject_val
        } else {
            let mut current = subject_val;
            for step in &binding.path {
                match step {
                    crate::mir::BindingStep::EnumPayload => {
                        let rt_fn = module.get_function("rt_enum_payload").unwrap_or_else(|| {
                            let fn_type = i64_type.fn_type(&[i64_type.into()], false);
                            module.add_function("rt_enum_payload", fn_type, None)
                        });
                        current = builder
                            .build_call(rt_fn, &[current.into()], "payload")
                            .map_err(|e| format!("pattern bind payload: {e}"))?
                            .try_as_basic_value().left().unwrap_or_else(|| i64_type.const_int(0, false).into());
                    }
                    crate::mir::BindingStep::TupleIndex(idx) => {
                        let rt_fn = module.get_function("rt_tuple_get").unwrap_or_else(|| {
                            let fn_type = i64_type.fn_type(&[i64_type.into(), i64_type.into()], false);
                            module.add_function("rt_tuple_get", fn_type, None)
                        });
                        let idx_val = i64_type.const_int(*idx as u64, false);
                        current = builder
                            .build_call(rt_fn, &[current.into(), idx_val.into()], "tuple_el")
                            .map_err(|e| format!("pattern bind tuple: {e}"))?
                            .try_as_basic_value().left().unwrap_or_else(|| i64_type.const_int(0, false).into());
                    }
                    crate::mir::BindingStep::FieldName(_) => {}
                }
            }
            current
        };
        vreg_map.insert(dest, result);
        Ok(())
    }
}

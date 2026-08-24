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
        vtable_symbol: Option<&str>,
        field_offsets: &[u32],
        field_types: &[crate::hir::TypeId],
        field_values: &[crate::mir::VReg],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let i8_type = self.context_ref().i8_type();
        let i8_ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
        let i64_type = self.runtime_int_type();

        // Allocate struct on the HEAP via rt_alloc (matching Cranelift behavior).
        // Stack alloca would create dangling pointers when passed cross-module.
        let module_ref = self.module.borrow();
        let module = module_ref.as_ref().unwrap();
        let alloc_fn_type = i8_ptr_type.fn_type(&[i64_type.into()], false);
        let alloc_fn = module
            .get_function("rt_alloc")
            .unwrap_or_else(|| module.add_function("rt_alloc", alloc_fn_type, None));
        let header_size = u64::from(vtable_symbol.is_some()) * 8;
        let size_val = i64_type.const_int(struct_size as u64 + header_size, false);
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

        if let Some(symbol) = vtable_symbol {
            let vtable = module.get_global(symbol).unwrap_or_else(|| {
                let array_type = i8_ptr_type.array_type(1);
                let global = module.add_global(array_type, None, symbol);
                global.set_linkage(inkwell::module::Linkage::External);
                global
            });
            builder
                .build_store(struct_ptr, vtable.as_pointer_value())
                .map_err(|e| crate::error::factory::llvm_build_failed("store vtable", &e))?;
        }

        for ((offset, field_type), value) in field_offsets.iter().zip(field_types.iter()).zip(field_values.iter()) {
            let field_val = self.get_vreg(value, vreg_map)?;
            let offset_val = self
                .context_ref()
                .i32_type()
                .const_int(*offset as u64 + header_size, false);
            let field_ptr = unsafe { builder.build_gep(i8_type, struct_ptr, &[offset_val], "field_ptr") }
                .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;
            let llvm_field_ty = self.llvm_type(field_type)?;
            let coerced_field_val = self.coerce_value_to_type(field_val, Some(llvm_field_ty), builder)?;
            let typed_ptr = builder
                .build_pointer_cast(
                    field_ptr,
                    self.context_ref().ptr_type(inkwell::AddressSpace::default()),
                    "field_typed_ptr",
                )
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast field ptr", &e))?;
            builder
                .build_store(typed_ptr, coerced_field_val)
                .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;
        }

        // Native structs still use the flat rt_alloc layout for direct field
        // access, but once they cross into generic RuntimeValue containers
        // they must carry the heap tag bit so arrays/channels do not reinterpret
        // the pointer as an integer payload.
        let struct_i64 = builder
            .build_ptr_to_int(struct_ptr, self.runtime_int_type(), "struct_i64")
            .map_err(|e| crate::error::factory::llvm_build_failed("ptr_to_int", &e))?;
        let tagged_struct = builder
            .build_or(struct_i64, i64_type.const_int(1, false), "struct_tagged")
            .map_err(|e| crate::error::factory::llvm_build_failed("or struct tag", &e))?;
        vreg_map.insert(dest, tagged_struct.into());
        Ok(())
    }

    /// Lane F1 / S5 — duplicate an aggregate's storage (see
    /// `MirInst::AggregateCopy`). Mirrors the Cranelift lowering in
    /// `codegen/instr/closures_structs.rs`, over the same tagged-pointer ABI
    /// that `compile_struct_init` above produces, including the branch-free
    /// null guard.
    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_aggregate_copy(
        &self,
        dest: crate::mir::VReg,
        src: crate::mir::VReg,
        byte_size: u32,
        deep_fields: &[crate::mir::AggregateFieldCopy],
        vreg_map: &mut VRegMap,
        builder: &Builder<'static>,
    ) -> Result<(), CompileError> {
        let src_val = self.get_vreg(&src, vreg_map)?;
        let inkwell::values::BasicValueEnum::IntValue(src_tagged) = src_val else {
            // Not the tagged-i64 aggregate ABI: alias rather than fabricate a
            // copy of an unknown layout.
            vreg_map.insert(dest, src_val);
            return Ok(());
        };

        let tagged = self.emit_aggregate_block_copy(src_tagged, byte_size, deep_fields, builder)?;
        vreg_map.insert(dest, tagged.into());
        Ok(())
    }

    /// Recursive worker for `compile_aggregate_copy`: copy one aggregate
    /// block, then deep-copy the field slots the static descriptor names
    /// (nested declared value types only — see `MirInst::AggregateCopy`).
    /// Recursion is bounded by the descriptor tree built at lowering with a
    /// cycle guard, so termination is unconditional. Branch-free: a slot not
    /// holding a live tagged heap handle keeps its original word via select.
    #[cfg(feature = "llvm")]
    fn emit_aggregate_block_copy(
        &self,
        src_tagged: inkwell::values::IntValue<'static>,
        byte_size: u32,
        deep_fields: &[crate::mir::AggregateFieldCopy],
        builder: &Builder<'static>,
    ) -> Result<inkwell::values::IntValue<'static>, CompileError> {
        let i8_type = self.context_ref().i8_type();
        let i8_ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
        let i64_type = self.runtime_int_type();

        let words = byte_size.div_ceil(8).max(1);
        let alloc_bytes = u64::from(words) * 8;

        let module_ref = self.module.borrow();
        let module = module_ref.as_ref().unwrap();
        let alloc_fn_type = i8_ptr_type.fn_type(&[i64_type.into()], false);
        let alloc_fn = module
            .get_function("rt_alloc")
            .unwrap_or_else(|| module.add_function("rt_alloc", alloc_fn_type, None));
        let size_val = i64_type.const_int(alloc_bytes, false);
        let alloc_call = builder
            .build_call(alloc_fn, &[size_val.into()], "aggcopy_alloc")
            .map_err(|e| crate::error::factory::llvm_build_failed("rt_alloc call", &e))?;
        let alloc_value = alloc_call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| crate::error::factory::llvm_build_failed("rt_alloc result", &"missing return value"))?;
        let new_ptr =
            match alloc_value {
                inkwell::values::BasicValueEnum::PointerValue(ptr) => builder
                    .build_pointer_cast(ptr, i8_ptr_type, "aggcopy_ptr")
                    .map_err(|e| crate::error::factory::llvm_cast_failed("cast alloc ptr", &e))?,
                inkwell::values::BasicValueEnum::IntValue(iv) => builder
                    .build_int_to_ptr(iv, i8_ptr_type, "aggcopy_ptr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?,
                _ => {
                    return Err(crate::error::factory::llvm_build_failed(
                        "rt_alloc result",
                        &"unsupported return value kind",
                    ))
                }
            };
        let new_i64 = builder
            .build_ptr_to_int(new_ptr, i64_type, "aggcopy_new_i64")
            .map_err(|e| crate::error::factory::llvm_build_failed("ptr_to_int", &e))?;

        // Untag, then branch-free null guard: a nil aggregate would fault.
        let tag_mask = i64_type.const_int(7, false);
        let untag_mask = i64_type.const_int(u64::MAX - 7, false);
        let src_ptr_i64 = builder
            .build_and(src_tagged, untag_mask, "aggcopy_src_untag")
            .map_err(|e| crate::error::factory::llvm_build_failed("and untag", &e))?;
        let one = i64_type.const_int(1, false);
        let src_tag = builder
            .build_and(src_tagged, tag_mask, "aggcopy_src_tag")
            .map_err(|e| crate::error::factory::llvm_build_failed("and tag", &e))?;
        let src_is_heap = builder
            .build_int_compare(inkwell::IntPredicate::EQ, src_tag, one, "aggcopy_src_heap")
            .map_err(|e| crate::error::factory::llvm_build_failed("icmp heap", &e))?;
        let src_nonnull = builder
            .build_int_compare(
                inkwell::IntPredicate::NE,
                src_ptr_i64,
                i64_type.const_zero(),
                "aggcopy_src_nonnull",
            )
            .map_err(|e| crate::error::factory::llvm_build_failed("icmp nonnull", &e))?;
        let src_is_valid = builder
            .build_and(src_is_heap, src_nonnull, "aggcopy_src_valid")
            .map_err(|e| crate::error::factory::llvm_build_failed("and valid", &e))?;
        let load_i64 = builder
            .build_select(src_is_valid, src_ptr_i64, new_i64, "aggcopy_load_src")
            .map_err(|e| crate::error::factory::llvm_build_failed("select", &e))?
            .into_int_value();
        let load_ptr = builder
            .build_int_to_ptr(load_i64, i8_ptr_type, "aggcopy_load_ptr")
            .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr src", &e))?;

        for w in 0..words {
            let off = self.context_ref().i32_type().const_int(u64::from(w) * 8, false);
            let from = unsafe { builder.build_gep(i8_type, load_ptr, &[off], "aggcopy_from") }
                .map_err(|e| crate::error::factory::llvm_build_failed("gep src", &e))?;
            let to = unsafe { builder.build_gep(i8_type, new_ptr, &[off], "aggcopy_to") }
                .map_err(|e| crate::error::factory::llvm_build_failed("gep dst", &e))?;
            let word = builder
                .build_load(i64_type, from, "aggcopy_word")
                .map_err(|e| crate::error::factory::llvm_build_failed("load word", &e))?;
            let word = builder
                .build_select(src_is_valid, word, i64_type.const_zero().into(), "aggcopy_word_guarded")
                .map_err(|e| crate::error::factory::llvm_build_failed("select word", &e))?;
            builder
                .build_store(to, word)
                .map_err(|e| crate::error::factory::llvm_build_failed("store word", &e))?;
        }

        let words_total = words;
        for field in deep_fields {
            if field.word_index >= words_total {
                continue; // descriptor out of range — fail closed, keep shallow
            }
            let off = self
                .context_ref()
                .i32_type()
                .const_int(u64::from(field.word_index) * 8, false);
            let slot = unsafe { builder.build_gep(i8_type, new_ptr, &[off], "aggcopy_deep_slot") }
                .map_err(|e| crate::error::factory::llvm_build_failed("gep deep slot", &e))?;
            let word = builder
                .build_load(i64_type, slot, "aggcopy_deep_word")
                .map_err(|e| crate::error::factory::llvm_build_failed("load deep word", &e))?
                .into_int_value();
            let inner = self.emit_aggregate_block_copy(word, field.byte_size, &field.nested, builder)?;
            // Replace only a live tagged heap handle; nil (0) and non-handle
            // words keep their original value.
            let tag_bit = builder
                .build_and(word, tag_mask, "aggcopy_deep_tag")
                .map_err(|e| crate::error::factory::llvm_build_failed("and tag bit", &e))?;
            let is_tagged = builder
                .build_int_compare(inkwell::IntPredicate::EQ, tag_bit, one, "aggcopy_deep_istag")
                .map_err(|e| crate::error::factory::llvm_build_failed("icmp tag", &e))?;
            let payload = builder
                .build_and(word, untag_mask, "aggcopy_deep_payload")
                .map_err(|e| crate::error::factory::llvm_build_failed("and payload", &e))?;
            let nonnull = builder
                .build_int_compare(
                    inkwell::IntPredicate::NE,
                    payload,
                    i64_type.const_zero(),
                    "aggcopy_deep_nonnull",
                )
                .map_err(|e| crate::error::factory::llvm_build_failed("icmp nonnull", &e))?;
            let is_handle = builder
                .build_and(is_tagged, nonnull, "aggcopy_deep_ishandle")
                .map_err(|e| crate::error::factory::llvm_build_failed("and handle", &e))?;
            let result = builder
                .build_select(is_handle, inner, word, "aggcopy_deep_result")
                .map_err(|e| crate::error::factory::llvm_build_failed("select deep", &e))?;
            builder
                .build_store(slot, result)
                .map_err(|e| crate::error::factory::llvm_build_failed("store deep", &e))?;
        }

        let tagged = builder
            .build_or(new_i64, i64_type.const_int(1, false), "aggcopy_tagged")
            .map_err(|e| crate::error::factory::llvm_build_failed("or tag", &e))?;
        Ok(tagged)
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
                let masked = builder
                    .build_and(iv, self.runtime_int_type().const_int(!0x7u64, false), "obj_ptr_bits")
                    .map_err(|e| crate::error::factory::llvm_build_failed("mask heap tag", &e))?;
                let ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
                builder
                    .build_int_to_ptr(masked, ptr_type, "obj_ptr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?
            }
            _ => {
                // Fallback: insert default value
                let default_val = self.runtime_int_type().const_int(0, false);
                vreg_map.insert(dest, default_val.into());
                return Ok(());
            }
        };

        let i8_type = self.context_ref().i8_type();
        let i8_ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
        let base_ptr = builder
            .build_pointer_cast(ptr, i8_ptr_type, "struct_ptr")
            .map_err(|e| crate::error::factory::llvm_cast_failed("cast struct ptr", &e))?;
        let offset_val = self.context_ref().i32_type().const_int(byte_offset as u64, false);
        let field_ptr = unsafe { builder.build_gep(i8_type, base_ptr, &[offset_val], "field_ptr") }
            .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;
        // `llvm_type()` always returns the tagged-value integer type (by
        // design, for the generic tagged-value ABI — see its doc comment),
        // which for an f64/f32 field would load the field's raw IEEE-754
        // bit pattern as an untagged IntValue instead of a FloatValue. That
        // loses the float-ness at the load site, so any later consumer
        // (e.g. FStringFormat's `val.is_float_value()` check) can no longer
        // recover it and prints the bit pattern as an integer. Struct
        // fields are stored packed by their *actual* declared type (see
        // llvm_type_mapper / CTypeMapper), so float-typed fields must be
        // loaded with the real float LLVM type, not the tagged-int type.
        use crate::hir::TypeId as HirTypeId;
        let llvm_field_ty: inkwell::types::BasicTypeEnum<'static> = match *field_type {
            HirTypeId::F64 => self.context_ref().f64_type().into(),
            HirTypeId::F32 => self.context_ref().f32_type().into(),
            _ => self.llvm_type(field_type)?,
        };
        let typed_ptr = builder
            .build_pointer_cast(
                field_ptr,
                self.context_ref().ptr_type(inkwell::AddressSpace::default()),
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
                let masked = builder
                    .build_and(iv, self.runtime_int_type().const_int(!0x7u64, false), "obj_ptr_bits")
                    .map_err(|e| crate::error::factory::llvm_build_failed("mask heap tag", &e))?;
                let ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
                builder
                    .build_int_to_ptr(masked, ptr_type, "obj_ptr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?
            }
            _ => return Ok(()), // Fallback: no-op
        };

        let i8_type = self.context_ref().i8_type();
        let i8_ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
        let base_ptr = builder
            .build_pointer_cast(ptr, i8_ptr_type, "struct_ptr")
            .map_err(|e| crate::error::factory::llvm_cast_failed("cast struct ptr", &e))?;
        let offset_val = self.context_ref().i32_type().const_int(byte_offset as u64, false);
        let field_ptr = unsafe { builder.build_gep(i8_type, base_ptr, &[offset_val], "field_ptr") }
            .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;
        let llvm_field_ty = self.llvm_type(field_type)?;
        let coerced_val = self.coerce_value_to_type(val, Some(llvm_field_ty), builder)?;
        let typed_ptr = builder
            .build_pointer_cast(
                field_ptr,
                self.context_ref().ptr_type(inkwell::AddressSpace::default()),
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
        let i8_type = self.context_ref().i8_type();
        let i8_ptr_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
        // Closures can escape the creating stack frame through runtime pool and
        // thread APIs. Allocate them on the runtime heap so captured values stay
        // stable after the loop iteration or function call that created them.
        let i64_type = self.runtime_int_type();
        let alloc_fn_type = i8_ptr_type.fn_type(&[i64_type.into()], false);
        let alloc_fn = module
            .get_function("rt_alloc")
            .unwrap_or_else(|| module.add_function("rt_alloc", alloc_fn_type, None));
        let allocation_size = closure_size.max(16);
        let size_val = i64_type.const_int(allocation_size as u64, false);
        let alloc_call = builder
            .build_call(alloc_fn, &[size_val.into()], "closure_alloc")
            .map_err(|e| crate::error::factory::llvm_build_failed("rt_alloc call", &e))?;
        let alloc_value = alloc_call
            .try_as_basic_value()
            .left()
            .ok_or_else(|| crate::error::factory::llvm_build_failed("rt_alloc result", &"missing return value"))?;
        let closure_ptr =
            match alloc_value {
                inkwell::values::BasicValueEnum::PointerValue(ptr) => builder
                    .build_pointer_cast(ptr, i8_ptr_type, "closure_ptr")
                    .map_err(|e| crate::error::factory::llvm_cast_failed("cast closure ptr", &e))?,
                inkwell::values::BasicValueEnum::IntValue(iv) => builder
                    .build_int_to_ptr(iv, i8_ptr_type, "closure_ptr")
                    .map_err(|e| crate::error::factory::llvm_build_failed("int_to_ptr", &e))?,
                _ => {
                    return Err(crate::error::factory::llvm_build_failed(
                        "rt_alloc result",
                        &"unsupported return value kind",
                    ))
                }
            };

        let func_ptr = module
            .get_function(func_name)
            .map(|f| f.as_global_value().as_pointer_value())
            .unwrap_or_else(|| i8_ptr_type.const_null());
        let func_ptr_cast = builder
            .build_pointer_cast(func_ptr, i8_ptr_type, "fn_ptr_cast")
            .map_err(|e| crate::error::factory::llvm_cast_failed("cast fn ptr", &e))?;
        let ptr_slot_type = self.context_ref().ptr_type(inkwell::AddressSpace::default());
        let fn_slot = builder
            .build_pointer_cast(closure_ptr, ptr_slot_type, "fn_slot")
            .map_err(|e| crate::error::factory::llvm_cast_failed("cast fn slot", &e))?;
        builder
            .build_store(fn_slot, func_ptr_cast)
            .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;

        if closure_size < 16 {
            let offset_val = self.context_ref().i32_type().const_int(8, false);
            let marker_ptr = unsafe { builder.build_gep(i8_type, closure_ptr, &[offset_val], "closure_marker_ptr") }
                .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;
            let marker_slot = builder
                .build_pointer_cast(
                    marker_ptr,
                    self.context_ref().ptr_type(inkwell::AddressSpace::default()),
                    "closure_marker_slot",
                )
                .map_err(|e| crate::error::factory::llvm_cast_failed("cast marker ptr", &e))?;
            builder
                .build_store(marker_slot, i64_type.const_zero())
                .map_err(|e| crate::error::factory::llvm_build_failed("store", &e))?;
        }

        for ((offset, field_type), value) in capture_offsets.iter().zip(capture_types.iter()).zip(captures.iter()) {
            let capture_val = self.get_vreg(value, vreg_map)?;
            let offset_val = self.context_ref().i32_type().const_int(*offset as u64, false);
            let field_ptr = unsafe { builder.build_gep(i8_type, closure_ptr, &[offset_val], "cap_ptr") }
                .map_err(|e| crate::error::factory::llvm_build_failed("gep", &e))?;
            let llvm_field_ty = self.llvm_type(field_type)?;
            let coerced_capture_val = self.coerce_value_to_type(capture_val, Some(llvm_field_ty), builder)?;
            let typed_ptr = builder
                .build_pointer_cast(
                    field_ptr,
                    self.context_ref().ptr_type(inkwell::AddressSpace::default()),
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
}

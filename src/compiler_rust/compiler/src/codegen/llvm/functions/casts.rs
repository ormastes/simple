use super::LlvmBackend;
use crate::error::CompileError;

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::module::Module;
#[cfg(feature = "llvm")]
use inkwell::types::BasicTypeEnum;

fn runtime_integer_cast_requires_decode(from_type: crate::hir::TypeId, to_type: crate::hir::TypeId) -> bool {
    matches!(from_type, crate::hir::TypeId::ANY | crate::hir::TypeId::STRING)
        && matches!(
            to_type,
            crate::hir::TypeId::I8
                | crate::hir::TypeId::I16
                | crate::hir::TypeId::I32
                | crate::hir::TypeId::I64
                | crate::hir::TypeId::U8
                | crate::hir::TypeId::U16
                | crate::hir::TypeId::U32
                | crate::hir::TypeId::U64
        )
}

// An explicit semantic integer -> f64 cast is numeric conversion, not the
// representation-only bitcast used when moving an existing f64 through the
// RuntimeValue ABI. Do not classify ANY/text/nominal runtime words as integers
// merely because their physical LLVM value happens to be an IntValue.
fn explicit_integer_to_f64_source(
    from_type: crate::hir::TypeId,
    to_type: crate::hir::TypeId,
) -> Option<(u32, bool)> {
    use crate::hir::TypeId as T;
    if to_type != T::F64 {
        return None;
    }
    match from_type {
        T::I8 => Some((8, true)),
        T::I16 => Some((16, true)),
        T::I32 => Some((32, true)),
        T::I64 => Some((64, true)),
        T::U8 => Some((8, false)),
        T::U16 => Some((16, false)),
        T::U32 => Some((32, false)),
        T::U64 => Some((64, false)),
        _ => None,
    }
}

impl LlvmBackend {
    // ============================================================================
    // Cast Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    pub(in crate::codegen::llvm) fn compile_cast(
        &self,
        source_val: inkwell::values::BasicValueEnum<'static>,
        from_type: &crate::hir::TypeId,
        to_type: &crate::hir::TypeId,
        builder: &Builder<'static>,
        module: &Module<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        if let Some((bits, signed)) = explicit_integer_to_f64_source(*from_type, *to_type) {
            let mut integer = match source_val {
                inkwell::values::BasicValueEnum::IntValue(value) => value,
                _ => {
                    return Err(CompileError::semantic(
                        "explicit integer-to-f64 cast requires an integer SSA source".to_string(),
                    ));
                }
            };
            // The native ABI may carry a narrow scalar in a runtime-width
            // register. Restore its semantic width before signed/unsigned
            // conversion; do not reinterpret those integer bits as a double.
            let source_width = integer.get_type().get_bit_width();
            let semantic_type = match bits {
                8 => self.context_ref().i8_type(),
                16 => self.context_ref().i16_type(),
                32 => self.context_ref().i32_type(),
                64 => self.context_ref().i64_type(),
                _ => unreachable!("primitive integer cast width"),
            };
            if source_width > bits {
                integer = builder
                    .build_int_truncate(integer, semantic_type, "numeric_cast_narrow")
                    .map_err(|e| crate::error::factory::llvm_build_failed("numeric cast narrow", &e))?;
            } else if source_width < bits {
                integer = if signed {
                    builder.build_int_s_extend(integer, semantic_type, "numeric_cast_sext")
                } else {
                    builder.build_int_z_extend(integer, semantic_type, "numeric_cast_zext")
                }
                .map_err(|e| crate::error::factory::llvm_build_failed("numeric cast extend", &e))?;
            }
            let converted = if signed {
                builder.build_signed_int_to_float(integer, self.context_ref().f64_type(), "numeric_sitofp")
            } else {
                builder.build_unsigned_int_to_float(integer, self.context_ref().f64_type(), "numeric_uitofp")
            }
            .map_err(|e| crate::error::factory::llvm_build_failed("numeric integer-to-f64 cast", &e))?;
            return Ok(converted.into());
        }

        if runtime_integer_cast_requires_decode(*from_type, *to_type) {
            match *to_type {
                crate::hir::TypeId::I8
                | crate::hir::TypeId::I16
                | crate::hir::TypeId::I32
                | crate::hir::TypeId::I64
                | crate::hir::TypeId::U8
                | crate::hir::TypeId::U16
                | crate::hir::TypeId::U32
                | crate::hir::TypeId::U64 => {
                    let rv_type = self.runtime_int_type();
                    let src_int = self
                        .coerce_value_to_type(source_val, Some(rv_type.into()), builder)?
                        .into_int_value();
                    let fn_type = rv_type.fn_type(&[rv_type.into()], false);
                    let unwrap_name = if *to_type == crate::hir::TypeId::U64 && *from_type == crate::hir::TypeId::ANY {
                        "rt_value_as_u64"
                    } else {
                        "rt_value_as_int"
                    };
                    let func = module
                        .get_function(unwrap_name)
                        .unwrap_or_else(|| module.add_function(unwrap_name, fn_type, None));
                    let call = builder
                        .build_call(func, &[src_int.into()], unwrap_name)
                        .map_err(|e| crate::error::factory::llvm_build_failed("call rt_value_as_int", &e))?;
                    let raw_i64 = call
                        .try_as_basic_value()
                        .basic()
                        .ok_or_else(|| CompileError::semantic(format!("{unwrap_name} returned no value")))?
                        .into_int_value();
                    let narrowed = match *to_type {
                        crate::hir::TypeId::I8 | crate::hir::TypeId::U8 => builder
                            .build_int_truncate(raw_i64, self.context_ref().i8_type(), "any_to_i8")
                            .map_err(|e| crate::error::factory::llvm_build_failed("trunc any->i8", &e))?
                            .into(),
                        crate::hir::TypeId::I16 | crate::hir::TypeId::U16 => builder
                            .build_int_truncate(raw_i64, self.context_ref().i16_type(), "any_to_i16")
                            .map_err(|e| crate::error::factory::llvm_build_failed("trunc any->i16", &e))?
                            .into(),
                        crate::hir::TypeId::I32 | crate::hir::TypeId::U32 => builder
                            .build_int_truncate(raw_i64, self.context_ref().i32_type(), "any_to_i32")
                            .map_err(|e| crate::error::factory::llvm_build_failed("trunc any->i32", &e))?
                            .into(),
                        _ => raw_i64.into(),
                    };
                    return Ok(narrowed);
                }
                _ => {}
            }
        }

        // Preserve the existing representation-only handling for other cast
        // categories. Numeric integer-to-f64 conversion is handled above;
        // generic ABI reconciliation still preserves an existing float's bits.
        Ok(source_val)
    }
}

#[cfg(test)]
mod tests {
    use super::{explicit_integer_to_f64_source, runtime_integer_cast_requires_decode};
    use crate::hir::TypeId;

    #[test]
    fn tagged_any_and_text_integer_casts_require_runtime_decode() {
        assert!(runtime_integer_cast_requires_decode(TypeId::ANY, TypeId::I64));
        assert!(runtime_integer_cast_requires_decode(TypeId::STRING, TypeId::I64));
        assert!(runtime_integer_cast_requires_decode(TypeId::STRING, TypeId::U8));
        assert!(!runtime_integer_cast_requires_decode(TypeId::I64, TypeId::I64));
        assert!(!runtime_integer_cast_requires_decode(TypeId::STRING, TypeId::F64));
    }

    #[test]
    fn explicit_integer_to_f64_is_gated_by_semantic_type() {
        assert_eq!(explicit_integer_to_f64_source(TypeId::I64, TypeId::F64), Some((64, true)));
        assert_eq!(explicit_integer_to_f64_source(TypeId::U64, TypeId::F64), Some((64, false)));
        for from in [TypeId::ANY, TypeId::STRING, TypeId::F32, TypeId::F64, TypeId::BOOL] {
            assert_eq!(explicit_integer_to_f64_source(from, TypeId::F64), None);
        }
        assert_eq!(explicit_integer_to_f64_source(TypeId::I64, TypeId::I64), None);
        assert_eq!(explicit_integer_to_f64_source(TypeId::I64, TypeId::F32), None);
    }

    #[cfg(feature = "llvm")]
    fn verify_numeric_f64_module_and_object(arch: simple_common::target::TargetArch, machine: [u8; 2]) {
        use super::LlvmBackend;
        use simple_common::target::{Target, TargetOS};

        let backend = LlvmBackend::new(Target::new(arch, TargetOS::Windows)).unwrap();
        backend.create_module("explicit_numeric_f64_cast").unwrap();
        {
            let module_ref = backend.module.borrow();
            let module = module_ref.as_ref().unwrap();
            let builder_ref = backend.builder.borrow();
            let builder = builder_ref.as_ref().unwrap();
            let double = backend.context_ref().f64_type();
            for (name, source) in [
                ("cast_i8", TypeId::I8), ("cast_u8", TypeId::U8),
                ("cast_i16", TypeId::I16), ("cast_u16", TypeId::U16),
                ("cast_i32", TypeId::I32), ("cast_u32", TypeId::U32),
                ("cast_i64", TypeId::I64), ("cast_u64", TypeId::U64),
            ] {
                let input = backend.runtime_int_type();
                let function = module.add_function(name, double.fn_type(&[input.into()], false), None);
                builder.position_at_end(backend.context_ref().append_basic_block(function, "entry"));
                let converted = backend.compile_cast(
                    function.get_first_param().unwrap(), &source, &TypeId::F64, builder, module,
                ).unwrap();
                // The baseline's no-op becomes an ABI bitcast here, making
                // the missing numeric conversion observable in real LLVM IR.
                let returned = backend.coerce_value_to_type(converted, Some(double.into()), builder).unwrap();
                builder.build_return(Some(&returned)).unwrap();
            }
            // Keep the separate ABI-only bitcast behavior unchanged.
            let word = backend.context_ref().i64_type();
            let function = module.add_function("abi_float_bits", double.fn_type(&[word.into()], false), None);
            builder.position_at_end(backend.context_ref().append_basic_block(function, "entry"));
            let returned = backend.coerce_value_to_type(
                function.get_first_param().unwrap(), Some(double.into()), builder,
            ).unwrap();
            builder.build_return(Some(&returned)).unwrap();
        }
        let ir = backend.get_ir().unwrap();
        for width in [8, 16, 32, 64] {
            for (prefix, instruction) in [("i", "sitofp"), ("u", "uitofp")] {
                let name = format!("@cast_{prefix}{width}(");
                let start = ir.find(&name).unwrap_or_else(|| panic!("missing function {name}: {ir}"));
                let tail = &ir[start..];
                let end = tail.find("\n}").expect("numeric cast function body");
                let body = &tail[..end];
                assert!(body.contains(&format!("{instruction} i{width}")),
                    "{name} must retain its own signedness and width: {body}");
            }
        }
        assert!(ir.contains("trunc i"), "runtime-width inputs must restore narrow semantics: {ir}");
        if backend.runtime_int_type().get_bit_width() == 32 {
            assert!(ir.contains("sext i32") && ir.contains("zext i32"), "32-bit carriers must widen signed/unsigned i64 distinctly: {ir}");
        }
        assert!(ir.contains("bitcast i64") && ir.contains("to double"), "ABI bitcast disappeared: {ir}");
        assert!(!ir.contains("@rt_value_as_float"), "raw integers must not enter tagged-float decoding: {ir}");
        backend.verify().unwrap();
        let object = backend.emit_object(&crate::mir::MirModule::new()).unwrap();
        assert!(object.len() > 20, "no COFF sections emitted");
        assert_eq!(&object[..2], &machine, "wrong COFF target machine");
    }

    #[cfg(feature = "llvm")]
    #[test]
    fn explicit_numeric_f64_casts_emit_verified_x64_ir_and_coff() {
        verify_numeric_f64_module_and_object(simple_common::target::TargetArch::X86_64, [0x64, 0x86]);
    }

    #[cfg(feature = "llvm")]
    #[test]
    fn explicit_numeric_f64_casts_emit_verified_x86_ir_and_coff() {
        verify_numeric_f64_module_and_object(simple_common::target::TargetArch::X86, [0x4c, 0x01]);
    }
}

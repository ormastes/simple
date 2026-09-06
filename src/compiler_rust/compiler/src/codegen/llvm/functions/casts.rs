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
                        .left()
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

        // In Simple's tagged-value ABI, all values are i64 at runtime.
        // Casts between integer types, ANY, pointer types, etc. are all no-ops.
        // Float values are stored as f64 bits in i64, so float↔int casts
        // would need bitcast, but at the MIR level the runtime handles this.
        // Simply pass through the value unchanged.
        Ok(source_val)
    }
}

#[cfg(test)]
mod tests {
    use super::runtime_integer_cast_requires_decode;
    use crate::hir::TypeId;

    #[test]
    fn tagged_any_and_text_integer_casts_require_runtime_decode() {
        assert!(runtime_integer_cast_requires_decode(TypeId::ANY, TypeId::I64));
        assert!(runtime_integer_cast_requires_decode(TypeId::STRING, TypeId::I64));
        assert!(runtime_integer_cast_requires_decode(TypeId::STRING, TypeId::U8));
        assert!(!runtime_integer_cast_requires_decode(TypeId::I64, TypeId::I64));
        assert!(!runtime_integer_cast_requires_decode(TypeId::STRING, TypeId::F64));
    }
}

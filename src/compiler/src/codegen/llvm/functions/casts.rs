use super::LlvmBackend;
use crate::error::CompileError;

#[cfg(feature = "llvm")]
use inkwell::builder::Builder;
#[cfg(feature = "llvm")]
use inkwell::types::BasicTypeEnum;

impl LlvmBackend {
    // ============================================================================
    // Cast Instructions
    // ============================================================================

    #[cfg(feature = "llvm")]
    fn compile_cast(
        &self,
        source_val: inkwell::values::BasicValueEnum<'static>,
        from_type: &crate::hir::TypeId,
        to_type: &crate::hir::TypeId,
        builder: &Builder<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        use crate::hir::TypeId;

        let i64_type = self.context.i64_type();
        let f64_type = self.context.f64_type();

        match (*from_type, *to_type) {
            // Float to Int (f64 -> i64)
            (TypeId::F64, TypeId::I64)
            | (TypeId::F32, TypeId::I64)
            | (TypeId::F32, TypeId::I32)
            | (TypeId::F64, TypeId::I32) => {
                if let inkwell::values::BasicValueEnum::FloatValue(float_val) = source_val {
                    let result = builder
                        .build_float_to_signed_int(float_val, i64_type, "cast_f2i")
                        .map_err(|e| {
                            CompileError::Semantic(format!("Failed to cast float to int: {}", e))
                        })?;
                    Ok(result.into())
                } else {
                    Err(CompileError::Semantic(
                        "Expected float value for float-to-int cast".to_string(),
                    ))
                }
            }
            // Int to Float (i64 -> f64)
            (TypeId::I64, TypeId::F64)
            | (TypeId::I32, TypeId::F64)
            | (TypeId::I32, TypeId::F32)
            | (TypeId::I64, TypeId::F32) => {
                if let inkwell::values::BasicValueEnum::IntValue(int_val) = source_val {
                    let result = builder
                        .build_signed_int_to_float(int_val, f64_type, "cast_i2f")
                        .map_err(|e| {
                            CompileError::Semantic(format!("Failed to cast int to float: {}", e))
                        })?;
                    Ok(result.into())
                } else {
                    Err(CompileError::Semantic(
                        "Expected int value for int-to-float cast".to_string(),
                    ))
                }
            }
            // Int to Int (widening or truncation)
            (TypeId::I32, TypeId::I64) => {
                if let inkwell::values::BasicValueEnum::IntValue(int_val) = source_val {
                    let result = builder
                        .build_int_s_extend(int_val, i64_type, "cast_i32_i64")
                        .map_err(|e| {
                            CompileError::Semantic(format!("Failed to extend int: {}", e))
                        })?;
                    Ok(result.into())
                } else {
                    Err(CompileError::Semantic(
                        "Expected int value for int-to-int cast".to_string(),
                    ))
                }
            }
            (TypeId::I64, TypeId::I32) => {
                if let inkwell::values::BasicValueEnum::IntValue(int_val) = source_val {
                    let i32_type = self.context.i32_type();
                    let result = builder
                        .build_int_truncate(int_val, i32_type, "cast_i64_i32")
                        .map_err(|e| {
                            CompileError::Semantic(format!("Failed to truncate int: {}", e))
                        })?;
                    Ok(result.into())
                } else {
                    Err(CompileError::Semantic(
                        "Expected int value for int-to-int cast".to_string(),
                    ))
                }
            }
            // Float to Float (widening or truncation)
            (TypeId::F32, TypeId::F64) => {
                if let inkwell::values::BasicValueEnum::FloatValue(float_val) = source_val {
                    let result = builder
                        .build_float_ext(float_val, f64_type, "cast_f32_f64")
                        .map_err(|e| {
                            CompileError::Semantic(format!("Failed to extend float: {}", e))
                        })?;
                    Ok(result.into())
                } else {
                    Err(CompileError::Semantic(
                        "Expected float value for float-to-float cast".to_string(),
                    ))
                }
            }
            (TypeId::F64, TypeId::F32) => {
                if let inkwell::values::BasicValueEnum::FloatValue(float_val) = source_val {
                    let f32_type = self.context.f32_type();
                    let result = builder
                        .build_float_trunc(float_val, f32_type, "cast_f64_f32")
                        .map_err(|e| {
                            CompileError::Semantic(format!("Failed to truncate float: {}", e))
                        })?;
                    Ok(result.into())
                } else {
                    Err(CompileError::Semantic(
                        "Expected float value for float-to-float cast".to_string(),
                    ))
                }
            }
            // Same type - no-op
            _ if from_type == to_type => Ok(source_val),
            // Unsupported cast
            _ => Err(CompileError::Semantic(format!(
                "Unsupported cast from {:?} to {:?}", from_type, to_type
            ))),
        }
    }
}

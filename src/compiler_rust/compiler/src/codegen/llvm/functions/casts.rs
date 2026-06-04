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
    pub(in crate::codegen::llvm) fn compile_cast(
        &self,
        source_val: inkwell::values::BasicValueEnum<'static>,
        _from_type: &crate::hir::TypeId,
        _to_type: &crate::hir::TypeId,
        _builder: &Builder<'static>,
    ) -> Result<inkwell::values::BasicValueEnum<'static>, CompileError> {
        // In Simple's tagged-value ABI, all values are i64 at runtime.
        // Casts between integer types, ANY, pointer types, etc. are all no-ops.
        // Float values are stored as f64 bits in i64, so float↔int casts
        // would need bitcast, but at the MIR level the runtime handles this.
        // Simply pass through the value unchanged.
        Ok(source_val)
    }
}

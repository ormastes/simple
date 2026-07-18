/// LLVM type system and type mapping
use crate::error::CompileError;
use crate::hir::TypeId;

#[cfg(feature = "llvm")]
use inkwell::types::BasicTypeEnum;

/// LLVM type representation
#[derive(Debug, Clone, PartialEq)]
pub enum LlvmType {
    Void,
    I1,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    Pointer(Box<LlvmType>),
    Struct(Vec<LlvmType>),
    Array(Box<LlvmType>, usize),
}

/// Binary operation types
#[derive(Debug, Clone, Copy)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
}

impl super::LlvmBackend {
    /// Map TypeId to LlvmType
    pub fn map_type(&self, ty: &TypeId) -> Result<LlvmType, CompileError> {
        use crate::hir::TypeId as T;
        match *ty {
            T::VOID => Ok(LlvmType::Void),
            T::BOOL => Ok(LlvmType::I1),
            T::I8 | T::U8 => Ok(LlvmType::I8),
            T::I16 | T::U16 => Ok(LlvmType::I16),
            T::I32 | T::U32 | T::CHAR => Ok(LlvmType::I32),
            T::I64 | T::U64 => Ok(LlvmType::I64),
            T::F32 => Ok(LlvmType::F32),
            T::F64 => Ok(LlvmType::F64),
            T::STRING | T::NIL | T::ANY => Ok(LlvmType::Pointer(Box::new(LlvmType::I8))),
            // User-defined types (structs, enums, etc.) → opaque pointer
            _ => Ok(LlvmType::Pointer(Box::new(LlvmType::I8))),
        }
    }

    /// Get actual LLVM BasicTypeEnum for a TypeId (feature-gated)
    ///
    /// For native-build (bootstrap), ALL values are represented as a single
    /// integer whose width matches the target's RuntimeValue:
    /// - 64-bit targets: i64 (tagged 64-bit value)
    /// - 32-bit targets: i32 (tagged 32-bit value)
    ///
    /// The C runtime defines `typedef int64_t RuntimeValue` on 64-bit and
    /// `typedef int32_t RuntimeValue` on 32-bit (e.g. RV32). Using the
    /// matching width avoids calling-convention mismatches where the LLVM
    /// backend would pass i64 in two registers (a0+a1 on RV32) but the C
    /// function expects a single-register i32 argument.
    #[cfg(feature = "llvm")]
    pub(super) fn llvm_type(&self, _ty: &TypeId) -> Result<BasicTypeEnum<'static>, CompileError> {
        Ok(self.runtime_int_type().into())
    }
}

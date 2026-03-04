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
    #[cfg(feature = "llvm")]
    pub(super) fn llvm_type(&self, ty: &TypeId) -> Result<BasicTypeEnum<'static>, CompileError> {
        use crate::hir::TypeId as T;
        match *ty {
            T::VOID => Ok(self.context.i8_type().into()), // void → i8 (for BasicTypeEnum)
            T::BOOL => Ok(self.context.bool_type().into()),
            T::I8 | T::U8 => Ok(self.context.i8_type().into()),
            T::I16 | T::U16 => Ok(self.context.i16_type().into()),
            T::I32 | T::U32 | T::CHAR => Ok(self.context.i32_type().into()),
            T::I64 | T::U64 => Ok(self.context.i64_type().into()),
            T::F32 => Ok(self.context.f32_type().into()),
            T::F64 => Ok(self.context.f64_type().into()),
            T::STRING | T::NIL | T::ANY => {
                Ok(self.context.ptr_type(inkwell::AddressSpace::default()).into())
            }
            // User-defined types (structs, enums, arrays, etc.) → opaque pointer
            _ => Ok(self.context.ptr_type(inkwell::AddressSpace::default()).into()),
        }
    }
}

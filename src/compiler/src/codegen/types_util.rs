//! Type conversion utilities shared between AOT and JIT codegen.

use crate::hir::TypeId;
use cranelift_codegen::ir::types;

/// Convert TypeId to Cranelift type for zero-cost codegen.
///
/// This maps Simple language types to their native machine representations
/// for efficient codegen without RuntimeValue boxing.
pub fn type_id_to_cranelift(type_id: TypeId) -> types::Type {
    match type_id {
        TypeId::VOID => types::I64, // Use I64 for void (no actual value)
        TypeId::BOOL => types::I8,
        TypeId::I8 => types::I8,
        TypeId::I16 => types::I16,
        TypeId::I32 => types::I32,
        TypeId::I64 => types::I64,
        TypeId::U8 => types::I8,
        TypeId::U16 => types::I16,
        TypeId::U32 => types::I32,
        TypeId::U64 => types::I64,
        TypeId::F32 => types::F32,
        TypeId::F64 => types::F64,
        TypeId::STRING => types::I64, // Pointer
        TypeId::NIL => types::I64,    // Tagged value
        // All other types (objects, closures, arrays, etc.) use i64 (RuntimeValue)
        _ => types::I64,
    }
}

/// Get the size in bytes for a TypeId.
///
/// Returns the native size of the type for memory layout calculations.
pub fn type_id_size(type_id: TypeId) -> u32 {
    match type_id {
        TypeId::VOID => 0,
        TypeId::BOOL | TypeId::I8 | TypeId::U8 => 1,
        TypeId::I16 | TypeId::U16 => 2,
        TypeId::I32 | TypeId::U32 | TypeId::F32 => 4,
        TypeId::I64 | TypeId::U64 | TypeId::F64 => 8,
        TypeId::STRING | TypeId::NIL => 8,
        // All other types are pointer-sized (8 bytes)
        _ => 8,
    }
}

/// Convert TypeId to Cranelift type for function signatures.
///
/// This maps types to their native ABI representation for function calls.
/// Note: BOOL uses I8 for native ABI compatibility.
pub fn type_to_cranelift(ty: TypeId) -> types::Type {
    match ty {
        TypeId::VOID => types::I64, // Void returns use I64 for ABI compatibility
        TypeId::BOOL => types::I8,
        TypeId::I8 | TypeId::U8 => types::I8,
        TypeId::I16 | TypeId::U16 => types::I16,
        TypeId::I32 | TypeId::U32 => types::I32,
        TypeId::I64 | TypeId::U64 => types::I64,
        TypeId::F32 => types::F32,
        TypeId::F64 => types::F64,
        TypeId::STRING => types::I64, // String pointer
        TypeId::NIL => types::I64,    // Nil is pointer-sized
        _ => types::I64,              // Custom types default to pointer-sized
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_type_id_to_cranelift() {
        assert_eq!(type_id_to_cranelift(TypeId::I64), types::I64);
        assert_eq!(type_id_to_cranelift(TypeId::BOOL), types::I8);
        assert_eq!(type_id_to_cranelift(TypeId::F64), types::F64);
    }

    #[test]
    fn test_type_id_size() {
        assert_eq!(type_id_size(TypeId::I8), 1);
        assert_eq!(type_id_size(TypeId::I32), 4);
        assert_eq!(type_id_size(TypeId::I64), 8);
        assert_eq!(type_id_size(TypeId::STRING), 8);
    }

    #[test]
    fn test_type_to_cranelift() {
        // Function params/returns use native ABI types
        assert_eq!(type_to_cranelift(TypeId::I64), types::I64);
        assert_eq!(type_to_cranelift(TypeId::BOOL), types::I8);
        assert_eq!(type_to_cranelift(TypeId::F64), types::F64);
    }
}

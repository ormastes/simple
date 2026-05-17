//! Type conversion utilities shared between AOT and JIT codegen.

use crate::hir::TypeId;
use cranelift_codegen::ir::types;

/// Returns the Cranelift pointer type for a given target pointer width in bits.
pub fn ptr_type(pointer_bits: u8) -> types::Type {
    match pointer_bits {
        32 => types::I32,
        _ => types::I64,
    }
}

/// Returns pointer size in bytes for a given target pointer width in bits.
pub fn ptr_bytes(pointer_bits: u8) -> u32 {
    match pointer_bits {
        32 => 4,
        _ => 8,
    }
}

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
        TypeId::ANY => types::I64,    // Dynamic type (RuntimeValue)
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
        TypeId::STRING | TypeId::NIL | TypeId::ANY => 8,
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
        TypeId::ANY => types::I64,    // Dynamic Any type (RuntimeValue)
        _ => types::I64,              // Custom types default to pointer-sized
    }
}

/// Target-aware TypeId to Cranelift type conversion.
/// Pointer-bearing types use the target's native pointer width.
pub fn type_id_to_cranelift_for_target(type_id: TypeId, pointer_bits: u8) -> types::Type {
    let ptr = ptr_type(pointer_bits);
    match type_id {
        TypeId::VOID => ptr,
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
        TypeId::STRING => ptr,
        TypeId::NIL => ptr,
        TypeId::ANY => ptr,
        _ => ptr,
    }
}

/// Target-aware type size in bytes.
pub fn type_id_size_for_target(type_id: TypeId, pointer_bits: u8) -> u32 {
    let ps = ptr_bytes(pointer_bits);
    match type_id {
        TypeId::VOID => 0,
        TypeId::BOOL | TypeId::I8 | TypeId::U8 => 1,
        TypeId::I16 | TypeId::U16 => 2,
        TypeId::I32 | TypeId::U32 | TypeId::F32 => 4,
        TypeId::I64 | TypeId::U64 | TypeId::F64 => 8,
        TypeId::STRING | TypeId::NIL | TypeId::ANY => ps,
        _ => ps,
    }
}

/// Target-aware function signature type conversion.
pub fn type_to_cranelift_for_target(ty: TypeId, pointer_bits: u8) -> types::Type {
    let ptr = ptr_type(pointer_bits);
    match ty {
        TypeId::VOID => ptr,
        TypeId::BOOL => types::I8,
        TypeId::I8 | TypeId::U8 => types::I8,
        TypeId::I16 | TypeId::U16 => types::I16,
        TypeId::I32 | TypeId::U32 => types::I32,
        TypeId::I64 | TypeId::U64 => types::I64,
        TypeId::F32 => types::F32,
        TypeId::F64 => types::F64,
        TypeId::STRING => ptr,
        TypeId::NIL => ptr,
        TypeId::ANY => ptr,
        _ => ptr,
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

    #[test]
    fn test_ptr_type() {
        assert_eq!(ptr_type(32), types::I32);
        assert_eq!(ptr_type(64), types::I64);
    }

    #[test]
    fn test_target_aware_32bit() {
        assert_eq!(type_id_to_cranelift_for_target(TypeId::STRING, 32), types::I32);
        assert_eq!(type_id_to_cranelift_for_target(TypeId::ANY, 32), types::I32);
        assert_eq!(type_id_to_cranelift_for_target(TypeId::I64, 32), types::I64);
        assert_eq!(type_id_size_for_target(TypeId::STRING, 32), 4);
        assert_eq!(type_id_size_for_target(TypeId::I64, 32), 8);
    }

    #[test]
    fn test_target_aware_64bit_matches_original() {
        // 64-bit target-aware must match the original functions
        for ty in [TypeId::I8, TypeId::I32, TypeId::I64, TypeId::STRING, TypeId::ANY, TypeId::F64] {
            assert_eq!(
                type_id_to_cranelift(ty),
                type_id_to_cranelift_for_target(ty, 64)
            );
            assert_eq!(
                type_id_size(ty),
                type_id_size_for_target(ty, 64)
            );
        }
    }
}

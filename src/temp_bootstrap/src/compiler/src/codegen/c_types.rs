//! Type mapping: TypeId → C type string.
//!
//! Maps Simple language types to their C representation for the C code generation backend.

use crate::hir::TypeId;

/// Convert a TypeId to its C type string representation.
///
/// All object/pointer/string types use `int64_t` since the runtime uses tagged 64-bit values.
pub fn type_id_to_c(type_id: TypeId) -> &'static str {
    match type_id {
        TypeId::VOID => "void",
        TypeId::BOOL => "int8_t",
        TypeId::I8 => "int8_t",
        TypeId::I16 => "int16_t",
        TypeId::I32 => "int32_t",
        TypeId::I64 => "int64_t",
        TypeId::U8 => "uint8_t",
        TypeId::U16 => "uint16_t",
        TypeId::U32 => "uint32_t",
        TypeId::U64 => "uint64_t",
        TypeId::F32 => "float",
        TypeId::F64 => "double",
        TypeId::STRING => "int64_t", // Runtime tagged value (pointer)
        TypeId::NIL => "int64_t",    // Runtime tagged value
        _ => "int64_t",             // Custom types default to runtime tagged value
    }
}

/// Convert a TypeId to a C type suitable for local variable declarations.
///
/// Unlike `type_id_to_c`, this never returns "void" — void locals are represented as `int64_t`.
pub fn type_id_to_c_local(type_id: TypeId) -> &'static str {
    match type_id {
        TypeId::VOID => "int64_t", // Locals can't be void
        _ => type_id_to_c(type_id),
    }
}

/// Convert a TypeId to a C type for function return types.
///
/// VOID maps to "int64_t" for ABI compatibility (callers expect a return value).
pub fn type_id_to_c_return(type_id: TypeId) -> &'static str {
    match type_id {
        TypeId::VOID => "int64_t",
        _ => type_id_to_c(type_id),
    }
}

/// Convert a TypeId to a C type for function parameters.
pub fn type_id_to_c_param(type_id: TypeId) -> &'static str {
    match type_id {
        TypeId::VOID => "int64_t",
        _ => type_id_to_c(type_id),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_primitive_types() {
        assert_eq!(type_id_to_c(TypeId::I8), "int8_t");
        assert_eq!(type_id_to_c(TypeId::I16), "int16_t");
        assert_eq!(type_id_to_c(TypeId::I32), "int32_t");
        assert_eq!(type_id_to_c(TypeId::I64), "int64_t");
        assert_eq!(type_id_to_c(TypeId::U8), "uint8_t");
        assert_eq!(type_id_to_c(TypeId::U16), "uint16_t");
        assert_eq!(type_id_to_c(TypeId::U32), "uint32_t");
        assert_eq!(type_id_to_c(TypeId::U64), "uint64_t");
        assert_eq!(type_id_to_c(TypeId::F32), "float");
        assert_eq!(type_id_to_c(TypeId::F64), "double");
        assert_eq!(type_id_to_c(TypeId::BOOL), "int8_t");
    }

    #[test]
    fn test_void_type() {
        assert_eq!(type_id_to_c(TypeId::VOID), "void");
        assert_eq!(type_id_to_c_local(TypeId::VOID), "int64_t");
        assert_eq!(type_id_to_c_return(TypeId::VOID), "int64_t");
    }

    #[test]
    fn test_pointer_types() {
        assert_eq!(type_id_to_c(TypeId::STRING), "int64_t");
        assert_eq!(type_id_to_c(TypeId::NIL), "int64_t");
    }

    #[test]
    fn test_custom_types_default_to_i64() {
        // Custom types (ID > 13) should map to int64_t
        assert_eq!(type_id_to_c(TypeId(100)), "int64_t");
        assert_eq!(type_id_to_c(TypeId(999)), "int64_t");
    }
}

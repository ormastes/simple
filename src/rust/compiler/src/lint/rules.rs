//! Lint rule implementations and type checking.

use simple_parser::ast::Type;

/// The primitive types that trigger the primitive_api lint
const PRIMITIVE_TYPES: &[&str] = &[
    "i8", "i16", "i32", "i64", "u8", "u16", "u32", "u64", "f32", "f64", "bool",
];

/// Check if a type is a bare primitive
pub(super) fn is_primitive_type(ty: &Type) -> bool {
    match ty {
        Type::Simple(name) => PRIMITIVE_TYPES.contains(&name.as_str()),
        _ => false,
    }
}

/// Check if a type is bare bool specifically
pub(super) fn is_bare_bool(ty: &Type) -> bool {
    matches!(ty, Type::Simple(name) if name == "bool")
}

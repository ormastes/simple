//! Enum discriminant/payload SFFI bridge for the interpreter.
//!
//! Codegen lowers enum values to heap-allocated `RuntimeEnum` records and
//! reads them back via the `rt_enum_discriminant`/`rt_enum_payload` externs
//! (see `simple_runtime::value::objects`). The interpreter never allocates a
//! `RuntimeEnum` — it represents enum values natively as `Value::Enum { .. }`
//! — but the self-hosted compiler source (disc-dispatch idiom) calls these
//! externs directly on ordinary enum values (`TypeKind`, `ExprKind`,
//! `StmtKind`, `HirExprKind`, `HirBinOp`, ...), so the interpreter must expose
//! the same two externs against `Value::Enum` and reproduce the runtime's
//! semantics EXACTLY — including reusing the shared `hash_variant_discriminant`
//! name-hash so a discriminant computed here always matches the constant
//! codegen bakes in for the same variant name (task #113).

use crate::error::CompileError;
use crate::value::Value;
use simple_runtime::value::hash_variant_discriminant;

/// Get the discriminant (name-hash tag) of an enum value.
///
/// Mirrors `simple_runtime::value::objects::rt_enum_discriminant`: returns
/// the hash of the variant name (truncated to u32, sign-extended to i64) for
/// an enum value, or -1 if the value is not an enum.
pub fn rt_enum_discriminant_fn(args: &[Value]) -> Result<Value, CompileError> {
    let disc = match args.first() {
        Some(Value::Enum { variant, .. }) => hash_variant_discriminant(variant) as i64,
        _ => -1,
    };
    Ok(Value::Int(disc))
}

/// Get the payload of an enum value.
///
/// Mirrors `simple_runtime::value::objects::rt_enum_payload`: returns the
/// payload value if present, or `Value::Nil` if the enum variant carries no
/// payload / the value is not an enum at all.
pub fn rt_enum_payload_fn(args: &[Value]) -> Result<Value, CompileError> {
    let payload = match args.first() {
        Some(Value::Enum { payload: Some(p), .. }) => (**p).clone(),
        _ => Value::Nil,
    };
    Ok(payload)
}

/// Get the runtime enum-family identity of an enum value.
///
/// Mirrors `simple_runtime::value::objects::rt_enum_id`: a stable positive id
/// shared by every variant of one enum type, or `-1` for a non-enum. The
/// interpreter has no registered `RuntimeEnum` ids, so the id is the shared
/// name hash of the enum type name (0 is reserved as the legacy untyped lane,
/// so a zero hash maps to 1).
pub fn rt_enum_id_fn(args: &[Value]) -> Result<Value, CompileError> {
    let id = match args.first() {
        Some(Value::Enum { enum_name, .. }) => match hash_variant_discriminant(enum_name) {
            0 => 1,
            h => h as i64,
        },
        _ => -1,
    };
    Ok(Value::Int(id))
}

#[cfg(test)]
mod rt_enum_id_tests {
    use super::*;

    fn enum_value(enum_name: &str, variant: &str) -> Value {
        Value::Enum { enum_name: enum_name.to_string(), variant: variant.to_string(), payload: None }
    }

    #[test]
    fn same_enum_shares_positive_id_across_variants() {
        let a = rt_enum_id_fn(&[enum_value("SymbolKind", "Function")]).unwrap();
        let b = rt_enum_id_fn(&[enum_value("SymbolKind", "Variable")]).unwrap();
        assert_eq!(a, b);
        assert!(matches!(a, Value::Int(n) if n > 0));
    }

    #[test]
    fn different_enums_differ_and_non_enum_is_negative() {
        let a = rt_enum_id_fn(&[enum_value("SymbolKind", "Function")]).unwrap();
        let b = rt_enum_id_fn(&[enum_value("HirTypeKind", "Function")]).unwrap();
        assert_ne!(a, b);
        assert_eq!(rt_enum_id_fn(&[Value::Int(3)]).unwrap(), Value::Int(-1));
        assert_eq!(rt_enum_id_fn(&[]).unwrap(), Value::Int(-1));
    }
}

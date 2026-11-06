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

use crate::codegen::shared::enum_runtime_type_id;
use crate::error::CompileError;
use crate::value::Value;
use simple_runtime::value::hash_variant_discriminant;

/// Get the discriminant (declaration index) of an enum value.
///
/// Mirrors `simple_runtime::value::objects::rt_enum_discriminant`: returns
/// the positional declaration index (via the seed positional registry) for
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
/// Mirrors `simple_runtime::value::objects::rt_enum_id` after the same value
/// crosses the interpreter/native bridge. Result and Option retain reserved
/// IDs 0 and 1; user enum identities use the shared type-ID function. Variant
/// discriminants are a separate field and are not changed here.
pub fn rt_enum_id_fn(args: &[Value]) -> Result<Value, CompileError> {
    let id = match args.first() {
        Some(Value::Enum { enum_name, .. }) => i64::from(enum_runtime_type_id(enum_name)),
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

    #[test]
    fn builtin_family_ids_match_native_reserved_ids() {
        assert_eq!(rt_enum_id_fn(&[enum_value("Result", "Ok")]).unwrap(), Value::Int(0));
        assert_eq!(rt_enum_id_fn(&[enum_value("Result", "Err")]).unwrap(), Value::Int(0));
        assert_eq!(rt_enum_id_fn(&[enum_value("Option", "Some")]).unwrap(), Value::Int(1));
        assert_eq!(rt_enum_id_fn(&[enum_value("Option", "None")]).unwrap(), Value::Int(1));
    }

    #[test]
    fn interpreter_family_id_agrees_with_native_bridge() {
        for (name, variant) in [
            ("Result", "Ok"),
            ("Result", "Err"),
            ("Option", "Some"),
            ("Option", "None"),
            ("SymbolKind", "Function"),
            ("pkg.Mode", "Shared"),
        ] {
            let interpreted = enum_value(name, variant);
            let native = crate::runtime_bridge::value_to_runtime(&interpreted);
            let native_id = simple_runtime::value::rt_enum_id(native);
            assert_eq!(
                rt_enum_id_fn(&[interpreted]).unwrap(),
                Value::Int(native_id),
                "enum family {name}::{variant} changed identity across the bridge",
            );
        }
    }

    #[test]
    fn family_id_alignment_does_not_change_variant_discriminants() {
        for name in ["Option", "Result", "pkg.Mode"] {
            let interpreted = enum_value(name, "Shared");
            let native = crate::runtime_bridge::value_to_runtime(&interpreted);
            assert_eq!(
                rt_enum_discriminant_fn(&[interpreted]).unwrap(),
                Value::Int(simple_runtime::value::rt_enum_discriminant(native)),
            );
        }
    }
}

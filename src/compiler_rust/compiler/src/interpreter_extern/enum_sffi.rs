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

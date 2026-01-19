use simple_parser::ast::Type;

use crate::error::{codes, CompileError, ErrorContext};
use crate::semantics::{
    bool_cast, cast_bool_to_numeric, cast_float_to_numeric, cast_int_to_numeric, string_cast,
    CastNumericResult, NumericType,
};
use crate::value::Value;

// Value casting functions for interpreter_expr module
// Uses unified cast rules from crate::semantics::cast_rules

/// Cast a value to a target type
pub(super) fn cast_value(val: Value, target_type: &Type) -> Result<Value, CompileError> {
    match target_type {
        Type::Simple(type_name) => cast_to_simple_type(val, type_name),
        Type::Optional(inner) => {
            // Cast to Option type - wrap in Some
            let cast_val = cast_value(val, inner)?;
            Ok(Value::Enum {
                enum_name: "Option".to_string(),
                variant: "Some".to_string(),
                payload: Some(Box::new(cast_val)),
            })
        }
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("supported cast targets: simple types (bool, str, i64, f64, etc.) and optional types");
            Err(CompileError::semantic_with_context(
                format!("type mismatch: unsupported cast target type: {:?}", target_type),
                ctx,
            ))
        },
    }
}

/// Cast a value to a simple (named) type
fn cast_to_simple_type(val: Value, type_name: &str) -> Result<Value, CompileError> {
    // Check for numeric types first (handles i8-i64, u8-u64, f32, f64)
    if let Some(numeric_type) = NumericType::from_name(type_name) {
        return cast_to_numeric(val, numeric_type);
    }

    match type_name {
        // Boolean
        "bool" => cast_to_bool(val),
        // String
        "str" | "String" => cast_to_string(val),
        // For other types, check if it's already that type
        other => {
            // Type assertion - check if value is already that type
            let actual_type = val.type_name();
            if actual_type == other {
                Ok(val)
            } else {
                let ctx = ErrorContext::new()
                    .with_code(codes::TYPE_MISMATCH)
                    .with_help(format!("cannot convert {} to {} through type assertion", actual_type, other));
                Err(CompileError::semantic_with_context(
                    format!("type mismatch: cannot cast {} to {}", actual_type, other),
                    ctx,
                ))
            }
        }
    }
}

/// Cast a value to a numeric type using unified cast rules.
fn cast_to_numeric(val: Value, target: NumericType) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => match cast_int_to_numeric(i, target) {
            CastNumericResult::Int(v) => Ok(Value::Int(v)),
            CastNumericResult::Float(v) => Ok(Value::Float(v)),
        },
        Value::Float(f) => match cast_float_to_numeric(f, target) {
            CastNumericResult::Int(v) => Ok(Value::Int(v)),
            CastNumericResult::Float(v) => Ok(Value::Float(v)),
        },
        Value::Bool(b) => match cast_bool_to_numeric(b, target) {
            CastNumericResult::Int(v) => Ok(Value::Int(v)),
            CastNumericResult::Float(v) => Ok(Value::Float(v)),
        },
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help(format!("only int, float, and bool can be cast to numeric types"));
            Err(CompileError::semantic_with_context(
                format!("type mismatch: cannot cast {} to {}", val.type_name(), target.name()),
                ctx,
            ))
        },
    }
}

fn cast_to_bool(val: Value) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => Ok(Value::Bool(bool_cast::from_int(i))),
        Value::Float(f) => Ok(Value::Bool(bool_cast::from_float(f))),
        Value::Bool(b) => Ok(Value::Bool(b)),
        Value::Str(ref s) => Ok(Value::Bool(bool_cast::from_str(s))),
        Value::Nil => Ok(Value::Bool(false)),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("only int, float, string, and nil can be cast to bool");
            Err(CompileError::semantic_with_context(
                format!("type mismatch: cannot cast {} to bool", val.type_name()),
                ctx,
            ))
        },
    }
}

fn cast_to_string(val: Value) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => Ok(Value::Str(string_cast::from_int(i))),
        Value::Float(f) => Ok(Value::Str(string_cast::from_float(f))),
        Value::Bool(b) => Ok(Value::Str(string_cast::from_bool(b))),
        Value::Str(s) => Ok(Value::Str(s)),
        Value::Symbol(s) => Ok(Value::Str(s)),
        Value::Nil => Ok(Value::Str("nil".to_string())),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("only int, float, bool, string, symbol, and nil can be cast to String");
            Err(CompileError::semantic_with_context(
                format!("type mismatch: cannot cast {} to String", val.type_name()),
                ctx,
            ))
        },
    }
}

use simple_parser::ast::Type;

use crate::error::CompileError;
use crate::value::Value;

// Value casting functions for interpreter_expr module

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
        _ => Err(CompileError::Semantic(format!(
            "unsupported cast target type: {:?}",
            target_type
        ))),
    }
}

/// Cast a value to a simple (named) type
fn cast_to_simple_type(val: Value, type_name: &str) -> Result<Value, CompileError> {
    match type_name {
        // Signed integers
        "i8" => cast_to_i8(val),
        "i16" => cast_to_i16(val),
        "i32" => cast_to_i32(val),
        "i64" | "int" => cast_to_i64(val),
        // Unsigned integers
        "u8" => cast_to_u8(val),
        "u16" => cast_to_u16(val),
        "u32" => cast_to_u32(val),
        "u64" => cast_to_u64(val),
        // Floating point
        "f32" => cast_to_f32(val),
        "f64" | "float" => cast_to_f64(val),
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
                Err(CompileError::Semantic(format!(
                    "cannot cast {} to {}",
                    actual_type, other
                )))
            }
        }
    }
}

fn cast_to_i8(val: Value) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => Ok(Value::Int(i as i8 as i64)),
        Value::Float(f) => Ok(Value::Int(f as i8 as i64)),
        Value::Bool(b) => Ok(Value::Int(if b { 1 } else { 0 })),
        _ => Err(CompileError::Semantic(format!("cannot cast {} to i8", val.type_name()))),
    }
}

fn cast_to_i16(val: Value) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => Ok(Value::Int(i as i16 as i64)),
        Value::Float(f) => Ok(Value::Int(f as i16 as i64)),
        Value::Bool(b) => Ok(Value::Int(if b { 1 } else { 0 })),
        _ => Err(CompileError::Semantic(format!(
            "cannot cast {} to i16",
            val.type_name()
        ))),
    }
}

fn cast_to_i32(val: Value) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => Ok(Value::Int(i as i32 as i64)),
        Value::Float(f) => Ok(Value::Int(f as i32 as i64)),
        Value::Bool(b) => Ok(Value::Int(if b { 1 } else { 0 })),
        _ => Err(CompileError::Semantic(format!(
            "cannot cast {} to i32",
            val.type_name()
        ))),
    }
}

fn cast_to_i64(val: Value) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => Ok(Value::Int(i)),
        Value::Float(f) => Ok(Value::Int(f as i64)),
        Value::Bool(b) => Ok(Value::Int(if b { 1 } else { 0 })),
        _ => Err(CompileError::Semantic(format!(
            "cannot cast {} to i64",
            val.type_name()
        ))),
    }
}

fn cast_to_u8(val: Value) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => Ok(Value::Int(i as u8 as i64)),
        Value::Float(f) => Ok(Value::Int(f as u8 as i64)),
        Value::Bool(b) => Ok(Value::Int(if b { 1 } else { 0 })),
        _ => Err(CompileError::Semantic(format!("cannot cast {} to u8", val.type_name()))),
    }
}

fn cast_to_u16(val: Value) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => Ok(Value::Int(i as u16 as i64)),
        Value::Float(f) => Ok(Value::Int(f as u16 as i64)),
        Value::Bool(b) => Ok(Value::Int(if b { 1 } else { 0 })),
        _ => Err(CompileError::Semantic(format!(
            "cannot cast {} to u16",
            val.type_name()
        ))),
    }
}

fn cast_to_u32(val: Value) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => Ok(Value::Int(i as u32 as i64)),
        Value::Float(f) => Ok(Value::Int(f as u32 as i64)),
        Value::Bool(b) => Ok(Value::Int(if b { 1 } else { 0 })),
        _ => Err(CompileError::Semantic(format!(
            "cannot cast {} to u32",
            val.type_name()
        ))),
    }
}

fn cast_to_u64(val: Value) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => Ok(Value::Int(i as u64 as i64)),
        Value::Float(f) => Ok(Value::Int(f as u64 as i64)),
        Value::Bool(b) => Ok(Value::Int(if b { 1 } else { 0 })),
        _ => Err(CompileError::Semantic(format!(
            "cannot cast {} to u64",
            val.type_name()
        ))),
    }
}

fn cast_to_f32(val: Value) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => Ok(Value::Float(i as f32 as f64)),
        Value::Float(f) => Ok(Value::Float(f as f32 as f64)),
        Value::Bool(b) => Ok(Value::Float(if b { 1.0 } else { 0.0 })),
        _ => Err(CompileError::Semantic(format!(
            "cannot cast {} to f32",
            val.type_name()
        ))),
    }
}

fn cast_to_f64(val: Value) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => Ok(Value::Float(i as f64)),
        Value::Float(f) => Ok(Value::Float(f)),
        Value::Bool(b) => Ok(Value::Float(if b { 1.0 } else { 0.0 })),
        _ => Err(CompileError::Semantic(format!(
            "cannot cast {} to f64",
            val.type_name()
        ))),
    }
}

fn cast_to_bool(val: Value) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => Ok(Value::Bool(i != 0)),
        Value::Float(f) => Ok(Value::Bool(f != 0.0)),
        Value::Bool(b) => Ok(Value::Bool(b)),
        Value::Str(s) => Ok(Value::Bool(!s.is_empty())),
        Value::Nil => Ok(Value::Bool(false)),
        _ => Err(CompileError::Semantic(format!(
            "cannot cast {} to bool",
            val.type_name()
        ))),
    }
}

fn cast_to_string(val: Value) -> Result<Value, CompileError> {
    match val {
        Value::Int(i) => Ok(Value::Str(i.to_string())),
        Value::Float(f) => Ok(Value::Str(f.to_string())),
        Value::Bool(b) => Ok(Value::Str(b.to_string())),
        Value::Str(s) => Ok(Value::Str(s)),
        Value::Symbol(s) => Ok(Value::Str(s)),
        Value::Nil => Ok(Value::Str("nil".to_string())),
        _ => Err(CompileError::Semantic(format!(
            "cannot cast {} to String",
            val.type_name()
        ))),
    }
}

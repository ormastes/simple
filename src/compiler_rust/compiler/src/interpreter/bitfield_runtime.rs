use std::collections::HashMap;
use std::sync::Arc;

use simple_parser::ast::BitfieldDef;

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;

use super::BITFIELDS;

pub(crate) fn register_bitfield(def: &BitfieldDef) {
    BITFIELDS.with(|cell| {
        cell.borrow_mut().insert(def.name.clone(), Arc::new(def.clone()));
    });
}

pub(crate) fn instantiate_bitfield(class_name: &str, args: &[Value]) -> Result<Value, CompileError> {
    let def = lookup_bitfield(class_name)?;
    let raw = if args.len() == 1 {
        value_as_u128(&args[0])?
    } else {
        let mut fields = HashMap::new();
        for (idx, field) in def.fields.iter().enumerate() {
            if let Some(value) = args.get(idx) {
                fields.insert(field.name.clone(), value.clone());
            }
        }
        encode_raw(&def, &fields)?
    };
    Ok(build_value(&def, raw))
}

pub(crate) fn update_bitfield_field(object: &Value, field: &str, value: Value) -> Option<Value> {
    let Value::Object { class, fields } = object else {
        return None;
    };
    let def = BITFIELDS.with(|cell| cell.borrow().get(class).cloned())?;
    if !def.fields.iter().any(|f| f.name == field) {
        return None;
    }

    let mut updated = (**fields).clone();
    updated.insert(field.to_string(), value);
    let raw = encode_raw(&def, &updated).ok()?;
    Some(build_value(&def, raw))
}

fn lookup_bitfield(class_name: &str) -> Result<Arc<BitfieldDef>, CompileError> {
    BITFIELDS.with(|cell| cell.borrow().get(class_name).cloned()).ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::UNKNOWN_CLASS)
            .with_help("check that the bitfield is defined in this scope");
        CompileError::semantic_with_context(format!("bitfield `{}` not found", class_name), ctx)
    })
}

fn value_as_u128(value: &Value) -> Result<u128, CompileError> {
    Ok(value.as_int()? as u128)
}

fn field_mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

fn encode_raw(def: &BitfieldDef, fields: &HashMap<String, Value>) -> Result<u128, CompileError> {
    let mut raw = 0u128;
    let mut offset = 0u32;
    for field in &def.fields {
        if let Some(value) = fields.get(&field.name) {
            let value = value_as_u128(value)? & field_mask(field.bits as u32);
            raw |= value << offset;
        }
        offset += field.bits as u32;
    }
    Ok(raw)
}

fn decode_fields(def: &BitfieldDef, raw: u128) -> HashMap<String, Value> {
    let mut fields = HashMap::new();
    let mut offset = 0u32;
    for field in &def.fields {
        let value = ((raw >> offset) & field_mask(field.bits as u32)) as i64;
        fields.insert(field.name.clone(), Value::Int(value));
        offset += field.bits as u32;
    }
    fields.insert("__raw".to_string(), Value::Int(raw as i64));
    fields
}

fn build_value(def: &BitfieldDef, raw: u128) -> Value {
    Value::Object {
        class: def.name.clone(),
        fields: Arc::new(decode_fields(def, raw)),
    }
}

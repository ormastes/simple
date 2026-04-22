use std::collections::HashMap;
use std::sync::Arc;

use simple_parser::ast::{Argument, BitfieldDef, FunctionDef};

use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::evaluate_expr;
use crate::value::{Env, NativeFnArc, NativeFunction, Value};

use super::super::{classes, Enums, ImplMethods, BITFIELDS};

fn bitfield_def(class_name: &str) -> Option<Arc<BitfieldDef>> {
    BITFIELDS.with(|cell| cell.borrow().get(class_name).cloned())
}

fn field_mask(width: u32) -> u128 {
    if width >= 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    }
}

fn value_as_u128(value: &Value) -> Result<u128, CompileError> {
    Ok(value.as_int()? as u128)
}

fn encode_raw(def: &BitfieldDef, fields: &HashMap<String, Value>) -> Result<u128, CompileError> {
    let mut raw = 0u128;
    for field in &def.fields {
        if let Some(value) = fields.get(&field.name) {
            let v = value_as_u128(value)? & field_mask(field.bits as u32);
            raw |= v << raw_offset(def, &field.name);
        }
    }
    Ok(raw)
}

fn raw_offset(def: &BitfieldDef, field_name: &str) -> u32 {
    let mut offset = 0u32;
    for field in &def.fields {
        if field.name == field_name {
            return offset;
        }
        offset += field.bits as u32;
    }
    0
}

fn decode_fields(def: &BitfieldDef, raw: u128) -> HashMap<String, Value> {
    let mut fields = HashMap::new();
    let mut offset = 0u32;
    for field in &def.fields {
        let mask = field_mask(field.bits as u32);
        let value = ((raw >> offset) & mask) as i64;
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

pub(crate) fn instantiate_bitfield_from_values(class_name: &str, values: &[Value]) -> Result<Value, CompileError> {
    let def = bitfield_def(class_name).ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::UNKNOWN_CLASS)
            .with_help("check that the bitfield is defined in this scope");
        CompileError::semantic_with_context(format!("bitfield `{}` not found", class_name), ctx)
    })?;

    if values.len() == 1 {
        return Ok(build_value(&def, value_as_u128(&values[0])?));
    }

    let mut fields = HashMap::new();
    for (idx, field) in def.fields.iter().enumerate() {
        if let Some(value) = values.get(idx) {
            fields.insert(field.name.clone(), value.clone());
        }
    }
    let raw = encode_raw(&def, &fields)?;
    Ok(build_value(&def, raw))
}

pub(crate) fn instantiate_bitfield_from_args(
    class_name: &str,
    args: &[Argument],
    env: &mut Env,
    functions: &mut HashMap<String, Arc<FunctionDef>>,
    classes: &mut HashMap<String, Arc<simple_parser::ast::ClassDef>>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    let mut values = Vec::with_capacity(args.len());
    let def = bitfield_def(class_name).ok_or_else(|| {
        let ctx = ErrorContext::new()
            .with_code(codes::UNKNOWN_CLASS)
            .with_help("check that the bitfield is defined in this scope");
        CompileError::semantic_with_context(format!("bitfield `{}` not found", class_name), ctx)
    })?;

    if args.len() == 1 && args[0].name.is_none() {
        let value = evaluate_expr(&args[0].value, env, functions, classes, enums, impl_methods)?;
        return Ok(build_value(&def, value_as_u128(&value)?));
    }

    let mut named: HashMap<String, Value> = HashMap::new();
    let mut positional_idx = 0usize;
    for arg in args {
        let value = evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)?;
        if let Some(name) = &arg.name {
            named.insert(name.clone(), value);
        } else if let Some(field) = def.fields.get(positional_idx) {
            named.insert(field.name.clone(), value);
            positional_idx += 1;
        } else {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_STRUCT_LITERAL)
                .with_help(format!("bitfield `{}` expects {} field(s)", class_name, def.fields.len()));
            return Err(CompileError::semantic_with_context(
                format!("too many arguments for bitfield `{}` constructor", class_name),
                ctx,
            ));
        }
    }

    let raw = encode_raw(&def, &named)?;
    values.push(build_value(&def, raw));
    Ok(values.remove(0))
}

pub(crate) fn bitfield_new_native(class_name: String) -> Value {
    let func: NativeFnArc = Arc::new(move |args: &[Value]| instantiate_bitfield_from_values(&class_name, args));
    Value::NativeFunction(NativeFunction {
        name: format!("{}.new", class_name),
        func,
    })
}

pub(crate) fn update_bitfield_field(object: &Value, field: &str, value: Value) -> Option<Value> {
    let Value::Object { class, fields } = object else {
        return None;
    };
    let def = bitfield_def(class)?;
    if !def.fields.iter().any(|f| f.name == field) {
        return None;
    }

    let mut new_fields = (**fields).clone();
    new_fields.insert(field.to_string(), value);
    let raw = encode_raw(&def, &new_fields).ok()?;
    let mut decoded = decode_fields(&def, raw);
    if let Some(updated) = new_fields.get(field) {
        decoded.insert(field.to_string(), updated.clone());
    }
    Some(Value::Object {
        class: class.clone(),
        fields: Arc::new(decoded),
    })
}

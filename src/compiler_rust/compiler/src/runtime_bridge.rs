//! Bridge between RuntimeValue and interpreter Values.
//!
//! This module provides conversion functions between RuntimeValue (used by compiled code)
//! and interpreter Value types. It also provides conversions through BridgeValue.

use simple_runtime::RuntimeValue;

use crate::value::Value;
use crate::value_bridge::{bridge_tags, BridgeValue};

// ============================================================================
// Conversion: RuntimeValue <-> BridgeValue
// ============================================================================

impl From<RuntimeValue> for BridgeValue {
    fn from(rv: RuntimeValue) -> Self {
        use simple_runtime::value::tags as rt_tags;

        match rv.tag() {
            rt_tags::TAG_INT => BridgeValue::int(rv.as_int()),
            rt_tags::TAG_FLOAT => BridgeValue::float(rv.as_float()),
            rt_tags::TAG_SPECIAL => {
                let payload = rv.payload();
                match payload {
                    rt_tags::SPECIAL_NIL => BridgeValue::nil(),
                    rt_tags::SPECIAL_TRUE => BridgeValue::bool(true),
                    rt_tags::SPECIAL_FALSE => BridgeValue::bool(false),
                    _ => BridgeValue::symbol(&format!("symbol_{}", payload)),
                }
            }
            rt_tags::TAG_HEAP => {
                // For heap objects, we'd need to decode the actual type
                // For now, return a placeholder
                BridgeValue {
                    tag: bridge_tags::OBJECT,
                    payload: rv.to_raw(),
                    extended: std::ptr::null_mut(),
                }
            }
            _ => BridgeValue::nil(),
        }
    }
}

impl From<BridgeValue> for RuntimeValue {
    fn from(bv: BridgeValue) -> Self {
        match bv.tag {
            bridge_tags::NIL => RuntimeValue::NIL,
            bridge_tags::INT => RuntimeValue::from_int(bv.payload as i64),
            bridge_tags::FLOAT => RuntimeValue::from_float(f64::from_bits(bv.payload)),
            bridge_tags::BOOL => RuntimeValue::from_bool(bv.payload != 0),
            // Complex types can't be directly converted to RuntimeValue
            // They need heap allocation which we don't do here
            _ => RuntimeValue::NIL,
        }
    }
}

// ============================================================================
// Direct Value <-> RuntimeValue conversion (for simple types)
// ============================================================================

/// Convert an interpreter Value to a RuntimeValue (simple types only)
pub fn value_to_runtime(v: &Value) -> RuntimeValue {
    match v {
        Value::Nil => RuntimeValue::NIL,
        Value::Int(i) => RuntimeValue::from_int(*i),
        Value::Float(f) => RuntimeValue::from_float(*f),
        Value::Bool(b) => RuntimeValue::from_bool(*b),
        // Complex types need heap allocation - return NIL for now
        _ => RuntimeValue::NIL,
    }
}

/// Convert a RuntimeValue to an interpreter Value (simple types only)
pub fn runtime_to_value(rv: RuntimeValue) -> Value {
    use simple_runtime::value::tags as rt_tags;

    match rv.tag() {
        rt_tags::TAG_INT => Value::Int(rv.as_int()),
        rt_tags::TAG_FLOAT => Value::Float(rv.as_float()),
        rt_tags::TAG_SPECIAL => {
            let payload = rv.payload();
            match payload {
                rt_tags::SPECIAL_NIL => Value::Nil,
                rt_tags::SPECIAL_TRUE => Value::Bool(true),
                rt_tags::SPECIAL_FALSE => Value::Bool(false),
                _ => Value::Symbol(format!("symbol_{}", payload)),
            }
        }
        rt_tags::TAG_HEAP => {
            // Decode heap objects
            use simple_runtime::value::{
                rt_array_get, rt_array_len, rt_string_data, rt_string_len, rt_tuple_get, rt_tuple_len, HeapObjectType,
            };

            let ptr = rv.as_heap_ptr();
            if ptr.is_null() {
                return Value::Nil;
            }

            // Read heap object type
            unsafe {
                let header = ptr.cast::<simple_runtime::value::HeapHeader>();
                let obj_type = (*header).object_type;

                match obj_type {
                    HeapObjectType::Array => {
                        // Decode array
                        let len = rt_array_len(rv) as usize;
                        let mut elements = Vec::with_capacity(len);

                        for i in 0..len {
                            let elem_rv = rt_array_get(rv, i as i64);
                            let elem_val = runtime_to_value(elem_rv);
                            elements.push(elem_val);
                        }

                        Value::Array(elements)
                    }
                    HeapObjectType::String => {
                        // Decode string
                        let len = rt_string_len(rv) as usize;
                        let data_ptr = rt_string_data(rv);

                        if data_ptr.is_null() || len == 0 {
                            Value::Str(String::new())
                        } else {
                            let slice = std::slice::from_raw_parts(data_ptr, len);
                            match std::str::from_utf8(slice) {
                                Ok(s) => Value::Str(s.to_string()),
                                Err(_) => Value::Nil,
                            }
                        }
                    }
                    HeapObjectType::Tuple => {
                        // Decode tuple
                        let len = rt_tuple_len(rv) as usize;
                        let mut elements = Vec::with_capacity(len);

                        for i in 0..len {
                            let elem_rv = rt_tuple_get(rv, i as u64);
                            let elem_val = runtime_to_value(elem_rv);
                            elements.push(elem_val);
                        }

                        Value::Tuple(elements)
                    }
                    _ => {
                        // Other heap types not yet supported
                        Value::Nil
                    }
                }
            }
        }
        _ => Value::Nil,
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_runtime_to_bridge_int() {
        let rv = RuntimeValue::from_int(42);
        let bv = BridgeValue::from(rv);
        assert_eq!(bv.as_int(), 42);
    }

    #[test]
    fn test_bridge_to_runtime_int() {
        let bv = BridgeValue::int(42);
        let rv = RuntimeValue::from(bv);
        assert_eq!(rv.as_int(), 42);
    }

    #[test]
    fn test_value_to_runtime_simple() {
        assert_eq!(value_to_runtime(&Value::Nil), RuntimeValue::NIL);
        assert_eq!(value_to_runtime(&Value::Int(42)).as_int(), 42);
        assert_eq!(value_to_runtime(&Value::Bool(true)), RuntimeValue::TRUE);
    }

    #[test]
    fn test_runtime_to_value_simple() {
        assert_eq!(runtime_to_value(RuntimeValue::NIL), Value::Nil);
        assert_eq!(runtime_to_value(RuntimeValue::from_int(42)), Value::Int(42));
        assert_eq!(runtime_to_value(RuntimeValue::TRUE), Value::Bool(true));
    }
}

//! Bridge between RuntimeValue and interpreter Values.
//!
//! This module provides conversion functions between RuntimeValue (used by compiled code)
//! and interpreter Value types. It also provides conversions through BridgeValue.

use simple_runtime::RuntimeValue;

use crate::value::{enum_names, Value};
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

/// Convert an interpreter Value to a RuntimeValue.
pub fn value_to_runtime(v: &Value) -> RuntimeValue {
    match v {
        Value::Nil => RuntimeValue::NIL,
        Value::Int(i) => RuntimeValue::from_int(*i),
        Value::UInt { value, .. } => RuntimeValue::from_int(*value as i64),
        Value::Float(f) => RuntimeValue::from_float(*f),
        Value::Float32(f) => RuntimeValue::from_float(*f as f64),
        Value::Bool(b) => RuntimeValue::from_bool(*b),
        Value::Str(s) => simple_runtime::value::rt_string_new(s.as_ptr(), s.len() as u64),
        Value::Symbol(s) => simple_runtime::value::rt_string_new(s.as_ptr(), s.len() as u64),
        Value::Array(items) | Value::FrozenArray(items) => values_to_runtime_array(items.iter()),
        Value::FixedSizeArray { data, .. } => values_to_runtime_array(data.iter()),
        // A tuple must marshal to a runtime tuple (not an array) so it is
        // byte-identical to a natively-constructed tuple and reads correctly via
        // `rt_tuple_get`/destructuring when an extern's tuple result is kept boxed
        // across the interpreter bridge (see compile_interp_call).
        Value::Tuple(data) => values_to_runtime_tuple(data.iter()),
        Value::LabeledTuple { values, .. } => values_to_runtime_array(values.iter()),
        // A Dict must marshal to a real native `RuntimeDict` heap object (not
        // NIL) so a composite (Dict/Map) return value that is forced through
        // the interpreter bridge (`InterpCall` — e.g. via a TryOperator or
        // PatternMatch fallback reason unrelated to the value's own type)
        // round-trips correctly to native `Dict.len()` / `Dict.contains_key()`
        // / indexing on the caller side.
        //
        // Root cause of the S68/S71 "composite-return InterpCall" gap: this
        // match had NO arm for `Value::Dict`/`Value::FrozenDict`, so it fell
        // through to the wildcard `_ => RuntimeValue::NIL` below, silently
        // discarding the entire dict. `compile_interp_call` in
        // codegen/instr/core.rs already keeps composite results boxed
        // correctly (no codegen change needed) — the corruption happened
        // upstream, here, before the boxed RuntimeValue was ever handed back
        // to compiled code. `rt_dict_len(NIL)` returns -1, matching the
        // originally reported symptom exactly.
        //
        // The interpreter's `Value::Dict` (`Arc<HashMap<String, Value>>`) and
        // the native `RuntimeDict` are separate heap allocations with
        // different memory layouts — there is no shared underlying object to
        // extract a pointer/tag from, so identity cannot be preserved across
        // this boundary. This is necessarily a copy (mirrors the existing
        // `values_to_runtime_array`/`values_to_runtime_tuple` marshaling
        // above), which is correct for a *return value*: the interpreter-side
        // dict is a fresh, uniquely-owned object with no other alias, so a
        // deep copy loses no shared-mutation semantics.
        Value::Dict(map) | Value::FrozenDict(map) => values_to_runtime_dict(map.iter()),
        Value::Enum {
            enum_name,
            variant,
            payload,
        } => {
            let (enum_id, discriminant) = if enum_name == enum_names::OPTION {
                let ordinal = match variant.as_str() {
                    enum_names::SOME => 0,
                    enum_names::NONE => 1,
                    _ => panic!("unsupported Option variant at runtime bridge: {variant}"),
                };
                (1, ordinal)
            } else if enum_name == enum_names::RESULT {
                match variant.as_str() {
                    enum_names::OK | enum_names::ERR => {}
                    _ => panic!("unsupported Result variant at runtime bridge: {variant}"),
                }
                (0, simple_runtime::value::hash_variant_discriminant(variant))
            } else {
                panic!("unsupported enum at runtime bridge: {enum_name}::{variant}")
            };
            let payload = payload.as_deref().map_or(RuntimeValue::NIL, value_to_runtime);
            simple_runtime::value::rt_enum_new(enum_id, discriminant, payload)
        }
        _ => RuntimeValue::NIL,
    }
}

fn values_to_runtime_tuple<'a>(items: impl IntoIterator<Item = &'a Value>) -> RuntimeValue {
    let values: Vec<RuntimeValue> = items.into_iter().map(value_to_runtime).collect();
    let tuple = simple_runtime::value::rt_tuple_new(values.len() as u64);
    if tuple == RuntimeValue::NIL {
        return RuntimeValue::NIL;
    }
    for (i, value) in values.into_iter().enumerate() {
        if !simple_runtime::value::rt_tuple_set(tuple, i as u64, value) {
            return RuntimeValue::NIL;
        }
    }
    tuple
}

/// Marshal an interpreter dict (`String` keys, arbitrary `Value` values) into
/// a native heap `RuntimeDict` via `rt_dict_new`/`rt_dict_set`, recursively
/// converting nested values through `value_to_runtime`. Dict keys are always
/// `String` on the interpreter side (`Value::Dict(Arc<HashMap<String, Value>>)`),
/// so each key is marshaled through `rt_string_new` to match the native
/// runtime's `RuntimeValue` key convention used by `rt_dict_get`/`rt_dict_set`.
fn values_to_runtime_dict<'a>(entries: impl IntoIterator<Item = (&'a String, &'a Value)>) -> RuntimeValue {
    let dict = simple_runtime::value::rt_dict_new(0);
    if dict == RuntimeValue::NIL {
        return RuntimeValue::NIL;
    }
    for (key, value) in entries {
        let key_rv = simple_runtime::value::rt_string_new(key.as_ptr(), key.len() as u64);
        let value_rv = value_to_runtime(value);
        if !simple_runtime::value::rt_dict_set(dict, key_rv, value_rv) {
            return RuntimeValue::NIL;
        }
    }
    dict
}

fn values_to_runtime_array<'a>(items: impl IntoIterator<Item = &'a Value>) -> RuntimeValue {
    let values: Vec<RuntimeValue> = items.into_iter().map(value_to_runtime).collect();
    let array = simple_runtime::value::rt_array_new(values.len() as u64);
    if array == RuntimeValue::NIL {
        return RuntimeValue::NIL;
    }
    for value in values {
        if !simple_runtime::value::rt_array_push(array, value) {
            return RuntimeValue::NIL;
        }
    }
    array
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

                        Value::array(elements)
                    }
                    HeapObjectType::String => {
                        // Decode string
                        let len = rt_string_len(rv) as usize;
                        let data_ptr = rt_string_data(rv);

                        if data_ptr.is_null() || len == 0 {
                            Value::text(String::new())
                        } else {
                            let slice = std::slice::from_raw_parts(data_ptr, len);
                            match std::str::from_utf8(slice) {
                                Ok(s) => Value::text(s.to_string()),
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
                    HeapObjectType::Dict => {
                        // Decode dict via rt_dict_entries (array of (key, value)
                        // tuples), the symmetric counterpart to
                        // `values_to_runtime_dict` above. Keys are expected to be
                        // strings (the interpreter's `Value::Dict` convention);
                        // a non-string native key falls back to its debug form
                        // rather than silently dropping the entry.
                        use simple_runtime::value::rt_dict_entries;

                        let entries = rt_dict_entries(rv);
                        let len = rt_array_len(entries) as usize;
                        let mut map = std::collections::HashMap::with_capacity(len);

                        for i in 0..len {
                            let pair = rt_array_get(entries, i as i64);
                            let key_rv = rt_tuple_get(pair, 0);
                            let value_rv = rt_tuple_get(pair, 1);
                            let key = match runtime_to_value(key_rv) {
                                Value::Str(s) => (*s).clone(),
                                other => format!("{:?}", other),
                            };
                            map.insert(key, runtime_to_value(value_rv));
                        }

                        Value::Dict(std::sync::Arc::new(map))
                    }
                    HeapObjectType::Enum => {
                        use simple_runtime::value::{
                            hash_variant_discriminant, rt_enum_discriminant, rt_enum_id, rt_enum_payload,
                        };

                        let enum_id = rt_enum_id(rv);
                        let discriminant = rt_enum_discriminant(rv) as u32;
                        if enum_id == 1 {
                            match discriminant {
                                0 => Value::Enum {
                                    enum_name: enum_names::OPTION.to_string(),
                                    variant: enum_names::SOME.to_string(),
                                    payload: Some(Box::new(runtime_to_value(rt_enum_payload(rv)))),
                                },
                                1 => Value::Enum {
                                    enum_name: enum_names::OPTION.to_string(),
                                    variant: enum_names::NONE.to_string(),
                                    payload: None,
                                },
                                _ => panic!("unsupported Option discriminant at runtime bridge: {discriminant}"),
                            }
                        } else if enum_id == 0 && discriminant == hash_variant_discriminant(enum_names::OK) {
                            Value::Enum {
                                enum_name: enum_names::RESULT.to_string(),
                                variant: enum_names::OK.to_string(),
                                payload: Some(Box::new(runtime_to_value(rt_enum_payload(rv)))),
                            }
                        } else if enum_id == 0 && discriminant == hash_variant_discriminant(enum_names::ERR) {
                            Value::Enum {
                                enum_name: enum_names::RESULT.to_string(),
                                variant: enum_names::ERR.to_string(),
                                payload: Some(Box::new(runtime_to_value(rt_enum_payload(rv)))),
                            }
                        } else {
                            panic!("unsupported runtime enum at bridge: id={enum_id}, discriminant={discriminant}")
                        }
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
    fn test_value_to_runtime_array() {
        let value = Value::array(vec![Value::Int(7), Value::Bool(true)]);
        let runtime = value_to_runtime(&value);

        assert_eq!(simple_runtime::value::rt_tuple_len(runtime), 2);
        assert_eq!(simple_runtime::value::rt_tuple_get(runtime, 0).as_int(), 7);
        assert_eq!(simple_runtime::value::rt_tuple_get(runtime, 1), RuntimeValue::TRUE);
    }

    #[test]
    fn test_value_to_runtime_tuple_is_runtime_tuple() {
        let runtime = value_to_runtime(&Value::Tuple(vec![Value::Int(3), Value::Int(4)]));

        assert_eq!(simple_runtime::value::rt_tuple_len(runtime), 2);
        assert_eq!(simple_runtime::value::rt_tuple_get(runtime, 0).as_int(), 3);
        assert_eq!(simple_runtime::value::rt_tuple_get(runtime, 1).as_int(), 4);
    }

    #[test]
    fn test_runtime_to_value_simple() {
        assert_eq!(runtime_to_value(RuntimeValue::NIL), Value::Nil);
        assert_eq!(runtime_to_value(RuntimeValue::from_int(42)), Value::Int(42));
        assert_eq!(runtime_to_value(RuntimeValue::TRUE), Value::Bool(true));
    }

    #[test]
    fn shared_text_runtime_roundtrip_preserves_unicode() {
        let value = Value::text("é🙂".to_string());
        let runtime = value_to_runtime(&value);
        assert_eq!(runtime_to_value(runtime), value);
    }

    // ========================================================================
    // S78: composite-return InterpCall gap (S68/S71 follow-up) regression tests
    //
    // Root cause: `value_to_runtime` had no arm for `Value::Dict`/`FrozenDict`,
    // so any Dict-returning function routed through the interpreter bridge
    // (`rt_interp_call` -> `interp_call_handler` -> `value_to_runtime`) had its
    // result silently collapsed to `RuntimeValue::NIL`. Downstream native
    // `Dict.len()` on NIL returns -1 (see `rt_dict_len`'s `as_typed_ptr!`
    // fallback), matching the originally reported symptom exactly.
    // ========================================================================

    #[test]
    fn value_to_runtime_dict_is_a_real_native_dict_not_nil() {
        use std::collections::HashMap;

        let mut map = HashMap::new();
        map.insert("a".to_string(), Value::Int(1));
        map.insert("b".to_string(), Value::Int(2));
        let value = Value::dict(map);

        let runtime = value_to_runtime(&value);

        // Before the fix this was RuntimeValue::NIL and rt_dict_len returned -1.
        assert_ne!(runtime, RuntimeValue::NIL, "Dict must not collapse to NIL");
        assert_eq!(simple_runtime::value::rt_dict_len(runtime), 2);
    }

    #[test]
    fn value_to_runtime_dict_values_are_readable_by_key() {
        use std::collections::HashMap;

        let mut map = HashMap::new();
        map.insert("name".to_string(), Value::text("simple"));
        map.insert("count".to_string(), Value::Int(42));
        let value = Value::dict(map);

        let runtime = value_to_runtime(&value);

        let key = "count";
        let key_rv = simple_runtime::value::rt_string_new(key.as_ptr(), key.len() as u64);
        assert!(simple_runtime::value::rt_dict_contains(runtime, key_rv));
        assert_eq!(simple_runtime::value::rt_dict_get(runtime, key_rv).as_int(), 42);
    }

    #[test]
    fn value_to_runtime_dict_with_nested_composite_values_round_trips() {
        use std::collections::HashMap;

        let mut map = HashMap::new();
        map.insert(
            "items".to_string(),
            Value::array(vec![Value::Int(1), Value::Int(2), Value::Int(3)]),
        );
        let value = Value::dict(map);

        let runtime = value_to_runtime(&value);
        assert_eq!(simple_runtime::value::rt_dict_len(runtime), 1);

        let key = "items";
        let key_rv = simple_runtime::value::rt_string_new(key.as_ptr(), key.len() as u64);
        let nested = simple_runtime::value::rt_dict_get(runtime, key_rv);
        assert_eq!(simple_runtime::value::rt_array_len(nested), 3);
    }

    #[test]
    fn dict_runtime_to_value_roundtrip() {
        use std::collections::HashMap;

        let mut map = HashMap::new();
        map.insert("x".to_string(), Value::Int(10));
        map.insert("y".to_string(), Value::text("hello"));
        let value = Value::dict(map);

        let runtime = value_to_runtime(&value);
        let back = runtime_to_value(runtime);

        match (&value, &back) {
            (Value::Dict(a), Value::Dict(b)) => {
                assert_eq!(a.len(), b.len());
                for (k, v) in a.iter() {
                    assert_eq!(b.get(k), Some(v));
                }
            }
            other => panic!("expected Dict round-trip, got {:?}", other),
        }
    }

    #[test]
    fn frozen_dict_also_marshals_to_native_dict() {
        use std::collections::HashMap;
        use std::sync::Arc;

        let mut map = HashMap::new();
        map.insert("k".to_string(), Value::Bool(true));
        let value = Value::FrozenDict(Arc::new(map));

        let runtime = value_to_runtime(&value);
        assert_ne!(runtime, RuntimeValue::NIL);
        assert_eq!(simple_runtime::value::rt_dict_len(runtime), 1);
    }

    #[test]
    fn option_bridge_uses_canonical_id_and_ordinals() {
        let some = Value::Enum {
            enum_name: enum_names::OPTION.to_string(),
            variant: enum_names::SOME.to_string(),
            payload: Some(Box::new(Value::Int(3))),
        };
        let none = Value::Enum {
            enum_name: enum_names::OPTION.to_string(),
            variant: enum_names::NONE.to_string(),
            payload: None,
        };

        let some_runtime = value_to_runtime(&some);
        let none_runtime = value_to_runtime(&none);
        assert_eq!(simple_runtime::value::rt_enum_id(some_runtime), 1);
        assert_eq!(simple_runtime::value::rt_enum_discriminant(some_runtime), 0);
        assert_eq!(simple_runtime::value::rt_enum_payload(some_runtime).as_int(), 3);
        assert_eq!(simple_runtime::value::rt_enum_id(none_runtime), 1);
        assert_eq!(simple_runtime::value::rt_enum_discriminant(none_runtime), 1);
        assert_eq!(runtime_to_value(some_runtime), some);
        assert_eq!(runtime_to_value(none_runtime), none);
    }

    #[test]
    fn result_bridge_keeps_hashed_variants() {
        let ok = Value::Enum {
            enum_name: enum_names::RESULT.to_string(),
            variant: enum_names::OK.to_string(),
            payload: Some(Box::new(Value::Int(7))),
        };
        assert_eq!(runtime_to_value(value_to_runtime(&ok)), ok);
    }

    #[test]
    #[should_panic(expected = "unsupported Option variant at runtime bridge")]
    fn malformed_option_fails_loudly() {
        let malformed = Value::Enum {
            enum_name: enum_names::OPTION.to_string(),
            variant: "Maybe".to_string(),
            payload: None,
        };
        let _ = value_to_runtime(&malformed);
    }

    #[test]
    #[should_panic(expected = "unsupported runtime enum at bridge")]
    fn unknown_runtime_enum_fails_loudly() {
        let unknown = simple_runtime::value::rt_enum_new(99, 7, RuntimeValue::NIL);
        let _ = runtime_to_value(unknown);
    }
}

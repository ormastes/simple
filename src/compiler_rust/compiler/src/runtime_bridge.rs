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
        // A user-defined Enum (including the built-in Option/Result specials)
        // must marshal to a real native `RuntimeEnum` heap object (via
        // `rt_enum_new`) instead of collapsing to NIL, for exactly the same
        // "composite value forced through InterpCall" reason as Dict above
        // (S68/S71/S78 -> S82 follow-up). Native pattern-matching
        // (`MirPattern::Variant` in `compile_pattern_test`,
        // codegen/src/codegen/instr/pattern.rs:70-85) and `rt_is_none`/
        // `rt_is_some` (runtime/src/value/objects.rs:322,342) dispatch ONLY
        // on `rt_enum_discriminant` -- a hash of the *variant name* alone
        // (`hash_variant_discriminant`, runtime/src/value/objects.rs:251-257,
        // byte-identical to `calculate_variant_discriminant` in
        // codegen/instr/pattern.rs:118-124 and `variant_disc` in
        // codegen/instr/result.rs:12-19) -- never on `enum_id`. Confirmed
        // empirically: `compile_enum_unit`/`compile_enum_with`
        // (codegen/instr/pattern.rs:126-154, the path used for ALL
        // non-Option/Result enum construction) hardcode `enum_id = 0`
        // unconditionally, and `rt_option_map` (runtime/src/value/objects.rs:372)
        // hardcodes `enum_id = 0` when re-wrapping a fresh `Some`, even
        // though `create_enum_value` (codegen/instr/result.rs:80) uses
        // `enum_id = 1` for Option specifically -- i.e. `enum_id` is already
        // inconsistent/unused for correctness in the pre-existing native
        // codegen, so this marshal is safe reusing discriminant-only
        // identity. `enum_id` below matches the native convention (1 for
        // Option, 0 otherwise) purely for parity, not because anything reads
        // it downstream.
        Value::Enum {
            enum_name, variant, payload,
        } => {
            let discriminant = simple_runtime::value::hash_variant_discriminant(variant);
            let enum_id: u32 = if enum_name == enum_names::OPTION { 1 } else { 0 };
            let payload_rv = match payload {
                Some(inner) => value_to_runtime(inner),
                None => RuntimeValue::NIL,
            };
            simple_runtime::value::rt_enum_new(enum_id, discriminant, payload_rv)
        }
        // A class/struct instance (`Value::Object`) has NO sound marshaling
        // path at this bridge layer -- this is the registry gap S78 flagged
        // ("no class-id registry lookup exists"), now root-caused precisely:
        // native `compile_struct_init` (codegen/instr/closures_structs.rs:
        // 206-248) does NOT use the `RuntimeObject`/`rt_object_new`
        // heap-header representation (runtime/src/value/objects.rs:90-114)
        // for class instances AT ALL. It `rt_alloc`s a raw block and writes
        // fields at compile-time-baked-in byte offsets (`field_offsets`),
        // tagging the pointer with the bare `TAG_HEAP` bit (heap_tag = 1,
        // closures_structs.rs:245-246) and NO `HeapHeader`/`HeapObjectType`
        // prefix whatsoever. There is no runtime-queryable "class name/id ->
        // field layout" registry anywhere in this codebase -- the layout is
        // a compiler-internal fact baked directly into each call site's MIR
        // (`MirInst::StructInit { field_offsets, field_types, .. }`) and
        // never round-trips through a table this bridge could consult. Even
        // producing a `RuntimeObject` via `rt_object_new` would be actively
        // unsound: downstream native code for this class expects the bare
        // offset-based layout, not the `RuntimeObject` header+class_id+
        // field_count preamble, so a real conversion would misalign every
        // field read on the native side. Per the S82 mandate: converting the
        // previous SILENT `_ => RuntimeValue::NIL` collapse into a LOUD
        // failure here (rather than leaving the corruption undetected). See
        // the registry-gap writeup in
        // doc/08_tracking/bug/s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18.md.
        Value::Object { class, .. } => {
            panic!(
                "runtime_bridge::value_to_runtime: cannot marshal interpreter Value::Object of class `{class}` \
                 to a native RuntimeValue -- no class-id -> native field-layout registry exists at the \
                 interpreter/native bridge boundary (native compile_struct_init bakes field offsets into \
                 codegen call sites at compile time; there is no runtime-queryable class layout table). \
                 Silently returning NIL would corrupt downstream native field access; failing loudly instead. \
                 See doc/08_tracking/bug/s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18.md \
                 for the registry-gap writeup."
            );
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
                        // Symmetric decode for the `Value::Enum` marshal in
                        // `value_to_runtime` above. The discriminant is a
                        // one-way hash of the variant name alone
                        // (`hash_variant_discriminant`,
                        // runtime/src/value/objects.rs:251), so only the
                        // well-known built-in Option/Result discriminants can
                        // be reversed back to a concrete (enum_name, variant)
                        // pair -- there is no reverse discriminant -> name
                        // registry for arbitrary user-defined enums (the same
                        // registry gap noted for Object below; discriminant
                        // hash collisions with a user enum variant literally
                        // named "Some"/"None"/"Ok"/"Err" are a pre-existing
                        // ambiguity of the whole discriminant-hash scheme,
                        // not something introduced here).
                        use simple_runtime::value::{hash_variant_discriminant, rt_enum_discriminant, rt_enum_payload};

                        let discriminant = rt_enum_discriminant(rv) as u32;
                        let some_d = hash_variant_discriminant(enum_names::SOME);
                        let none_d = hash_variant_discriminant(enum_names::NONE);
                        let ok_d = hash_variant_discriminant(enum_names::OK);
                        let err_d = hash_variant_discriminant(enum_names::ERR);

                        if discriminant == some_d {
                            Value::Enum {
                                enum_name: enum_names::OPTION.to_string(),
                                variant: enum_names::SOME.to_string(),
                                payload: Some(Box::new(runtime_to_value(rt_enum_payload(rv)))),
                            }
                        } else if discriminant == none_d {
                            Value::Enum {
                                enum_name: enum_names::OPTION.to_string(),
                                variant: enum_names::NONE.to_string(),
                                payload: None,
                            }
                        } else if discriminant == ok_d {
                            Value::Enum {
                                enum_name: enum_names::RESULT.to_string(),
                                variant: enum_names::OK.to_string(),
                                payload: Some(Box::new(runtime_to_value(rt_enum_payload(rv)))),
                            }
                        } else if discriminant == err_d {
                            Value::Enum {
                                enum_name: enum_names::RESULT.to_string(),
                                variant: enum_names::ERR.to_string(),
                                payload: Some(Box::new(runtime_to_value(rt_enum_payload(rv)))),
                            }
                        } else {
                            panic!(
                                "runtime_bridge::runtime_to_value: cannot decode native RuntimeEnum with \
                                 discriminant {discriminant:#x} back to an interpreter Value::Enum -- the \
                                 discriminant is a one-way hash of the variant name and there is no reverse \
                                 discriminant -> (enum_name, variant) registry for user-defined enums beyond \
                                 the well-known Option/Result cases. Silently returning Nil would corrupt \
                                 downstream interpreter logic; failing loudly instead. See \
                                 doc/08_tracking/bug/s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18.md."
                            );
                        }
                    }
                    HeapObjectType::Object => {
                        // See the `Value::Object` loud-failure note in
                        // `value_to_runtime` above -- same registry gap,
                        // opposite direction. `compile_struct_init`
                        // (codegen/instr/closures_structs.rs:206-248) never
                        // produces a real `HeapObjectType::Object`/
                        // `RuntimeObject` value on the native cranelift path
                        // (it uses a bare `TAG_HEAP`-tagged offset struct with
                        // no header at all), so reaching this arm at runtime
                        // means either (a) a genuine `rt_object_new`-
                        // constructed RuntimeObject from a non-codegen
                        // producer, or (b) a native tagged-struct pointer
                        // whose first bytes coincidentally decode as
                        // `HeapObjectType::Object` -- in neither case can
                        // this bridge recover the class-id -> field-name
                        // mapping needed to build a faithful
                        // `Value::Object { class, fields }`.
                        let class_id = simple_runtime::value::rt_object_class_id(rv);
                        panic!(
                            "runtime_bridge::runtime_to_value: cannot decode native RuntimeObject \
                             (class_id={class_id}) back to an interpreter Value::Object -- no class-id -> \
                             field-name registry exists at the interpreter/native bridge boundary. Silently \
                             returning Nil would corrupt downstream interpreter logic; failing loudly instead. \
                             See doc/08_tracking/bug/s68_cranelift_interpcall_boxed_result_generic_return_gap_2026-07-18.md."
                        );
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

    // ========================================================================
    // S82: Enum/Option marshaling (S68/S71/S78 follow-up) regression tests
    //
    // Root cause (same shape as the Dict gap S78 fixed): `value_to_runtime`
    // had no arm for `Value::Enum`, so any Option/Result/user-enum-returning
    // function routed through the interpreter bridge had its result silently
    // collapsed to `RuntimeValue::NIL`. Downstream native `rt_is_none`/
    // `rt_enum_discriminant`/pattern-matching on NIL all read garbage.
    // ========================================================================

    #[test]
    fn value_to_runtime_option_some_is_a_real_native_enum_not_nil() {
        let value = Value::Enum {
            enum_name: enum_names::OPTION.to_string(),
            variant: enum_names::SOME.to_string(),
            payload: Some(Box::new(Value::Int(42))),
        };

        let runtime = value_to_runtime(&value);

        // Before the fix this was RuntimeValue::NIL (rt_is_none == true, wrongly).
        assert_ne!(runtime, RuntimeValue::NIL, "Some(42) must not collapse to NIL");
        assert!(simple_runtime::value::rt_is_some(runtime));
        assert_eq!(simple_runtime::value::rt_enum_payload(runtime).as_int(), 42);
    }

    #[test]
    fn value_to_runtime_option_none_is_recognized_as_none_discriminant() {
        let value = Value::Enum {
            enum_name: enum_names::OPTION.to_string(),
            variant: enum_names::NONE.to_string(),
            payload: None,
        };

        let runtime = value_to_runtime(&value);

        // None must be a real tagged enum whose discriminant native pattern
        // matching / `rt_is_some` recognizes as the "None" variant -- not a
        // bare untagged NIL and not a silently-wrong Some.
        assert!(!simple_runtime::value::rt_is_some(runtime));
        let none_disc = simple_runtime::value::hash_variant_discriminant(enum_names::NONE) as i64;
        assert_eq!(simple_runtime::value::rt_enum_discriminant(runtime), none_disc);
    }

    #[test]
    fn value_to_runtime_result_ok_and_err_round_trip_discriminant() {
        let ok = Value::Enum {
            enum_name: enum_names::RESULT.to_string(),
            variant: enum_names::OK.to_string(),
            payload: Some(Box::new(Value::text("done"))),
        };
        let err = Value::Enum {
            enum_name: enum_names::RESULT.to_string(),
            variant: enum_names::ERR.to_string(),
            payload: Some(Box::new(Value::text("boom"))),
        };

        let ok_rv = value_to_runtime(&ok);
        let err_rv = value_to_runtime(&err);

        assert_ne!(
            simple_runtime::value::rt_enum_discriminant(ok_rv),
            simple_runtime::value::rt_enum_discriminant(err_rv)
        );
        assert_ne!(ok_rv, RuntimeValue::NIL);
        assert_ne!(err_rv, RuntimeValue::NIL);
    }

    #[test]
    fn option_some_runtime_to_value_roundtrip() {
        let value = Value::Enum {
            enum_name: enum_names::OPTION.to_string(),
            variant: enum_names::SOME.to_string(),
            payload: Some(Box::new(Value::Int(7))),
        };

        let runtime = value_to_runtime(&value);
        let back = runtime_to_value(runtime);

        assert_eq!(value, back);
    }

    #[test]
    fn option_none_runtime_to_value_roundtrip() {
        let value = Value::Enum {
            enum_name: enum_names::OPTION.to_string(),
            variant: enum_names::NONE.to_string(),
            payload: None,
        };

        let runtime = value_to_runtime(&value);
        let back = runtime_to_value(runtime);

        assert_eq!(value, back);
    }

    #[test]
    fn result_ok_err_runtime_to_value_roundtrip() {
        let ok = Value::Enum {
            enum_name: enum_names::RESULT.to_string(),
            variant: enum_names::OK.to_string(),
            payload: Some(Box::new(Value::Int(1))),
        };
        let err = Value::Enum {
            enum_name: enum_names::RESULT.to_string(),
            variant: enum_names::ERR.to_string(),
            payload: Some(Box::new(Value::text("nope"))),
        };

        assert_eq!(runtime_to_value(value_to_runtime(&ok)), ok);
        assert_eq!(runtime_to_value(value_to_runtime(&err)), err);
    }

    #[test]
    fn value_to_runtime_dict_with_nested_option_round_trips() {
        // The bootstrap-critical case flagged in the S71 audit:
        // Dict<text, SomeEnum> values (e.g. process_async()'s
        // Dict<text, AsyncStateMachine>-shaped payloads) must not collapse
        // their Enum-typed values to NIL merely because they are nested
        // inside an already-fixed Dict.
        use std::collections::HashMap;

        let mut map = HashMap::new();
        map.insert(
            "maybe".to_string(),
            Value::Enum {
                enum_name: enum_names::OPTION.to_string(),
                variant: enum_names::SOME.to_string(),
                payload: Some(Box::new(Value::Int(99))),
            },
        );
        let value = Value::dict(map);

        let runtime = value_to_runtime(&value);
        assert_eq!(simple_runtime::value::rt_dict_len(runtime), 1);

        let key = "maybe";
        let key_rv = simple_runtime::value::rt_string_new(key.as_ptr(), key.len() as u64);
        let nested = simple_runtime::value::rt_dict_get(runtime, key_rv);

        assert_ne!(nested, RuntimeValue::NIL, "nested Option must not collapse to NIL");
        assert!(simple_runtime::value::rt_is_some(nested));
        assert_eq!(simple_runtime::value::rt_enum_payload(nested).as_int(), 99);
    }

    // ========================================================================
    // S82: Value::Object -- no sound native layout lookup exists at this
    // bridge boundary (see the in-code writeup on the `Value::Object` arm in
    // `value_to_runtime`). Assert the silent-NIL collapse is now a LOUD
    // failure instead, per the S82 mandate.
    // ========================================================================

    #[test]
    #[should_panic(expected = "cannot marshal interpreter Value::Object")]
    fn value_to_runtime_object_panics_loudly_instead_of_silently_nil() {
        use std::collections::HashMap;
        use std::sync::Arc;

        let value = Value::Object {
            class: "Point".to_string(),
            fields: Arc::new(HashMap::new()),
        };

        let _ = value_to_runtime(&value);
    }

    #[test]
    #[should_panic(expected = "cannot decode native RuntimeObject")]
    fn runtime_to_value_object_panics_loudly_instead_of_silently_nil() {
        let object_rv = simple_runtime::value::rt_object_new(7, 0);
        let _ = runtime_to_value(object_rv);
    }

    #[test]
    #[should_panic(expected = "cannot decode native RuntimeEnum")]
    fn runtime_to_value_unknown_enum_discriminant_panics_loudly_instead_of_silently_nil() {
        // A user-defined enum variant whose name is not Some/None/Ok/Err --
        // the discriminant->name direction genuinely cannot be recovered
        // (see the in-code writeup on the `HeapObjectType::Enum` arm in
        // `runtime_to_value`), so this must fail loudly rather than return a
        // silently-wrong Nil.
        let disc = simple_runtime::value::hash_variant_discriminant("Red");
        let enum_rv = simple_runtime::value::rt_enum_new(0, disc, RuntimeValue::NIL);
        let _ = runtime_to_value(enum_rv);
    }
}

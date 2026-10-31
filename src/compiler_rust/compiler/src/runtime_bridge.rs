//! Bridge between RuntimeValue and interpreter Values.
//!
//! This module provides conversion functions between RuntimeValue (used by compiled code)
//! and interpreter Value types. It also provides conversions through BridgeValue.

use simple_runtime::RuntimeValue;

use crate::codegen::shared::enum_runtime_type_id;
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

/// Convert an interpreter Value to a RuntimeValue (one level; see `value_to_runtime`).
fn value_to_runtime_inner(v: &Value) -> RuntimeValue {
    match v {
        Value::Nil => RuntimeValue::NIL,
        Value::Int(i) => RuntimeValue::from_int(*i),
        Value::UInt { value, .. } => RuntimeValue::from_u64(*value),
        Value::Float(f) => RuntimeValue::from_float(*f),
        Value::Float32(f) => RuntimeValue::from_float(*f as f64),
        Value::Bool(b) => RuntimeValue::from_bool(*b),
        Value::Str(s) => simple_runtime::value::rt_string_new(s.as_ptr(), s.len() as u64),
        Value::Symbol(s) => simple_runtime::value::rt_string_new(s.as_ptr(), s.len() as u64),
        Value::Array(items) | Value::FrozenArray(items) => values_to_runtime_array(items.iter()),
        Value::FixedSizeArray { data, .. } => values_to_runtime_array(data.iter()),
        // Packed `[u8]` (`rt_bytes_alloc` and the other runtime byte
        // allocators) is the same `[u8]` as a boxed array of `u8` values and
        // must cross the bridge as one. It used to fall through to the `NIL`
        // wildcard below, so a JIT'd `var a = rt_bytes_alloc(4)` read
        // `a.len() == 0` and the next `a[i] = b` stored through NIL and
        // crashed with SIGSEGV
        // (doc/08_tracking/bug/packed_byte_array_write_span_noop_2026-10-05.md).
        Value::ByteArray(bytes) | Value::FrozenByteArray(bytes) => {
            values_to_runtime_array(Value::byte_array_values(bytes).iter())
        }
        // A tuple must marshal to a runtime tuple (not an array) so it is
        // byte-identical to a natively-constructed tuple and reads correctly via
        // `rt_tuple_get`/destructuring when an extern's tuple result is kept boxed
        // across the interpreter bridge (see compile_interp_call).
        Value::Tuple(data) => values_to_runtime_tuple(data.iter()),
        Value::LabeledTuple { values, .. } => values_to_runtime_array(values.iter()),
        // Enum values cross the interpreter/native boundary as the same boxed
        // RuntimeEnum ABI used by native constructors and match checks. Type
        // IDs come from the shared helper: Option and Result have reserved IDs,
        // while user enum names retain the established hash-based identity.
        Value::Enum {
            enum_name,
            variant,
            payload,
        } => simple_runtime::value::rt_enum_new(
            enum_runtime_type_id(enum_name),
            simple_runtime::value::hash_variant_discriminant(variant),
            payload.as_deref().map_or(RuntimeValue::NIL, value_to_runtime),
        ),
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
        // Struct values and class instances used to fall through to the
        // wildcard below, so an instance crossing rt_interp_call (argument or
        // result) arrived on the other side as nil. They now marshal to a
        // native `RuntimeObject` whose class id names a registered layout
        // (class name + field order); see `object_bridge` below.
        Value::Object { class, fields } => object_bridge::struct_to_runtime(class, fields),
        Value::ClassInstance(instance) => object_bridge::class_to_runtime(instance),
        // A trait object is not unwrapped here: rebuilding it on the way back
        // would need the trait name, which the object layout does not carry.
        // It stays an explicit, documented NIL rather than a silent wildcard.
        Value::TraitObject { .. } => RuntimeValue::NIL,
        _ => RuntimeValue::NIL,
    }
}

/// Marshal an interpreter value to a runtime value at the top of a bridge
/// crossing. Nested values recurse through `value_to_runtime_inner` so the
/// per-crossing alias/cycle memo lives exactly as long as one crossing.
pub fn value_to_runtime(v: &Value) -> RuntimeValue {
    object_bridge::with_crossing(|| value_to_runtime_inner(v))
}

/// Convert a RuntimeValue to an interpreter Value at the top of a bridge
/// crossing (see `value_to_runtime`).
pub fn runtime_to_value(rv: RuntimeValue) -> Value {
    object_bridge::with_crossing(|| runtime_to_value_inner(rv))
}

/// Class instances and struct values across the interpreter <-> native
/// boundary.
///
/// Native representation: a `RuntimeObject` (`rt_object_new`) whose fields
/// hold the marshaled field values in the registered layout order. Class ids
/// at or above `CLASS_ID_BASE` are assigned here; each names a
/// `(class name, ordered field names, carrier)` layout in a process-global
/// registry (marshal-out and marshal-in can run on different threads). Any
/// other class id, or a field count that disagrees with the layout, decodes
/// to nil exactly as before, so foreign RuntimeObjects are never misread.
///
/// Semantics: VALUE semantics for both structs (`Value::Object`) and classes
/// (`Value::ClassInstance`) -- classes are value types
/// (doc/07_guide/language/capability_library_authoring.md; see
/// doc/08_tracking/bug/jit_class_instances_alias_instead_of_copy_2026-09-27.md).
/// Every crossing deep-copies: a mutation on either side after the crossing
/// is not visible on the other, and a native `rt_object_field_set` is seen by
/// the copy decoded from that object. No identity token or instance registry
/// exists, so nothing is kept alive and the result never depends on timing.
///
/// Cycles / aliasing: within ONE crossing, an instance already being
/// marshaled maps to the object already allocated for it (allocated before
/// its fields are filled), so a self-reference terminates and two aliases of
/// one instance inside one value become one object; decoding mirrors this
/// keyed by object address, which is stable for the duration of the crossing.
/// The memo is cleared when the outermost crossing ends.
///
/// Registry bound: one entry per distinct (class name, field-name set,
/// carrier) ever marshaled. Field sets are fixed by class/struct definitions,
/// so the size is bounded by the program's type count; as a hard backstop the
/// registry refuses new layouts beyond `MAX_LAYOUTS` (the value then marshals
/// to nil, the pre-existing behaviour) rather than growing without limit.
mod object_bridge {
    use std::cell::{Cell, RefCell};
    use std::collections::HashMap;
    use std::sync::{Arc, LazyLock, Mutex};

    use simple_runtime::value::{rt_object_class_id, rt_object_field_count, rt_object_field_get, rt_object_field_set};
    use simple_runtime::RuntimeValue;

    use super::{runtime_to_value_inner, value_to_runtime_inner};
    use crate::value::{ClassInstance, Value};

    /// First class id owned by the bridge; far above any id the runtime or
    /// codegen hands out.
    pub(super) const CLASS_ID_BASE: u32 = 0x7000_0000;
    /// Hard cap on registered layouts (see module docs).
    pub(super) const MAX_LAYOUTS: usize = 1 << 16;

    #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
    enum Carrier {
        Struct,
        Class,
    }

    #[derive(Clone)]
    struct Layout {
        class: String,
        fields: Arc<Vec<String>>,
        carrier: Carrier,
    }

    #[derive(Default)]
    struct Registry {
        layouts: Vec<Layout>,
        ids: HashMap<(String, Vec<String>, Carrier), u32>,
    }

    static REGISTRY: LazyLock<Mutex<Registry>> = LazyLock::new(|| Mutex::new(Registry::default()));

    fn intern_layout(class: &str, fields: Vec<String>, carrier: Carrier) -> Option<(u32, Layout)> {
        let mut reg = REGISTRY.lock().unwrap_or_else(|e| e.into_inner());
        let key = (class.to_string(), fields, carrier);
        if let Some(&id) = reg.ids.get(&key) {
            return Some((id, reg.layouts[(id - CLASS_ID_BASE) as usize].clone()));
        }
        if reg.layouts.len() >= MAX_LAYOUTS {
            return None;
        }
        let id = CLASS_ID_BASE + reg.layouts.len() as u32;
        let layout = Layout {
            class: key.0.clone(),
            fields: Arc::new(key.1.clone()),
            carrier,
        };
        reg.layouts.push(layout.clone());
        reg.ids.insert(key, id);
        Some((id, layout))
    }

    fn layout_of(class_id: i64) -> Option<Layout> {
        let id = u32::try_from(class_id).ok()?;
        let index = id.checked_sub(CLASS_ID_BASE)? as usize;
        let reg = REGISTRY.lock().unwrap_or_else(|e| e.into_inner());
        reg.layouts.get(index).cloned()
    }

    // ---- per-crossing memo -----------------------------------------------

    thread_local! {
        static DEPTH: Cell<usize> = const { Cell::new(0) };
        /// Arc<ClassInstance> address -> object allocated for it (marshal-out).
        static OUT_MEMO: RefCell<HashMap<usize, RuntimeValue>> = RefCell::new(HashMap::new());
        /// RuntimeObject raw value -> instance rebuilt from it (marshal-in).
        static IN_MEMO: RefCell<HashMap<u64, Arc<ClassInstance>>> = RefCell::new(HashMap::new());
    }

    /// Run one bridge crossing. Nested public calls share the outer memo; the
    /// memo is cleared when the outermost crossing ends (also on unwind), so
    /// no RuntimeValue or Arc is held across crossings.
    pub(super) fn with_crossing<R>(f: impl FnOnce() -> R) -> R {
        struct Guard;
        impl Drop for Guard {
            fn drop(&mut self) {
                let depth = DEPTH.with(|d| {
                    let next = d.get() - 1;
                    d.set(next);
                    next
                });
                if depth == 0 {
                    OUT_MEMO.with(|m| m.borrow_mut().clear());
                    IN_MEMO.with(|m| m.borrow_mut().clear());
                }
            }
        }
        DEPTH.with(|d| d.set(d.get() + 1));
        let _guard = Guard;
        f()
    }

    fn sorted_names(fields: &HashMap<String, Value>) -> Vec<String> {
        let mut names: Vec<String> = fields.keys().cloned().collect();
        names.sort();
        names
    }

    /// Allocate the object for `fields`; `before_fill` runs after allocation
    /// and before the fields are filled (used to memoize class instances).
    fn object_to_runtime(
        class: &str,
        fields: &HashMap<String, Value>,
        carrier: Carrier,
        before_fill: impl FnOnce(RuntimeValue),
    ) -> RuntimeValue {
        let Some((id, layout)) = intern_layout(class, sorted_names(fields), carrier) else {
            return RuntimeValue::NIL;
        };
        let object = simple_runtime::value::rt_object_new(id, layout.fields.len() as u32);
        if object.is_nil() {
            return RuntimeValue::NIL;
        }
        before_fill(object);
        for (i, name) in layout.fields.iter().enumerate() {
            let value = fields.get(name).map_or(RuntimeValue::NIL, value_to_runtime_inner);
            if !rt_object_field_set(object, i as u32, value) {
                return RuntimeValue::NIL;
            }
        }
        object
    }

    pub(super) fn struct_to_runtime(class: &str, fields: &HashMap<String, Value>) -> RuntimeValue {
        object_to_runtime(class, fields, Carrier::Struct, |_| {})
    }

    pub(super) fn class_to_runtime(instance: &Arc<ClassInstance>) -> RuntimeValue {
        let addr = Arc::as_ptr(instance) as usize;
        if let Some(existing) = OUT_MEMO.with(|m| m.borrow().get(&addr).copied()) {
            return existing;
        }
        // Snapshot under the read lock, then release it before recursing: a
        // self-referencing field must not re-enter the lock.
        let fields = instance.fields_snapshot();
        let object = object_to_runtime(instance.class(), &fields, Carrier::Class, |object| {
            OUT_MEMO.with(|m| m.borrow_mut().insert(addr, object));
        });
        if object.is_nil() {
            OUT_MEMO.with(|m| m.borrow_mut().remove(&addr));
        }
        object
    }

    /// Decode a `HeapObjectType::Object`. Unregistered ids and layout
    /// mismatches decode to nil.
    pub(super) fn runtime_to_object(rv: RuntimeValue) -> Value {
        let Some(layout) = layout_of(rt_object_class_id(rv)) else {
            return Value::Nil;
        };
        if rt_object_field_count(rv) != layout.fields.len() as i64 {
            return Value::Nil;
        }
        match layout.carrier {
            Carrier::Struct => {
                let mut fields = HashMap::with_capacity(layout.fields.len());
                for (i, name) in layout.fields.iter().enumerate() {
                    fields.insert(name.clone(), runtime_to_value_inner(rt_object_field_get(rv, i as u32)));
                }
                Value::Object {
                    class: layout.class.clone(),
                    fields: Arc::new(fields),
                }
            }
            Carrier::Class => {
                let raw = rv.to_raw();
                if let Some(existing) = IN_MEMO.with(|m| m.borrow().get(&raw).cloned()) {
                    return Value::ClassInstance(existing);
                }
                let instance = Arc::new(ClassInstance::new(layout.class.clone(), HashMap::new()));
                IN_MEMO.with(|m| m.borrow_mut().insert(raw, instance.clone()));
                for (i, name) in layout.fields.iter().enumerate() {
                    let value = runtime_to_value_inner(rt_object_field_get(rv, i as u32));
                    instance.set_field(name.clone(), value);
                }
                Value::ClassInstance(instance)
            }
        }
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

/// Convert a RuntimeValue to an interpreter Value (one level; see `runtime_to_value`).
fn runtime_to_value_inner(rv: RuntimeValue) -> Value {
    use simple_runtime::value::tags as rt_tags;

    // Full-precision floats use HeapObjectType::Float at erased/Any/container
    // boundaries. Checking only TAG_FLOAT below silently converted every such
    // value to Value::Nil through the unsupported-heap fallback. This surfaced
    // in the self-hosted compiler when FloatLit/Json Number pattern payloads
    // crossed rt_interp_call before ast_semantic_value called f64_to_bits.
    if rv.is_float() {
        return Value::Float(rv.as_float());
    }
    // Wide signed integers use the adjacent HeapObjectType::Int carrier. Keep
    // that scalar distinct from HeapUInt and from enum/object wrappers.
    if let Some(value) = rv.as_heap_i64() {
        return Value::Int(value);
    }

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
                    HeapObjectType::UInt => Value::UInt {
                        value: rv.as_heap_u64().expect("HeapUInt type must carry a u64 payload"),
                        width: 64,
                    },
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
                    HeapObjectType::Object => object_bridge::runtime_to_object(rv),
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

        // An ARRAY marshals to a runtime ARRAY, so it is read with the array
        // accessors, not the tuple ones. `value_to_runtime` deliberately splits
        // the two (see the `Value::Tuple` arm comment above) so a tuple is
        // byte-identical to a natively constructed tuple;
        // `test_value_to_runtime_tuple_is_runtime_tuple` below covers that side.
        // The tuple accessors used here reported -1 on an array.
        assert_eq!(simple_runtime::value::rt_array_len(runtime), 2);
        assert_eq!(simple_runtime::value::rt_array_get(runtime, 0).as_int(), 7);
        assert_eq!(simple_runtime::value::rt_array_get(runtime, 1), RuntimeValue::TRUE);
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
    fn value_to_runtime_enum_uses_the_native_hashed_enum_abi() {
        use simple_runtime::value::{
            hash_variant_discriminant, rt_enum_discriminant, rt_enum_id, rt_enum_payload, HeapObjectType,
        };

        let value = Value::Enum {
            enum_name: "Option".to_string(),
            variant: "Some".to_string(),
            payload: Some(Box::new(Value::Int(42))),
        };
        let runtime = value_to_runtime(&value);

        assert_eq!(runtime.heap_type(), Some(HeapObjectType::Enum));
        assert_eq!(rt_enum_id(runtime), i64::from(enum_runtime_type_id("Option")));
        assert_eq!(rt_enum_discriminant(runtime), i64::from(hash_variant_discriminant("Some")));
        assert_eq!(rt_enum_payload(runtime).as_int(), 42);
    }

    #[test]
    fn value_to_runtime_enum_marshals_result_ok() {
        use simple_runtime::value::{hash_variant_discriminant, rt_enum_discriminant, rt_enum_id, rt_enum_payload};

        let runtime = value_to_runtime(&Value::Enum {
            enum_name: "Result".to_string(),
            variant: "Ok".to_string(),
            payload: Some(Box::new(Value::Int(17))),
        });

        assert_eq!(rt_enum_id(runtime), i64::from(enum_runtime_type_id("Result")));
        assert_eq!(rt_enum_discriminant(runtime), i64::from(hash_variant_discriminant("Ok")));
        assert_eq!(rt_enum_payload(runtime).as_int(), 17);
    }

    #[test]
    fn value_to_runtime_enum_preserves_none_err_and_nested_payloads() {
        use simple_runtime::value::{hash_variant_discriminant, rt_enum_discriminant, rt_enum_id, rt_enum_payload};

        let none = Value::Enum {
            enum_name: "Option".to_string(),
            variant: "None".to_string(),
            payload: None,
        };
        let none_runtime = value_to_runtime(&none);
        assert_eq!(rt_enum_id(none_runtime), i64::from(enum_runtime_type_id("Option")));
        assert_eq!(rt_enum_discriminant(none_runtime), i64::from(hash_variant_discriminant("None")));
        assert_eq!(rt_enum_payload(none_runtime), RuntimeValue::NIL);

        let nested = Value::Enum {
            enum_name: "Result".to_string(),
            variant: "Err".to_string(),
            payload: Some(Box::new(Value::Enum {
                enum_name: "Option".to_string(),
                variant: "Some".to_string(),
                payload: Some(Box::new(Value::text("payload".to_string()))),
            })),
        };
        let runtime = value_to_runtime(&nested);
        assert_eq!(rt_enum_id(runtime), i64::from(enum_runtime_type_id("Result")));
        assert_eq!(rt_enum_discriminant(runtime), i64::from(hash_variant_discriminant("Err")));
        let nested_runtime = rt_enum_payload(runtime);
        assert_eq!(rt_enum_id(nested_runtime), i64::from(enum_runtime_type_id("Option")));
        assert_eq!(rt_enum_discriminant(nested_runtime), i64::from(hash_variant_discriminant("Some")));
        assert_eq!(runtime_to_value(rt_enum_payload(nested_runtime)), Value::text("payload".to_string()));
    }

    #[test]
    fn enum_marshalling_retains_the_existing_user_enum_collision_contract() {
        use simple_runtime::value::rt_enum_id;

        let first = value_to_runtime(&Value::Enum {
            enum_name: "collision.Type175882".to_string(),
            variant: "Same".to_string(),
            payload: None,
        });
        let second = value_to_runtime(&Value::Enum {
            enum_name: "collision.Type255081".to_string(),
            variant: "Same".to_string(),
            payload: None,
        });

        assert_eq!(enum_runtime_type_id("collision.Type175882"), enum_runtime_type_id("collision.Type255081"));
        assert_eq!(rt_enum_id(first), rt_enum_id(second));
    }

    #[test]
    fn high_bit_u64_runtime_roundtrip_is_lossless_and_remains_unsigned() {
        for value in [0, 7, 1u64 << 61, 1u64 << 63, u64::MAX] {
            let source = Value::UInt { value, width: 64 };
            let runtime = value_to_runtime(&source);
            assert_eq!(runtime.as_heap_u64(), Some(value));
            assert_eq!(runtime_to_value(runtime), source);
        }
    }

    #[test]
    fn heap_boxed_float_runtime_roundtrip_preserves_exact_bits() {
        for value in [0.0, -0.0, 0.1, f64::MIN_POSITIVE, f64::MAX] {
            let runtime = RuntimeValue::from_float(value);
            assert_eq!(runtime.heap_type(), Some(simple_runtime::value::HeapObjectType::Float));
            match runtime_to_value(runtime) {
                Value::Float(actual) => assert_eq!(actual.to_bits(), value.to_bits()),
                other => panic!("expected exact Float bridge value, got {other:?}"),
            }
        }
    }

    #[test]
    fn heap_boxed_wide_signed_int_runtime_roundtrip_stays_int() {
        for value in [i64::MIN, -(1i64 << 61), 1i64 << 61, i64::MAX] {
            let runtime = RuntimeValue::from_int(value);
            assert_eq!(runtime.heap_type(), Some(simple_runtime::value::HeapObjectType::Int));
            assert_eq!(runtime_to_value(runtime), Value::Int(value));
        }
    }

    #[test]
    fn enum_wrapper_is_not_implicitly_coerced_to_its_float_payload() {
        use simple_runtime::value::{rt_enum_new, rt_enum_payload};

        let payload = RuntimeValue::from_float(0.1);
        let wrapper = rt_enum_new(77, 3, payload);
        assert_eq!(runtime_to_value(wrapper), Value::Nil);
        match runtime_to_value(rt_enum_payload(wrapper)) {
            Value::Float(actual) => assert_eq!(actual.to_bits(), 0.1f64.to_bits()),
            other => panic!("explicit enum payload extraction lost float: {other:?}"),
        }
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
    fn value_to_runtime_packed_bytes_are_a_real_array_not_nil() {
        for value in [Value::byte_array(vec![1, 2, 255]), Value::frozen_byte_array(vec![1, 2, 255])] {
            let runtime = value_to_runtime(&value);
            assert_ne!(runtime, RuntimeValue::NIL, "packed [u8] must not collapse to NIL");
            assert_eq!(simple_runtime::value::rt_array_len(runtime), 3);
            // Same marshalling as a boxed [u8] of u8 values.
            let boxed = value_to_runtime(&Value::array(Value::byte_array_values(&[1, 2, 255])));
            for i in 0..3 {
                assert_eq!(
                    simple_runtime::value::rt_array_get(runtime, i),
                    simple_runtime::value::rt_array_get(boxed, i),
                    "element {i}"
                );
            }
        }
    }

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

    // ---- class instances / struct values (were marshaled to NIL) ---------

    use crate::value::ClassInstance;
    use std::collections::HashMap;
    use std::sync::Arc;

    fn fields(pairs: Vec<(&str, Value)>) -> HashMap<String, Value> {
        pairs.into_iter().map(|(k, v)| (k.to_string(), v)).collect()
    }

    fn class_value(class: &str, pairs: Vec<(&str, Value)>) -> (Arc<ClassInstance>, Value) {
        let inst = Arc::new(ClassInstance::new(class.to_string(), fields(pairs)));
        (inst.clone(), Value::ClassInstance(inst))
    }

    #[test]
    fn struct_value_round_trips_name_and_nested_fields() {
        use simple_runtime::value::HeapObjectType;
        let value = Value::Object {
            class: "Point".to_string(),
            fields: Arc::new(fields(vec![
                ("x", Value::Int(3)),
                ("label", Value::text("p".to_string())),
                ("tags", Value::array(vec![Value::Int(1), Value::Int(2)])),
                (
                    "meta",
                    Value::Dict(Arc::new(fields(vec![("k", Value::Int(9))]))),
                ),
            ])),
        };
        let runtime = value_to_runtime(&value);
        assert_ne!(runtime, RuntimeValue::NIL, "struct must not marshal to nil");
        assert_eq!(runtime.heap_type(), Some(HeapObjectType::Object));
        let back = runtime_to_value(runtime);
        let Value::Object { class, fields: f } = &back else {
            panic!("expected Value::Object, got {back:?}")
        };
        assert_eq!(class, "Point");
        assert_eq!(f.get("x"), Some(&Value::Int(3)));
        assert_eq!(f.get("label"), Some(&Value::text("p".to_string())));
        assert_eq!(f.len(), 4);
        match f.get("tags") {
            Some(Value::Array(items)) => assert_eq!(items.len(), 2),
            other => panic!("tags lost: {other:?}"),
        }
        // (Enum fields are not asserted: runtime_to_value has no
        // HeapObjectType::Enum decoder yet, independent of this bridge.)
        match f.get("meta") {
            Some(Value::Dict(d)) => assert_eq!(d.get("k"), Some(&Value::Int(9))),
            other => panic!("meta lost: {other:?}"),
        }
    }

    #[test]
    fn struct_values_have_value_semantics_across_the_bridge() {
        let inner = Arc::new(fields(vec![("n", Value::Int(1))]));
        let value = Value::Object {
            class: "Box".to_string(),
            fields: inner.clone(),
        };
        let back = runtime_to_value(value_to_runtime(&value));
        match back {
            Value::Object { fields: f, .. } => assert!(!Arc::ptr_eq(&f, &inner), "struct must be a copy"),
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn class_instance_round_trip_is_a_value_copy_preserving_name_and_fields() {
        let (inst, value) = class_value("Counter", vec![("count", Value::Int(7)), ("name", Value::text("c".to_string()))]);
        let runtime = value_to_runtime(&value);
        assert_ne!(runtime, RuntimeValue::NIL, "class instance must not marshal to nil");
        let back = match runtime_to_value(runtime) {
            Value::ClassInstance(back) => back,
            other => panic!("expected ClassInstance, got {other:?}"),
        };
        assert!(!Arc::ptr_eq(&back, &inst), "classes are value types: crossing copies");
        assert_eq!(back.class(), "Counter");
        assert_eq!(back.field("count"), Some(Value::Int(7)));
        assert_eq!(back.field("name"), Some(Value::text("c".to_string())));
        // A later interpreter-side mutation does not reach the crossed copy...
        inst.set_field("count".to_string(), Value::Int(8));
        assert_eq!(back.field("count"), Some(Value::Int(7)));
        // ...nor the native object (sorted fields ["count", "name"] -> slot 0).
        assert_eq!(runtime_to_value(simple_runtime::value::rt_object_field_get(runtime, 0)), Value::Int(7));
        // A native write is visible in the copy decoded afterwards.
        assert!(simple_runtime::value::rt_object_field_set(runtime, 0, RuntimeValue::from_int(42)));
        match runtime_to_value(runtime) {
            Value::ClassInstance(again) => {
                assert_eq!(again.field("count"), Some(Value::Int(42)));
                assert!(!Arc::ptr_eq(&again, &back));
            }
            other => panic!("{other:?}"),
        }
        assert_eq!(inst.field("count"), Some(Value::Int(8)), "native write must not reach the original");
    }

    #[test]
    fn equal_class_copies_are_natively_structurally_equal() {
        let (_a, va) = class_value("Pt", vec![("x", Value::Int(1)), ("y", Value::Int(2))]);
        let (_b, vb) = class_value("Pt", vec![("x", Value::Int(1)), ("y", Value::Int(2))]);
        let (_c, vc) = class_value("Pt", vec![("x", Value::Int(1)), ("y", Value::Int(3))]);
        let ra = value_to_runtime(&va);
        let rb = value_to_runtime(&vb);
        let rc = value_to_runtime(&vc);
        assert_ne!(ra, rb, "separate allocations");
        assert_eq!(simple_runtime::value::rt_value_eq(ra, rb), 1);
        assert_eq!(simple_runtime::value::rt_value_eq(ra, rc), 0);
        // Two crossings of one instance are equal copies.
        assert_eq!(simple_runtime::value::rt_value_eq(ra, value_to_runtime(&va)), 1);
    }

    #[test]
    fn class_round_trip_works_from_two_threads() {
        let handles: Vec<_> = (0..2i64)
            .map(|t| {
                std::thread::spawn(move || {
                    for i in 0..200i64 {
                        let (_inst, value) = class_value(
                            if t == 0 { "ThreadA" } else { "ThreadB" },
                            vec![("i", Value::Int(i)), ("t", Value::Int(t))],
                        );
                        match runtime_to_value(value_to_runtime(&value)) {
                            Value::ClassInstance(back) => {
                                assert_eq!(back.field("i"), Some(Value::Int(i)));
                                assert_eq!(back.field("t"), Some(Value::Int(t)));
                            }
                            other => panic!("{other:?}"),
                        }
                    }
                })
            })
            .collect();
        for h in handles {
            h.join().expect("thread panicked");
        }
    }

    #[test]
    fn self_referencing_class_instance_terminates_and_keeps_the_cycle() {
        let (inst, value) = class_value("Node", vec![("id", Value::Int(1))]);
        inst.set_field("next".to_string(), value.clone());
        let runtime = value_to_runtime(&value);
        // Break the interpreter cycle so the test does not leak the Arc.
        inst.set_field("next".to_string(), Value::Nil);
        assert_ne!(runtime, RuntimeValue::NIL);
        // Native side: the `next` slot (sorted ["id", "next"] -> 1) is the same object.
        assert_eq!(simple_runtime::value::rt_object_field_get(runtime, 1), runtime);
        // Decoding the native cycle terminates and yields one copied instance.
        match runtime_to_value(runtime) {
            Value::ClassInstance(back) => {
                assert!(!Arc::ptr_eq(&back, &inst));
                match back.field("next") {
                    Some(Value::ClassInstance(n)) => assert!(Arc::ptr_eq(&n, &back)),
                    other => panic!("next lost: {other:?}"),
                }
                back.set_field("next".to_string(), Value::Nil); // break cycle
            }
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn two_aliases_of_one_instance_marshal_to_one_object() {
        let (_inst, value) = class_value("Shared", vec![("v", Value::Int(1))]);
        let runtime = value_to_runtime(&Value::array(vec![value.clone(), value.clone()]));
        let a = simple_runtime::value::rt_array_get(runtime, 0);
        let b = simple_runtime::value::rt_array_get(runtime, 1);
        assert_eq!(a, b, "two aliases inside one crossing become one object");
        assert_ne!(a, RuntimeValue::NIL);
        // A separate crossing is a separate copy.
        assert_ne!(value_to_runtime(&value), a);
    }

    #[test]
    fn class_inside_struct_and_struct_inside_class_round_trip() {
        let (inst, class_v) = class_value("Owner", vec![("k", Value::Int(2))]);
        let s = Value::Object {
            class: "Holder".to_string(),
            fields: Arc::new(fields(vec![("owner", class_v.clone())])),
        };
        match runtime_to_value(value_to_runtime(&s)) {
            Value::Object { class, fields: f } => {
                assert_eq!(class, "Holder");
                match f.get("owner") {
                    Some(Value::ClassInstance(o)) => {
                        assert!(!Arc::ptr_eq(o, &inst));
                        assert_eq!(o.field("k"), Some(Value::Int(2)));
                    }
                    other => panic!("{other:?}"),
                }
            }
            other => panic!("{other:?}"),
        }
        inst.set_field("pt".to_string(), s);
        match runtime_to_value(value_to_runtime(&class_v)) {
            Value::ClassInstance(o) => assert!(matches!(o.field("pt"), Some(Value::Object { .. }))),
            other => panic!("{other:?}"),
        }
        inst.set_field("pt".to_string(), Value::Nil); // break the Arc cycle
    }

    #[test]
    fn foreign_runtime_objects_still_decode_to_nil() {
        // A RuntimeObject whose class id the bridge never registered.
        let foreign = simple_runtime::value::rt_object_new(7, 1);
        assert_eq!(runtime_to_value(foreign), Value::Nil);
        let unregistered = simple_runtime::value::rt_object_new(0x7fff_fff0, 1);
        assert_eq!(runtime_to_value(unregistered), Value::Nil);
    }
}

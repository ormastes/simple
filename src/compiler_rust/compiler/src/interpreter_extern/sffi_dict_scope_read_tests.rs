use super::*;
use simple_runtime::value::{rt_array_get, rt_array_len, rt_string_new, RuntimeString};
use std::collections::HashMap;
use std::sync::Arc;

const BOUND: &str = "rt_dict_scope_read_bound_v1";
const OWNER: &str = "rt_dict_scope_read_owner_v1";
const EPOCH: &str = "rt_dict_scope_read_epoch_v1";
const META: &str = "rt_dict_scope_read_meta_v1";
const SLOT: &str = "rt_dict_scope_read_slot_v1";

fn dispatch(name: &str, args: &[Value]) -> Result<Value, CompileError> {
    let handler = super::super::EXTERN_DISPATCH
        .get(name)
        .expect("scope reader must have explicit dispatch");
    handler(
        args,
        &mut crate::value::Env::new(),
        &mut HashMap::new(),
        &mut HashMap::new(),
        &HashMap::new(),
        &HashMap::new(),
    )
}

fn scalar(name: &str, values: &[i64]) -> i64 {
    let args: Vec<_> = values.iter().map(|value| Value::Int(*value)).collect();
    let Value::Int(result) = dispatch(name, &args).unwrap() else {
        panic!("scope reader result must be scalar Int");
    };
    result
}

fn encoded(value: RuntimeValue) -> Value {
    Value::Int(value.to_raw() as i64)
}

fn set(handle: i64, name: &str, value: i64) {
    let key = rt_string_new(name.as_ptr(), name.len() as u64);
    assert_eq!(
        rt_dict_set_fn(&[Value::Int(handle), encoded(key), encoded(RuntimeValue::from_int(value))]).unwrap(),
        Value::Bool(true)
    );
}

fn scope() -> (i64, i64, i64, i64) {
    let Value::Int(handle) = rt_dict_new_fn(&[Value::Int(8)]).unwrap() else {
        panic!("existing dict creation must issue encoded raw handle");
    };
    for id in 0..20 {
        set(handle, &format!("binding-{id}"), id);
    }
    set(handle, "café猫", i64::MAX);
    let fuel = scalar(BOUND, &[]);
    assert_eq!(fuel, rt_dict_scope_read_bound_v1());
    let owner = scalar(OWNER, &[handle, fuel]);
    assert!(owner > 0);
    let epoch = scalar(EPOCH, &[handle, owner, fuel]);
    assert!(epoch > 0);
    (handle, owner, epoch, fuel)
}

#[test]
fn scope_read_raw_handle_dispatch_preserves_order_utf8_and_wide_ids() {
    let (handle, owner, epoch, fuel) = scope();
    assert_eq!(scalar(META, &[handle, owner, epoch, 0, fuel]), 3);
    assert_eq!(scalar(META, &[handle, owner, epoch, 1, fuel]), 21);
    let capacity = scalar(META, &[handle, owner, epoch, 3, fuel]);
    let Value::Int(keys) = rt_dict_keys_fn(&[Value::Int(handle)]).unwrap() else {
        panic!("raw dict keys must remain raw");
    };
    let keys = RuntimeValue::from_raw(keys as u64);
    let mut ordinal = 0;
    let mut saw_wide_utf8 = false;
    for slot in 0..capacity {
        let occupancy = scalar(SLOT, &[handle, owner, epoch, slot, 0, 0, fuel]);
        assert!((0..=1).contains(&occupancy));
        if occupancy == 0 {
            continue;
        }
        let key = rt_array_get(keys, ordinal);
        let text = unsafe { &*(key.as_heap_ptr() as *const RuntimeString) };
        assert_eq!(scalar(SLOT, &[handle, owner, epoch, slot, 2, 0, fuel]), text.len as i64);
        for (byte, expected) in unsafe { text.as_bytes() }.iter().enumerate() {
            assert_eq!(
                scalar(SLOT, &[handle, owner, epoch, slot, 3, byte as i64, fuel]),
                *expected as i64
            );
        }
        if unsafe { text.as_bytes() } == "café猫".as_bytes() {
            assert_eq!(scalar(SLOT, &[handle, owner, epoch, slot, 1, 0, fuel]), i64::MAX);
            saw_wide_utf8 = true;
        }
        ordinal += 1;
    }
    assert_eq!(ordinal, rt_array_len(keys));
    assert!(saw_wide_utf8);
}

#[test]
fn scope_read_dispatch_refuses_stale_invalid_and_nonint_values() {
    let (handle, owner, epoch, fuel) = scope();
    let capacity = scalar(META, &[handle, owner, epoch, 3, fuel]);
    let slot = (0..capacity)
        .find(|slot| scalar(SLOT, &[handle, owner, epoch, *slot, 0, 0, fuel]) == 1)
        .unwrap();
    let calls = [
        (OWNER, vec![handle, fuel]),
        (EPOCH, vec![handle, owner, fuel]),
        (META, vec![handle, owner, epoch, 0, fuel]),
        (SLOT, vec![handle, owner, epoch, slot, 0, 0, fuel]),
    ];
    for (name, scalars) in &calls {
        for bad_fuel in [0, fuel - 1] {
            let mut under = scalars.clone();
            *under.last_mut().unwrap() = bad_fuel;
            assert_eq!(scalar(name, &under), -1);
        }
        let mut forged = scalars.clone();
        forged[0] = 0x1005;
        assert_eq!(scalar(name, &forged), -1);
        for index in 0..scalars.len() {
            let mut args: Vec<_> = scalars.iter().map(|value| Value::Int(*value)).collect();
            for invalid in [Value::Bool(true), Value::Float(1.0), Value::Nil, Value::text("scalar")] {
                args[index] = invalid;
                assert_eq!(dispatch(name, &args).unwrap(), Value::Int(-1));
            }
        }
    }
    assert_eq!(scalar(EPOCH, &[handle, owner + 1, fuel]), -1);
    assert_eq!(scalar(META, &[handle, owner, epoch + 1, 0, fuel]), -1);
    assert_eq!(scalar(SLOT, &[handle, owner, epoch, capacity, 0, 0, fuel]), -1);
    set(handle, "binding-0", 999);
    assert_eq!(scalar(META, &[handle, owner, epoch, 0, fuel]), -1);
    let current = scalar(EPOCH, &[handle, owner, fuel]);
    assert!(current > epoch);
    assert_eq!(scalar(META, &[handle, owner, current, 1, fuel]), 21);
}

#[test]
fn scope_read_dispatch_rich_dicts_refuse_without_heap_materialization_and_arity_errors() {
    let fuel = scalar(BOUND, &[]); // Initialize actual registered dispatch before measuring.
    let map = Arc::new(HashMap::from([("binding".to_string(), Value::Int(42))]));
    for rich in [Value::Dict(map.clone()), Value::FrozenDict(map.clone())] {
        for (name, arity) in [(OWNER, 2), (EPOCH, 3), (META, 5), (SLOT, 7)] {
            let mut args = vec![Value::Int(1); arity];
            args[0] = rich.clone();
            *args.last_mut().unwrap() = Value::Int(fuel);
            let shares = Arc::strong_count(&map);
            let before = simple_runtime::value::heap::rt_heap_alloc_count();
            assert_eq!(dispatch(name, &args).unwrap(), Value::Int(-1));
            assert_eq!(simple_runtime::value::heap::rt_heap_alloc_count(), before);
            assert_eq!(Arc::strong_count(&map), shares);
        }
    }
    for (name, arity) in [(BOUND, 0), (OWNER, 2), (EPOCH, 3), (META, 5), (SLOT, 7)] {
        assert!(dispatch(name, &vec![Value::Int(1); arity + 1]).is_err());
        if arity > 0 {
            assert!(dispatch(name, &vec![Value::Int(1); arity - 1]).is_err());
        }
    }
}

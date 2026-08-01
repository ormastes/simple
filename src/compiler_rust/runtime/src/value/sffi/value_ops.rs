//! Value creation, extraction, and type checking implemented directly in Rust.

use crate::value::core::RuntimeValue;
use crate::value::tags;

#[no_mangle]
pub extern "C" fn rt_value_int(i: i64) -> RuntimeValue {
    RuntimeValue::from_int(i)
}
#[no_mangle]
pub extern "C" fn rt_value_float(f: f64) -> RuntimeValue {
    RuntimeValue::from_float(f)
}
#[no_mangle]
pub extern "C" fn rt_value_bool(b: bool) -> RuntimeValue {
    RuntimeValue::from_bool(b)
}
#[no_mangle]
pub extern "C" fn rt_value_nil() -> RuntimeValue {
    RuntimeValue::NIL
}
#[no_mangle]
pub extern "C" fn rt_value_as_int(v: RuntimeValue) -> i64 {
    v.as_int()
}
#[no_mangle]
pub extern "C" fn rt_value_as_float(v: RuntimeValue) -> f64 {
    v.as_float()
}
#[no_mangle]
pub extern "C" fn rt_value_as_bool(v: RuntimeValue) -> bool {
    v.as_bool()
}
#[no_mangle]
pub extern "C" fn rt_value_truthy(v: RuntimeValue) -> bool {
    v.truthy()
}
/// Coerce a boxed RuntimeValue to a raw machine i64 with a full-width return.
/// Used by the InterpCall bridge to hand interpreter results back to compiled
/// code whose destination is a raw bool/int register (bool -> 0/1, nil -> 0).
#[no_mangle]
pub extern "C" fn rt_value_raw_i64(v: RuntimeValue) -> i64 {
    if v.is_int() {
        v.as_int()
    } else if v.is_bool() {
        i64::from(v.as_bool())
    } else if v.is_float() {
        v.as_float() as i64
    } else {
        0
    }
}
#[no_mangle]
pub extern "C" fn rt_value_is_nil(v: RuntimeValue) -> bool {
    v.is_nil()
}
#[no_mangle]
pub extern "C" fn rt_value_is_int(v: RuntimeValue) -> bool {
    v.is_int()
}
#[no_mangle]
pub extern "C" fn rt_value_is_float(v: RuntimeValue) -> bool {
    v.is_float()
}
#[no_mangle]
pub extern "C" fn rt_value_is_bool(v: RuntimeValue) -> bool {
    v.is_bool()
}
#[no_mangle]
pub extern "C" fn rt_value_is_heap(v: RuntimeValue) -> bool {
    v.is_heap()
}
#[no_mangle]
pub extern "C" fn rt_value_type_tag(v: RuntimeValue) -> u8 {
    v.tag() as u8
}
#[no_mangle]
pub extern "C" fn rt_is_error(v: RuntimeValue) -> bool {
    v.tag() == tags::TAG_SPECIAL && v.payload() == tags::SPECIAL_ERROR
}

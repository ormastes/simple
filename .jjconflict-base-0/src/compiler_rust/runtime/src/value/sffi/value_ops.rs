//! Value creation, extraction, and type checking implemented directly in Rust.

use crate::value::core::RuntimeValue;
use crate::value::tags;

#[inline(always)]
pub fn rt_value_int(i: i64) -> RuntimeValue {
    RuntimeValue::from_int(i)
}
#[inline(always)]
pub fn rt_value_float(f: f64) -> RuntimeValue {
    RuntimeValue::from_float(f)
}
#[inline(always)]
pub fn rt_value_bool(b: bool) -> RuntimeValue {
    RuntimeValue::from_bool(b)
}
#[inline(always)]
pub fn rt_value_nil() -> RuntimeValue {
    RuntimeValue::NIL
}
#[inline(always)]
pub fn rt_value_as_int(v: RuntimeValue) -> i64 {
    v.as_int()
}
#[inline(always)]
pub fn rt_value_as_float(v: RuntimeValue) -> f64 {
    v.as_float()
}
#[inline(always)]
pub fn rt_value_as_bool(v: RuntimeValue) -> bool {
    v.as_bool()
}
#[inline(always)]
pub fn rt_value_truthy(v: RuntimeValue) -> bool {
    v.truthy()
}
#[inline(always)]
pub fn rt_value_is_nil(v: RuntimeValue) -> bool {
    v.is_nil()
}
#[inline(always)]
pub fn rt_value_is_int(v: RuntimeValue) -> bool {
    v.is_int()
}
#[inline(always)]
pub fn rt_value_is_float(v: RuntimeValue) -> bool {
    v.is_float()
}
#[inline(always)]
pub fn rt_value_is_bool(v: RuntimeValue) -> bool {
    v.is_bool()
}
#[inline(always)]
pub fn rt_value_is_heap(v: RuntimeValue) -> bool {
    v.is_heap()
}
#[inline(always)]
pub fn rt_value_type_tag(v: RuntimeValue) -> u8 {
    v.tag() as u8
}
#[inline(always)]
pub fn rt_is_error(v: RuntimeValue) -> bool {
    v.tag() == tags::TAG_SPECIAL && v.payload() == tags::SPECIAL_ERROR
}

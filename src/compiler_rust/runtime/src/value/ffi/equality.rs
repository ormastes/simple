//! Value equality comparison — implementations in src/runtime/runtime_equality.c.

use crate::value::core::RuntimeValue;

mod c_ffi {
    use crate::value::core::RuntimeValue;
    extern "C" {
        pub(super) fn rt_value_eq(a: RuntimeValue, b: RuntimeValue) -> u8;
        pub(super) fn rt_value_compare(a: RuntimeValue, b: RuntimeValue) -> i64;
        pub(super) fn rt_native_eq(a: i64, b: i64) -> i64;
        pub(super) fn rt_native_neq(a: i64, b: i64) -> i64;
    }
}

#[inline(always)]
pub fn rt_value_eq(a: RuntimeValue, b: RuntimeValue) -> u8 {
    unsafe { c_ffi::rt_value_eq(a, b) }
}
#[inline(always)]
pub fn rt_value_compare(a: RuntimeValue, b: RuntimeValue) -> i64 {
    unsafe { c_ffi::rt_value_compare(a, b) }
}
#[inline(always)]
pub fn rt_native_eq(a: i64, b: i64) -> i64 {
    unsafe { c_ffi::rt_native_eq(a, b) }
}
#[inline(always)]
pub fn rt_native_neq(a: i64, b: i64) -> i64 {
    unsafe { c_ffi::rt_native_neq(a, b) }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_int_equality() {
        let a = RuntimeValue::from_int(42);
        let b = RuntimeValue::from_int(42);
        let c = RuntimeValue::from_int(99);

        assert_eq!(rt_value_eq(a, b), 1);
        assert_eq!(rt_value_eq(a, c), 0);
        assert_eq!(rt_value_eq(b, c), 0);
    }

    #[test]
    fn test_float_equality() {
        let a = RuntimeValue::from_float(3.25);
        let b = RuntimeValue::from_float(3.25);
        let c = RuntimeValue::from_float(2.71);

        assert_eq!(rt_value_eq(a, b), 1);
        assert_eq!(rt_value_eq(a, c), 0);
    }

    #[test]
    fn test_bool_equality() {
        let t1 = RuntimeValue::from_bool(true);
        let t2 = RuntimeValue::from_bool(true);
        let f1 = RuntimeValue::from_bool(false);
        let f2 = RuntimeValue::from_bool(false);

        assert_eq!(rt_value_eq(t1, t2), 1);
        assert_eq!(rt_value_eq(f1, f2), 1);
        assert_eq!(rt_value_eq(t1, f1), 0);
        assert_eq!(rt_value_eq(t2, f2), 0);
    }

    #[test]
    fn test_nil_equality() {
        let n1 = RuntimeValue::NIL;
        let n2 = RuntimeValue::NIL;

        assert_eq!(rt_value_eq(n1, n2), 1);
    }

    #[test]
    fn test_different_types_not_equal() {
        let int_val = RuntimeValue::from_int(42);
        let float_val = RuntimeValue::from_float(42.0);
        let bool_val = RuntimeValue::from_bool(true);
        let nil_val = RuntimeValue::NIL;

        assert_eq!(rt_value_eq(int_val, float_val), 0);
        assert_eq!(rt_value_eq(int_val, bool_val), 0);
        assert_eq!(rt_value_eq(int_val, nil_val), 0);
        assert_eq!(rt_value_eq(float_val, bool_val), 0);
        assert_eq!(rt_value_eq(float_val, nil_val), 0);
        assert_eq!(rt_value_eq(bool_val, nil_val), 0);
    }

    #[test]
    fn test_same_value_reference() {
        let val = RuntimeValue::from_int(42);
        assert_eq!(rt_value_eq(val, val), 1);
    }

    #[test]
    fn test_special_float_values() {
        let inf1 = RuntimeValue::from_float(f64::INFINITY);
        let inf2 = RuntimeValue::from_float(f64::INFINITY);
        let neg_inf1 = RuntimeValue::from_float(f64::NEG_INFINITY);
        let neg_inf2 = RuntimeValue::from_float(f64::NEG_INFINITY);

        assert_eq!(rt_value_eq(inf1, inf2), 1);
        assert_eq!(rt_value_eq(neg_inf1, neg_inf2), 1);
        assert_eq!(rt_value_eq(inf1, neg_inf1), 0);
    }

    #[test]
    fn test_zero_equality() {
        let pos_zero = RuntimeValue::from_float(0.0);
        let neg_zero = RuntimeValue::from_float(-0.0);

        assert_eq!(rt_value_eq(pos_zero, neg_zero), 1);
    }

    #[test]
    fn test_enum_equality() {
        use crate::value::objects::rt_enum_new;
        let a = rt_enum_new(0, 42, RuntimeValue::NIL);
        let b = rt_enum_new(0, 42, RuntimeValue::NIL);
        let c = rt_enum_new(0, 99, RuntimeValue::NIL);

        assert_eq!(rt_value_eq(a, b), 1, "same disc should be equal");
        assert_eq!(rt_value_eq(a, c), 0, "diff disc should not be equal");
    }
}

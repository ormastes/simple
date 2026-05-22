//! Random number generation SFFI — LCG implementations in src/runtime/runtime_random.c.

mod c_sffi {
    extern "C" {
        pub(super) fn rt_random_seed(seed: i64);
        pub(super) fn rt_random_getstate() -> i64;
        pub(super) fn rt_random_setstate(new_state: i64);
        pub(super) fn rt_random_next() -> i64;
        pub(super) fn rt_random_randint(min: i64, max: i64) -> i64;
        pub(super) fn rt_random_random() -> f64;
        pub(super) fn rt_random_uniform(min: f64, max: f64) -> f64;
        #[link_name = "__c_rt_random_hex_buf"]
        pub(super) fn random_hex_buf(out: *mut u8, byte_count: i64) -> i64;
    }
}

#[inline(always)]
pub fn rt_random_seed(seed: i64) {
    unsafe { c_sffi::rt_random_seed(seed) }
}
#[inline(always)]
pub fn rt_random_getstate() -> i64 {
    unsafe { c_sffi::rt_random_getstate() }
}
#[inline(always)]
pub fn rt_random_setstate(new_state: i64) {
    unsafe { c_sffi::rt_random_setstate(new_state) }
}
#[inline(always)]
pub fn rt_random_next() -> i64 {
    unsafe { c_sffi::rt_random_next() }
}
#[inline(always)]
pub fn rt_random_randint(min: i64, max: i64) -> i64 {
    unsafe { c_sffi::rt_random_randint(min, max) }
}
#[inline(always)]
pub fn rt_random_random() -> f64 {
    unsafe { c_sffi::rt_random_random() }
}
#[inline(always)]
pub fn rt_random_uniform(min: f64, max: f64) -> f64 {
    unsafe { c_sffi::rt_random_uniform(min, max) }
}

#[no_mangle]
pub extern "C" fn rt_random_hex(len: i64) -> crate::value::RuntimeValue {
    let n = len.max(0) as usize;
    if n == 0 {
        return unsafe { crate::value::collections::rt_string_new(std::ptr::null(), 0) };
    }
    let mut buf = vec![0u8; n * 2];
    let written = unsafe { c_sffi::random_hex_buf(buf.as_mut_ptr(), n as i64) };
    if written <= 0 {
        return crate::value::RuntimeValue::NIL;
    }
    unsafe { crate::value::collections::rt_string_new(buf.as_ptr(), written as u64) }
}

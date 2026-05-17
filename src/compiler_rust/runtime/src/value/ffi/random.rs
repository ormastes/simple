//! Random number generation FFI — LCG implementations in src/runtime/runtime_random.c.

mod c_ffi {
    extern "C" {
        pub(super) fn rt_random_seed(seed: i64);
        pub(super) fn rt_random_getstate() -> i64;
        pub(super) fn rt_random_setstate(new_state: i64);
        pub(super) fn rt_random_next() -> i64;
        pub(super) fn rt_random_randint(min: i64, max: i64) -> i64;
        pub(super) fn rt_random_random() -> f64;
        pub(super) fn rt_random_uniform(min: f64, max: f64) -> f64;
    }
}

#[inline(always)]
pub fn rt_random_seed(seed: i64) { unsafe { c_ffi::rt_random_seed(seed) } }
#[inline(always)]
pub fn rt_random_getstate() -> i64 { unsafe { c_ffi::rt_random_getstate() } }
#[inline(always)]
pub fn rt_random_setstate(new_state: i64) { unsafe { c_ffi::rt_random_setstate(new_state) } }
#[inline(always)]
pub fn rt_random_next() -> i64 { unsafe { c_ffi::rt_random_next() } }
#[inline(always)]
pub fn rt_random_randint(min: i64, max: i64) -> i64 { unsafe { c_ffi::rt_random_randint(min, max) } }
#[inline(always)]
pub fn rt_random_random() -> f64 { unsafe { c_ffi::rt_random_random() } }
#[inline(always)]
pub fn rt_random_uniform(min: f64, max: f64) -> f64 { unsafe { c_ffi::rt_random_uniform(min, max) } }

#[no_mangle]
pub extern "C" fn rt_random_hex(len: i64) -> crate::value::RuntimeValue {
    use rand::RngCore;
    let n = len.max(0) as usize;
    let mut bytes = vec![0u8; n];
    rand::rngs::OsRng.fill_bytes(&mut bytes);
    let mut hex = String::with_capacity(n * 2);
    for b in &bytes {
        use std::fmt::Write;
        let _ = write!(&mut hex, "{:02x}", b);
    }
    let hex_bytes = hex.as_bytes();
    crate::value::collections::rt_string_new(hex_bytes.as_ptr(), hex_bytes.len() as u64)
}

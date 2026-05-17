//! Time FFI — implementations now live in src/runtime/runtime_time.c.

mod c_ffi {
    extern "C" {
        pub(super) fn rt_time_now_nanos() -> i64;
        pub(super) fn rt_time_now_micros() -> i64;
        pub(super) fn rt_time_now_unix_micros() -> i64;
        pub(super) fn rt_time_now_seconds_f64() -> f64;
        pub(super) fn rt_timestamp_get_year(micros: i64) -> i32;
        pub(super) fn rt_timestamp_get_month(micros: i64) -> i32;
        pub(super) fn rt_timestamp_get_day(micros: i64) -> i32;
        pub(super) fn rt_timestamp_get_hour(micros: i64) -> i32;
        pub(super) fn rt_timestamp_get_minute(micros: i64) -> i32;
        pub(super) fn rt_timestamp_get_second(micros: i64) -> i32;
        pub(super) fn rt_timestamp_get_microsecond(micros: i64) -> i32;
        pub(super) fn rt_timestamp_from_components(
            year: i32, month: i32, day: i32,
            hour: i32, minute: i32, second: i32, microsecond: i32,
        ) -> i64;
        pub(super) fn rt_timestamp_add_days(micros: i64, days: i64) -> i64;
        pub(super) fn rt_timestamp_diff_days(micros1: i64, micros2: i64) -> i64;
        pub(super) fn rt_progress_init();
        pub(super) fn rt_progress_reset();
        pub(super) fn rt_progress_get_elapsed_seconds() -> f64;
    }
}

#[inline(always)]
pub fn rt_time_now_nanos() -> i64 { unsafe { c_ffi::rt_time_now_nanos() } }
#[inline(always)]
pub fn rt_time_now_micros() -> i64 { unsafe { c_ffi::rt_time_now_micros() } }
#[inline(always)]
pub fn rt_time_now_unix_micros() -> i64 { unsafe { c_ffi::rt_time_now_unix_micros() } }
#[inline(always)]
pub fn rt_time_now_seconds() -> f64 { unsafe { c_ffi::rt_time_now_seconds_f64() } }
#[inline(always)]
pub fn rt_timestamp_get_year(micros: i64) -> i32 { unsafe { c_ffi::rt_timestamp_get_year(micros) } }
#[inline(always)]
pub fn rt_timestamp_get_month(micros: i64) -> i32 { unsafe { c_ffi::rt_timestamp_get_month(micros) } }
#[inline(always)]
pub fn rt_timestamp_get_day(micros: i64) -> i32 { unsafe { c_ffi::rt_timestamp_get_day(micros) } }
#[inline(always)]
pub fn rt_timestamp_get_hour(micros: i64) -> i32 { unsafe { c_ffi::rt_timestamp_get_hour(micros) } }
#[inline(always)]
pub fn rt_timestamp_get_minute(micros: i64) -> i32 { unsafe { c_ffi::rt_timestamp_get_minute(micros) } }
#[inline(always)]
pub fn rt_timestamp_get_second(micros: i64) -> i32 { unsafe { c_ffi::rt_timestamp_get_second(micros) } }
#[inline(always)]
pub fn rt_timestamp_get_microsecond(micros: i64) -> i32 { unsafe { c_ffi::rt_timestamp_get_microsecond(micros) } }
#[inline(always)]
pub fn rt_timestamp_from_components(
    year: i32, month: i32, day: i32,
    hour: i32, minute: i32, second: i32, microsecond: i32,
) -> i64 {
    unsafe { c_ffi::rt_timestamp_from_components(year, month, day, hour, minute, second, microsecond) }
}
#[inline(always)]
pub fn rt_timestamp_add_days(micros: i64, days: i64) -> i64 { unsafe { c_ffi::rt_timestamp_add_days(micros, days) } }
#[inline(always)]
pub fn rt_timestamp_diff_days(micros1: i64, micros2: i64) -> i64 { unsafe { c_ffi::rt_timestamp_diff_days(micros1, micros2) } }
#[inline(always)]
pub fn rt_progress_init() { unsafe { c_ffi::rt_progress_init() } }
#[inline(always)]
pub fn rt_progress_reset() { unsafe { c_ffi::rt_progress_reset() } }
#[inline(always)]
pub fn rt_progress_get_elapsed_seconds() -> f64 { unsafe { c_ffi::rt_progress_get_elapsed_seconds() } }

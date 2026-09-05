//! Time SFFI — clocks live in `runtime_time.c`; timestamp/progress helpers live
//! in `runtime_timestamp.c` so Stage4 can compose them without duplicate clocks.

mod c_sffi {
    extern "C" {
        pub(super) fn rt_time_now_nanos() -> i64;
        pub(super) fn rt_time_now_micros() -> i64;
        pub(super) fn rt_time_now_unix_micros() -> i64;
        pub(super) fn rt_time_now_seconds() -> i64;
        pub(super) fn rt_time_now_seconds_f64() -> f64;
        pub(super) fn rt_timestamp_get_year(micros: i64) -> i32;
        pub(super) fn rt_timestamp_get_month(micros: i64) -> i32;
        pub(super) fn rt_timestamp_get_day(micros: i64) -> i32;
        pub(super) fn rt_timestamp_get_hour(micros: i64) -> i32;
        pub(super) fn rt_timestamp_get_minute(micros: i64) -> i32;
        pub(super) fn rt_timestamp_get_second(micros: i64) -> i32;
        pub(super) fn rt_timestamp_get_microsecond(micros: i64) -> i32;
        pub(super) fn rt_timestamp_from_components(
            year: i32,
            month: i32,
            day: i32,
            hour: i32,
            minute: i32,
            second: i32,
            microsecond: i32,
        ) -> i64;
        pub(super) fn rt_timestamp_add_days(micros: i64, days: i64) -> i64;
        pub(super) fn rt_timestamp_diff_days(micros1: i64, micros2: i64) -> i64;
        pub(super) fn rt_progress_init() -> bool;
        pub(super) fn rt_progress_reset() -> bool;
        pub(super) fn rt_progress_get_elapsed_seconds() -> f64;
        pub(super) fn rt_progress_clock_now_nanos() -> i64;
        pub(super) fn rt_progress_tls_is_initialized() -> bool;
        pub(super) fn rt_progress_tls_start_nanos() -> i64;
        pub(super) fn rt_progress_tls_store_start_nanos(start_nanos: i64);
        pub(super) fn rt_progress_tls_clear();
    }
}

#[inline(always)]
fn lift_clock_value(value: i64) -> Option<i64> {
    (value >= 0).then_some(value)
}

#[inline(always)]
pub fn rt_time_now_nanos() -> i64 {
    unsafe { c_sffi::rt_time_now_nanos() }
}
#[inline(always)]
pub fn try_rt_time_now_nanos() -> Option<i64> {
    lift_clock_value(rt_time_now_nanos())
}
#[inline(always)]
pub fn rt_time_now_micros() -> i64 {
    unsafe { c_sffi::rt_time_now_micros() }
}
#[inline(always)]
pub fn try_rt_time_now_micros() -> Option<i64> {
    lift_clock_value(rt_time_now_micros())
}
#[inline(always)]
pub fn rt_time_now_unix_micros() -> i64 {
    unsafe { c_sffi::rt_time_now_unix_micros() }
}
#[inline(always)]
pub fn try_rt_time_now_unix_micros() -> Option<i64> {
    lift_clock_value(rt_time_now_unix_micros())
}
#[inline(always)]
pub fn rt_time_now_seconds() -> i64 {
    unsafe { c_sffi::rt_time_now_seconds() }
}
#[inline(always)]
pub fn rt_time_now_seconds_f64() -> f64 {
    unsafe { c_sffi::rt_time_now_seconds_f64() }
}
#[inline(always)]
pub fn try_rt_time_now_seconds_f64() -> Option<f64> {
    let value = rt_time_now_seconds_f64();
    (value >= 0.0).then_some(value)
}
#[inline(always)]
pub fn fractional_seconds_to_millis(time_seconds: f64) -> i64 {
    (time_seconds * 1000.0) as i64
}
#[inline(always)]
pub fn rt_timestamp_get_year(micros: i64) -> i32 {
    unsafe { c_sffi::rt_timestamp_get_year(micros) }
}
#[inline(always)]
pub fn rt_timestamp_get_month(micros: i64) -> i32 {
    unsafe { c_sffi::rt_timestamp_get_month(micros) }
}
#[inline(always)]
pub fn rt_timestamp_get_day(micros: i64) -> i32 {
    unsafe { c_sffi::rt_timestamp_get_day(micros) }
}
#[inline(always)]
pub fn rt_timestamp_get_hour(micros: i64) -> i32 {
    unsafe { c_sffi::rt_timestamp_get_hour(micros) }
}
#[inline(always)]
pub fn rt_timestamp_get_minute(micros: i64) -> i32 {
    unsafe { c_sffi::rt_timestamp_get_minute(micros) }
}
#[inline(always)]
pub fn rt_timestamp_get_second(micros: i64) -> i32 {
    unsafe { c_sffi::rt_timestamp_get_second(micros) }
}
#[inline(always)]
pub fn rt_timestamp_get_microsecond(micros: i64) -> i32 {
    unsafe { c_sffi::rt_timestamp_get_microsecond(micros) }
}
#[inline(always)]
pub fn rt_timestamp_from_components(
    year: i32,
    month: i32,
    day: i32,
    hour: i32,
    minute: i32,
    second: i32,
    microsecond: i32,
) -> i64 {
    unsafe { c_sffi::rt_timestamp_from_components(year, month, day, hour, minute, second, microsecond) }
}
#[inline(always)]
pub fn rt_timestamp_add_days(micros: i64, days: i64) -> i64 {
    unsafe { c_sffi::rt_timestamp_add_days(micros, days) }
}
#[inline(always)]
pub fn rt_timestamp_diff_days(micros1: i64, micros2: i64) -> i64 {
    unsafe { c_sffi::rt_timestamp_diff_days(micros1, micros2) }
}
#[inline(always)]
pub fn rt_progress_init() -> bool {
    unsafe { c_sffi::rt_progress_init() }
}
#[inline(always)]
pub fn rt_progress_reset() -> bool {
    unsafe { c_sffi::rt_progress_reset() }
}
#[inline(always)]
pub fn rt_progress_get_elapsed_seconds() -> f64 {
    unsafe { c_sffi::rt_progress_get_elapsed_seconds() }
}
#[inline(always)]
pub fn rt_progress_clock_now_nanos() -> i64 {
    unsafe { c_sffi::rt_progress_clock_now_nanos() }
}
#[inline(always)]
pub fn rt_progress_tls_is_initialized() -> bool {
    unsafe { c_sffi::rt_progress_tls_is_initialized() }
}
#[inline(always)]
pub fn rt_progress_tls_start_nanos() -> i64 {
    unsafe { c_sffi::rt_progress_tls_start_nanos() }
}
#[inline(always)]
pub fn rt_progress_tls_store_start_nanos(start_nanos: i64) {
    unsafe { c_sffi::rt_progress_tls_store_start_nanos(start_nanos) }
}
#[inline(always)]
pub fn rt_progress_tls_clear() {
    unsafe { c_sffi::rt_progress_tls_clear() }
}

#[cfg(test)]
mod tests {
    use super::{fractional_seconds_to_millis, lift_clock_value, rt_time_now_seconds, try_rt_time_now_seconds_f64};

    #[test]
    fn clock_failure_sentinel_is_not_a_value() {
        assert_eq!(lift_clock_value(-1), None);
        assert_eq!(lift_clock_value(0), Some(0));
        assert_eq!(lift_clock_value(i64::MAX), Some(i64::MAX));
    }

    #[test]
    fn seconds_clock_lifts_nonnegative_live_value() {
        assert!(try_rt_time_now_seconds_f64().is_some());
    }

    /// Direct link+call regression for the i64 `rt_time_now_seconds` FFI
    /// symbol: `runtime/src/value/sffi/time.rs` declares it as `extern "C"`
    /// but no C source compiled by this crate's `build.rs` ever defined it
    /// (only `runtime.c`, deliberately excluded, did) -- a from-scratch link
    /// failed outright. Now defined in `runtime_time.c`, which IS compiled
    /// here. A real Unix timestamp is comfortably >= 1_600_000_000
    /// (2020-09-13) on any host this test runs on, and must roughly match
    /// the existing f64 clock so both aren't drifting relative to each
    /// other. See doc/08_tracking/bug/
    /// seed_rt_time_now_seconds_unlinkable_2026-08-28.md.
    #[test]
    fn rt_time_now_seconds_links_and_returns_a_real_unix_timestamp() {
        let secs = rt_time_now_seconds();
        assert!(
            secs >= 1_600_000_000,
            "rt_time_now_seconds() returned {secs}, not a plausible Unix timestamp"
        );
        let secs_f64 = try_rt_time_now_seconds_f64().expect("f64 clock must also succeed");
        assert!(
            (secs as f64 - secs_f64).abs() < 5.0,
            "rt_time_now_seconds() ({secs}) and the f64 clock ({secs_f64}) disagree by more than 5s"
        );
    }

    #[test]
    fn fractional_seconds_to_millis_preserves_subsecond_precision() {
        assert_eq!(fractional_seconds_to_millis(1_700_000_000.125), 1_700_000_000_125);
        assert_eq!(fractional_seconds_to_millis(12.999), 12_999);
    }
}

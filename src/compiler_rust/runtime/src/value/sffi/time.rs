//! Time SFFI — clocks live in `runtime_time.c`; timestamp/progress helpers live
//! in `runtime_timestamp.c` so Stage4 can compose them without duplicate clocks.

mod c_sffi {
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
pub fn rt_time_now_seconds() -> f64 {
    unsafe { c_sffi::rt_time_now_seconds_f64() }
}
#[inline(always)]
pub fn try_rt_time_now_seconds() -> Option<f64> {
    let value = rt_time_now_seconds();
    (value >= 0.0).then_some(value)
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

#[cfg(test)]
mod tests {
    use super::{lift_clock_value, try_rt_time_now_seconds};

    #[test]
    fn clock_failure_sentinel_is_not_a_value() {
        assert_eq!(lift_clock_value(-1), None);
        assert_eq!(lift_clock_value(0), Some(0));
        assert_eq!(lift_clock_value(i64::MAX), Some(i64::MAX));
    }

    #[test]
    fn seconds_clock_lifts_nonnegative_live_value() {
        assert!(try_rt_time_now_seconds().is_some());
    }
}

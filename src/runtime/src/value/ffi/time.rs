//! Time and timestamp FFI functions.
//!
//! Provides functions for working with Unix timestamps (microseconds since epoch)
//! and extracting date/time components. All timestamps are in UTC.
//!
//! ## Timestamp Format
//!
//! Timestamps are represented as i64 microseconds since Unix epoch (1970-01-01 00:00:00 UTC):
//! - Positive values: dates after 1970
//! - Negative values: dates before 1970
//! - Resolution: microseconds (1/1,000,000 second)
//!
//! ## Function Categories
//!
//! - **Current Time**: Get current timestamp
//! - **Component Extraction**: Extract year, month, day, hour, minute, second, microsecond
//! - **Construction**: Build timestamp from components
//! - **Arithmetic**: Add/subtract days, calculate differences
//!
//! ## Usage Pattern
//!
//! ```rust
//! // Get current time
//! let now = rt_time_now_unix_micros();
//!
//! // Extract components
//! let year = rt_timestamp_get_year(now);
//! let month = rt_timestamp_get_month(now);
//! let day = rt_timestamp_get_day(now);
//!
//! // Create timestamp
//! let timestamp = rt_timestamp_from_components(2024, 1, 15, 12, 30, 45, 0);
//!
//! // Arithmetic
//! let tomorrow = rt_timestamp_add_days(now, 1);
//! let days_diff = rt_timestamp_diff_days(tomorrow, now);
//! ```

// ============================================================================
// Current Time Functions
// ============================================================================

/// Get current Unix timestamp in microseconds since epoch (1970-01-01 00:00:00 UTC)
///
/// Returns the current system time as microseconds since Unix epoch.
/// Returns 0 if the system time is before Unix epoch (very rare).
///
/// # Examples
/// - 2024-01-01 00:00:00 UTC → ~1704067200000000
/// - 1970-01-01 00:00:00 UTC → 0
#[no_mangle]
pub extern "C" fn rt_time_now_unix_micros() -> i64 {
    match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(duration) => {
            let secs = duration.as_secs() as i64;
            let micros = duration.subsec_micros() as i64;
            secs * 1_000_000 + micros
        }
        Err(_) => 0,
    }
}

/// Get current Unix timestamp as float seconds since epoch
///
/// Returns the current system time as floating-point seconds since Unix epoch.
/// Provides fractional seconds with high precision.
/// Returns 0.0 if the system time is before Unix epoch (very rare).
///
/// # Examples
/// - 2024-01-01 00:00:00 UTC → ~1704067200.0
/// - 2024-01-01 00:00:00.5 UTC → ~1704067200.5
#[no_mangle]
pub extern "C" fn rt_time_now_seconds() -> f64 {
    match std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH) {
        Ok(duration) => duration.as_secs_f64(),
        Err(_) => 0.0,
    }
}

// ============================================================================
// Component Extraction Functions
// ============================================================================

/// Convert Unix timestamp (microseconds) to year
///
/// # Examples
/// - 0 (1970-01-01) → 1970
/// - 86400000000 (1970-01-02) → 1970
/// - 31536000000000 (1971-01-01) → 1971
#[no_mangle]
pub extern "C" fn rt_timestamp_get_year(micros: i64) -> i32 {
    let days = micros / (86400 * 1_000_000);
    timestamp_days_to_year(days)
}

/// Convert Unix timestamp (microseconds) to month (1-12)
///
/// # Examples
/// - 0 (1970-01-01) → 1 (January)
/// - Timestamp for 1970-12-31 → 12 (December)
#[no_mangle]
pub extern "C" fn rt_timestamp_get_month(micros: i64) -> i32 {
    let days = micros / (86400 * 1_000_000);
    let (_, month, _) = timestamp_days_to_ymd(days);
    month
}

/// Convert Unix timestamp (microseconds) to day of month (1-31)
///
/// # Examples
/// - 0 (1970-01-01) → 1
/// - Timestamp for 1970-01-15 → 15
#[no_mangle]
pub extern "C" fn rt_timestamp_get_day(micros: i64) -> i32 {
    let days = micros / (86400 * 1_000_000);
    let (_, _, day) = timestamp_days_to_ymd(days);
    day
}

/// Convert Unix timestamp (microseconds) to hour (0-23)
///
/// # Examples
/// - 0 → 0 (midnight)
/// - 3600000000 (1 hour) → 1
/// - 43200000000 (12 hours) → 12 (noon)
#[no_mangle]
pub extern "C" fn rt_timestamp_get_hour(micros: i64) -> i32 {
    let seconds_in_day = (micros / 1_000_000) % 86400;
    (seconds_in_day / 3600) as i32
}

/// Convert Unix timestamp (microseconds) to minute (0-59)
///
/// # Examples
/// - 0 → 0
/// - 60000000 (1 minute) → 1
/// - 3660000000 (1 hour 1 minute) → 1
#[no_mangle]
pub extern "C" fn rt_timestamp_get_minute(micros: i64) -> i32 {
    let seconds_in_day = (micros / 1_000_000) % 86400;
    ((seconds_in_day % 3600) / 60) as i32
}

/// Convert Unix timestamp (microseconds) to second (0-59)
///
/// # Examples
/// - 0 → 0
/// - 1000000 (1 second) → 1
/// - 61000000 (1 minute 1 second) → 1
#[no_mangle]
pub extern "C" fn rt_timestamp_get_second(micros: i64) -> i32 {
    let seconds_in_day = (micros / 1_000_000) % 86400;
    (seconds_in_day % 60) as i32
}

/// Convert Unix timestamp (microseconds) to microsecond (0-999999)
///
/// Returns the fractional second component as microseconds.
///
/// # Examples
/// - 0 → 0
/// - 1 → 1
/// - 500000 → 500000 (0.5 seconds)
/// - 1000000 → 0 (exactly 1 second)
#[no_mangle]
pub extern "C" fn rt_timestamp_get_microsecond(micros: i64) -> i32 {
    (micros % 1_000_000) as i32
}

// ============================================================================
// Timestamp Construction
// ============================================================================

/// Convert date/time components to Unix timestamp (microseconds)
///
/// # Arguments
/// * `year` - Year (e.g., 2024)
/// * `month` - Month (1-12, where 1=January)
/// * `day` - Day of month (1-31)
/// * `hour` - Hour (0-23)
/// * `minute` - Minute (0-59)
/// * `second` - Second (0-59)
/// * `microsecond` - Microsecond (0-999999)
///
/// # Examples
/// - from_components(1970, 1, 1, 0, 0, 0, 0) → 0 (Unix epoch)
/// - from_components(1970, 1, 2, 0, 0, 0, 0) → 86400000000 (1 day)
#[no_mangle]
pub extern "C" fn rt_timestamp_from_components(
    year: i32,
    month: i32,
    day: i32,
    hour: i32,
    minute: i32,
    second: i32,
    microsecond: i32,
) -> i64 {
    let days = ymd_to_timestamp_days(year, month, day);
    let seconds_in_day = (hour as i64) * 3600 + (minute as i64) * 60 + (second as i64);
    days * 86400 * 1_000_000 + seconds_in_day * 1_000_000 + (microsecond as i64)
}

// ============================================================================
// Timestamp Arithmetic
// ============================================================================

/// Add days to a Unix timestamp
///
/// # Examples
/// - add_days(0, 1) → 86400000000 (Unix epoch + 1 day)
/// - add_days(timestamp, -1) → timestamp - 1 day
#[no_mangle]
pub extern "C" fn rt_timestamp_add_days(micros: i64, days: i64) -> i64 {
    micros + days * 86400 * 1_000_000
}

/// Calculate difference in days between two timestamps
///
/// Returns (micros1 - micros2) / days_in_microseconds
///
/// # Examples
/// - diff_days(86400000000, 0) → 1 (1 day difference)
/// - diff_days(0, 86400000000) → -1 (negative 1 day)
#[no_mangle]
pub extern "C" fn rt_timestamp_diff_days(micros1: i64, micros2: i64) -> i64 {
    (micros1 - micros2) / (86400 * 1_000_000)
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Check if year is a leap year
fn is_leap_year(year: i32) -> bool {
    (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0)
}

/// Get days in month
fn days_in_month(year: i32, month: i32) -> i32 {
    match month {
        1 | 3 | 5 | 7 | 8 | 10 | 12 => 31,
        4 | 6 | 9 | 11 => 30,
        2 => {
            if is_leap_year(year) {
                29
            } else {
                28
            }
        }
        _ => 0,
    }
}

/// Convert days since Unix epoch to year
fn timestamp_days_to_year(days: i64) -> i32 {
    // Unix epoch starts at 1970-01-01
    let mut year = 1970;
    let mut remaining_days = days;

    // Handle negative days (dates before 1970)
    if remaining_days < 0 {
        while remaining_days < 0 {
            year -= 1;
            let days_in_year = if is_leap_year(year) { 366 } else { 365 };
            remaining_days += days_in_year as i64;
        }
        return year;
    }

    // Handle positive days (dates after 1970)
    loop {
        let days_in_year = if is_leap_year(year) { 366 } else { 365 };
        if remaining_days < days_in_year as i64 {
            break;
        }
        remaining_days -= days_in_year as i64;
        year += 1;
    }

    year
}

/// Convert days since Unix epoch to (year, month, day)
fn timestamp_days_to_ymd(days: i64) -> (i32, i32, i32) {
    let mut year = 1970;
    let mut remaining_days = days;

    // Handle negative days (dates before 1970)
    if remaining_days < 0 {
        while remaining_days < 0 {
            year -= 1;
            let days_in_year = if is_leap_year(year) { 366 } else { 365 };
            remaining_days += days_in_year as i64;
        }
    } else {
        // Handle positive days (dates after 1970)
        loop {
            let days_in_year = if is_leap_year(year) { 366 } else { 365 };
            if remaining_days < days_in_year as i64 {
                break;
            }
            remaining_days -= days_in_year as i64;
            year += 1;
        }
    }

    // Now convert remaining days to month and day
    let mut month = 1;
    while month <= 12 {
        let days_in_current_month = days_in_month(year, month) as i64;
        if remaining_days < days_in_current_month {
            break;
        }
        remaining_days -= days_in_current_month;
        month += 1;
    }

    let day = remaining_days + 1; // Days are 1-indexed

    (year, month, day as i32)
}

/// Convert (year, month, day) to days since Unix epoch
fn ymd_to_timestamp_days(year: i32, month: i32, day: i32) -> i64 {
    let mut days: i64 = 0;

    // Add days for all years from 1970 to year-1
    if year >= 1970 {
        for y in 1970..year {
            days += if is_leap_year(y) { 366 } else { 365 };
        }
    } else {
        for y in year..1970 {
            days -= if is_leap_year(y) { 366 } else { 365 };
        }
    }

    // Add days for all months in current year
    for m in 1..month {
        days += days_in_month(year, m) as i64;
    }

    // Add remaining days
    days += (day - 1) as i64;

    days
}

#[cfg(test)]
mod tests {
    use super::*;

    // ========================================================================
    // Current Time Tests
    // ========================================================================

    #[test]
    fn test_time_now_unix_micros() {
        let now = rt_time_now_unix_micros();
        // Should be a reasonable timestamp (after 2020, before 2100)
        assert!(now > 1_577_836_800_000_000); // 2020-01-01
        assert!(now < 4_102_444_800_000_000); // 2100-01-01
    }

    #[test]
    fn test_time_now_seconds() {
        let now = rt_time_now_seconds();
        // Should be a reasonable timestamp
        assert!(now > 1577836800.0); // 2020-01-01
        assert!(now < 4102444800.0); // 2100-01-01
    }

    #[test]
    fn test_time_consistency() {
        // Micros and seconds should be consistent
        let micros = rt_time_now_unix_micros();
        let seconds = rt_time_now_seconds();
        let micros_as_seconds = micros as f64 / 1_000_000.0;

        // Should be within 1 second of each other
        assert!((micros_as_seconds - seconds).abs() < 1.0);
    }

    // ========================================================================
    // Component Extraction Tests
    // ========================================================================

    #[test]
    fn test_unix_epoch_components() {
        // Unix epoch: 1970-01-01 00:00:00
        let epoch = 0i64;

        assert_eq!(rt_timestamp_get_year(epoch), 1970);
        assert_eq!(rt_timestamp_get_month(epoch), 1);
        assert_eq!(rt_timestamp_get_day(epoch), 1);
        assert_eq!(rt_timestamp_get_hour(epoch), 0);
        assert_eq!(rt_timestamp_get_minute(epoch), 0);
        assert_eq!(rt_timestamp_get_second(epoch), 0);
        assert_eq!(rt_timestamp_get_microsecond(epoch), 0);
    }

    #[test]
    fn test_specific_date_components() {
        // 2024-03-15 14:30:45.123456
        let timestamp = rt_timestamp_from_components(2024, 3, 15, 14, 30, 45, 123456);

        assert_eq!(rt_timestamp_get_year(timestamp), 2024);
        assert_eq!(rt_timestamp_get_month(timestamp), 3);
        assert_eq!(rt_timestamp_get_day(timestamp), 15);
        assert_eq!(rt_timestamp_get_hour(timestamp), 14);
        assert_eq!(rt_timestamp_get_minute(timestamp), 30);
        assert_eq!(rt_timestamp_get_second(timestamp), 45);
        assert_eq!(rt_timestamp_get_microsecond(timestamp), 123456);
    }

    #[test]
    fn test_one_day_after_epoch() {
        // 1970-01-02 00:00:00 (1 day = 86400 seconds)
        let one_day = 86400i64 * 1_000_000;

        assert_eq!(rt_timestamp_get_year(one_day), 1970);
        assert_eq!(rt_timestamp_get_month(one_day), 1);
        assert_eq!(rt_timestamp_get_day(one_day), 2);
    }

    #[test]
    fn test_time_components() {
        // Test various times within a day
        let base = rt_timestamp_from_components(2024, 1, 1, 0, 0, 0, 0);

        // 12:00:00
        let noon = base + 12 * 3600 * 1_000_000;
        assert_eq!(rt_timestamp_get_hour(noon), 12);
        assert_eq!(rt_timestamp_get_minute(noon), 0);
        assert_eq!(rt_timestamp_get_second(noon), 0);

        // 23:59:59
        let almost_midnight = base + (23 * 3600 + 59 * 60 + 59) * 1_000_000;
        assert_eq!(rt_timestamp_get_hour(almost_midnight), 23);
        assert_eq!(rt_timestamp_get_minute(almost_midnight), 59);
        assert_eq!(rt_timestamp_get_second(almost_midnight), 59);
    }

    #[test]
    fn test_microsecond_component() {
        let base = rt_timestamp_from_components(2024, 1, 1, 0, 0, 0, 0);

        // Test various microsecond values
        assert_eq!(rt_timestamp_get_microsecond(base), 0);
        assert_eq!(rt_timestamp_get_microsecond(base + 1), 1);
        assert_eq!(rt_timestamp_get_microsecond(base + 500_000), 500_000);
        assert_eq!(rt_timestamp_get_microsecond(base + 999_999), 999_999);
        assert_eq!(rt_timestamp_get_microsecond(base + 1_000_000), 0); // Wraps to next second
    }

    // ========================================================================
    // Timestamp Construction Tests
    // ========================================================================

    #[test]
    fn test_from_components_epoch() {
        let timestamp = rt_timestamp_from_components(1970, 1, 1, 0, 0, 0, 0);
        assert_eq!(timestamp, 0);
    }

    #[test]
    fn test_from_components_roundtrip() {
        // Create a timestamp and extract components - should match
        let original_year = 2024;
        let original_month = 6;
        let original_day = 15;
        let original_hour = 14;
        let original_minute = 30;
        let original_second = 45;
        let original_micro = 123456;

        let timestamp = rt_timestamp_from_components(
            original_year,
            original_month,
            original_day,
            original_hour,
            original_minute,
            original_second,
            original_micro,
        );

        assert_eq!(rt_timestamp_get_year(timestamp), original_year);
        assert_eq!(rt_timestamp_get_month(timestamp), original_month);
        assert_eq!(rt_timestamp_get_day(timestamp), original_day);
        assert_eq!(rt_timestamp_get_hour(timestamp), original_hour);
        assert_eq!(rt_timestamp_get_minute(timestamp), original_minute);
        assert_eq!(rt_timestamp_get_second(timestamp), original_second);
        assert_eq!(rt_timestamp_get_microsecond(timestamp), original_micro);
    }

    // ========================================================================
    // Arithmetic Tests
    // ========================================================================

    #[test]
    fn test_add_days() {
        let epoch = 0i64;
        let one_day = 86400i64 * 1_000_000;

        assert_eq!(rt_timestamp_add_days(epoch, 1), one_day);
        assert_eq!(rt_timestamp_add_days(epoch, 7), 7 * one_day);
        assert_eq!(rt_timestamp_add_days(one_day, -1), epoch);
    }

    #[test]
    fn test_diff_days() {
        let epoch = 0i64;
        let one_day = 86400i64 * 1_000_000;

        assert_eq!(rt_timestamp_diff_days(one_day, epoch), 1);
        assert_eq!(rt_timestamp_diff_days(epoch, one_day), -1);
        assert_eq!(rt_timestamp_diff_days(7 * one_day, epoch), 7);
    }

    // ========================================================================
    // Helper Function Tests
    // ========================================================================

    #[test]
    fn test_is_leap_year() {
        assert!(!is_leap_year(1900)); // Divisible by 100 but not 400
        assert!(is_leap_year(2000)); // Divisible by 400
        assert!(is_leap_year(2004)); // Divisible by 4
        assert!(!is_leap_year(2001)); // Not divisible by 4
        assert!(is_leap_year(2024)); // Divisible by 4
    }

    #[test]
    fn test_days_in_month() {
        // Regular year
        assert_eq!(days_in_month(2023, 1), 31); // January
        assert_eq!(days_in_month(2023, 2), 28); // February (non-leap)
        assert_eq!(days_in_month(2023, 4), 30); // April

        // Leap year
        assert_eq!(days_in_month(2024, 2), 29); // February (leap)
    }

    #[test]
    fn test_leap_year_handling() {
        // Feb 29, 2024 should be valid
        let feb_29_2024 = rt_timestamp_from_components(2024, 2, 29, 0, 0, 0, 0);
        assert_eq!(rt_timestamp_get_month(feb_29_2024), 2);
        assert_eq!(rt_timestamp_get_day(feb_29_2024), 29);
    }

    #[test]
    fn test_year_boundaries() {
        // Test transition between years
        let dec_31_1970 = rt_timestamp_from_components(1970, 12, 31, 23, 59, 59, 0);
        let jan_1_1971 = rt_timestamp_from_components(1971, 1, 1, 0, 0, 0, 0);

        assert_eq!(rt_timestamp_get_year(dec_31_1970), 1970);
        assert_eq!(rt_timestamp_get_year(jan_1_1971), 1971);

        // Should be 1 second apart (plus 1 microsecond due to the 59th second)
        let diff = jan_1_1971 - dec_31_1970;
        assert_eq!(diff, 1_000_000); // 1 second in microseconds
    }

    #[test]
    fn test_month_boundaries() {
        // Test last day of January and first day of February
        let jan_31 = rt_timestamp_from_components(2024, 1, 31, 0, 0, 0, 0);
        let feb_1 = rt_timestamp_from_components(2024, 2, 1, 0, 0, 0, 0);

        assert_eq!(rt_timestamp_get_month(jan_31), 1);
        assert_eq!(rt_timestamp_get_day(jan_31), 31);
        assert_eq!(rt_timestamp_get_month(feb_1), 2);
        assert_eq!(rt_timestamp_get_day(feb_1), 1);
    }
}

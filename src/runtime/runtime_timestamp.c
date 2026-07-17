/*
 * Simple Runtime — Timestamp and Progress FFI Functions
 *
 * Arithmetic and progress helpers split from runtime_time.c so the Stage4
 * core-C clock owner can compose with this source without duplicate symbols.
 * Build: cc -c -fPIC -O2 -std=gnu11 runtime_timestamp.c -o runtime_timestamp.o
 */

#include <stdint.h>
#include <time.h>

#ifdef _WIN32
extern int64_t rt_time_now_unix_micros(void);
extern int64_t rt_time_now_nanos(void);
#endif

/* ---- Unix timestamp in seconds as f64 (fractional) ---- */
double rt_time_now_seconds_f64(void) {
#ifdef _WIN32
    return (double)rt_time_now_unix_micros() / 1000000.0;
#else
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
#endif
}

/* ---- Civil date helpers (Howard Hinnant algorithm) ----
 * Converts days since Unix epoch (1970-01-01) to year/month/day.
 * Works for negative days (dates before 1970).
 * Epoch shifted to 0000-03-01 internally.
 */
static void days_to_ymd(int64_t z, int32_t *year, int32_t *month, int32_t *day) {
    z += 719468;
    int64_t era = (z >= 0 ? z : z - 146096) / 146097;
    int64_t doe = z - era * 146097;
    int64_t yoe = (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365;
    int64_t y   = yoe + era * 400;
    int64_t doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    int64_t mp  = (5 * doy + 2) / 153;
    int64_t d   = doy - (153 * mp + 2) / 5 + 1;
    int64_t m   = mp < 10 ? mp + 3 : mp - 9;
    y += (m <= 2);
    *year  = (int32_t)y;
    *month = (int32_t)m;
    *day   = (int32_t)d;
}

/* ---- Timestamp component extraction (micros since epoch → component) ---- */
int32_t rt_timestamp_get_year(int64_t micros) {
    int64_t days = micros / (86400LL * 1000000LL);
    /* floor division for negative values */
    if (micros < 0 && micros % (86400LL * 1000000LL) != 0) days--;
    int32_t y, m, d;
    days_to_ymd(days, &y, &m, &d);
    return y;
}

int32_t rt_timestamp_get_month(int64_t micros) {
    int64_t days = micros / (86400LL * 1000000LL);
    if (micros < 0 && micros % (86400LL * 1000000LL) != 0) days--;
    int32_t y, m, d;
    days_to_ymd(days, &y, &m, &d);
    return m;
}

int32_t rt_timestamp_get_day(int64_t micros) {
    int64_t days = micros / (86400LL * 1000000LL);
    if (micros < 0 && micros % (86400LL * 1000000LL) != 0) days--;
    int32_t y, m, d;
    days_to_ymd(days, &y, &m, &d);
    return d;
}

static int64_t time_of_day_micros(int64_t micros) {
    int64_t value = micros % (86400LL * 1000000LL);
    if (value < 0) value += 86400LL * 1000000LL;
    return value;
}

int32_t rt_timestamp_get_hour(int64_t micros) {
    return (int32_t)(time_of_day_micros(micros) / (3600LL * 1000000LL));
}

int32_t rt_timestamp_get_minute(int64_t micros) {
    return (int32_t)((time_of_day_micros(micros) / (60LL * 1000000LL)) % 60);
}

int32_t rt_timestamp_get_second(int64_t micros) {
    return (int32_t)((time_of_day_micros(micros) / 1000000LL) % 60);
}

int32_t rt_timestamp_get_microsecond(int64_t micros) {
    return (int32_t)(time_of_day_micros(micros) % 1000000LL);
}

/* ---- Construct timestamp from UTC components ---- */
int64_t rt_timestamp_from_components(int32_t year, int32_t month, int32_t day,
                                     int32_t hour, int32_t minute, int32_t second,
                                     int32_t microsecond) {
    /* Shift Jan/Feb to previous year for march-based algorithm */
    int32_t y = year  - (month <= 2 ? 1 : 0);
    int32_t m = month + (month <= 2 ? 9 : -3);
    int64_t era = (int64_t)(y >= 0 ? y : y - 399) / 400;
    int64_t yoe = (int64_t)y - era * 400;
    int64_t doy = (153 * m + 2) / 5 + day - 1;
    int64_t doe = yoe * 365 + yoe / 4 - yoe / 100 + doy;
    int64_t days = era * 146097 + doe - 719468;
    int64_t secs = days * 86400LL
                 + (int64_t)hour   * 3600
                 + (int64_t)minute * 60
                 + (int64_t)second;
    return secs * 1000000LL + microsecond;
}

/* ---- Add days to timestamp ---- */
int64_t rt_timestamp_add_days(int64_t micros, int64_t days) {
    return micros + days * 86400LL * 1000000LL;
}

/* ---- Difference in days between two timestamps ---- */
int64_t rt_timestamp_diff_days(int64_t micros1, int64_t micros2) {
    int64_t diff = micros1 - micros2;
    int64_t days = diff / (86400LL * 1000000LL);
    /* truncate toward zero (matching Rust integer division) */
    return days;
}

/* ---- Progress tracking (process-local monotonic timer) ---- */
static int g_progress_initialized = 0;
#ifndef _WIN32
static struct timespec g_progress_start;
#endif

void rt_progress_init(void) {
#ifdef _WIN32
    g_progress_initialized = 1;
#else
    clock_gettime(CLOCK_MONOTONIC, &g_progress_start);
    g_progress_initialized = 1;
#endif
}

void rt_progress_reset(void) {
#ifdef _WIN32
    g_progress_initialized = 1;
#else
    clock_gettime(CLOCK_MONOTONIC, &g_progress_start);
    g_progress_initialized = 1;
#endif
}

double rt_progress_get_elapsed_seconds(void) {
#ifdef _WIN32
    if (!g_progress_initialized) {
        rt_progress_init();
        return 0.0;
    }
    return (double)rt_time_now_nanos() / 1000000000.0;
#else
    if (!g_progress_initialized) {
        rt_progress_init();
        return 0.0;
    }
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    double secs = (double)(now.tv_sec  - g_progress_start.tv_sec)
                + (double)(now.tv_nsec - g_progress_start.tv_nsec) / 1e9;
    return secs < 0.0 ? 0.0 : secs;
#endif
}

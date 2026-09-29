/* Simple Runtime: hosted clock and bounded thread-local timestamp ABI shims.
 * Calendar arithmetic and progress policy are owned by std.common.time_utils. */
#include <stdbool.h>
#include <stdint.h>
#include <time.h>

#ifdef _WIN32
extern int64_t rt_time_now_unix_micros(void);
extern int64_t rt_time_now_nanos(void);
#endif

#if defined(_MSC_VER)
#define RT_TIME_THREAD_LOCAL __declspec(thread)
#else
#define RT_TIME_THREAD_LOCAL _Thread_local __attribute__((tls_model("initial-exec")))
#endif

static RT_TIME_THREAD_LOCAL bool g_progress_initialized = false;
static RT_TIME_THREAD_LOCAL int64_t g_progress_start_nanos = 0;

double rt_time_now_seconds_f64(void) {
#ifdef _WIN32
    int64_t micros = rt_time_now_unix_micros();
    return micros < 0 ? -1.0 : (double)micros / 1000000.0;
#else
    struct timespec ts = {0, 0};
    if (clock_gettime(CLOCK_REALTIME, &ts) != 0) return -1.0;
    return (double)ts.tv_sec + (double)ts.tv_nsec / 1e9;
#endif
}

int64_t rt_progress_clock_now_nanos(void) {
#ifdef _WIN32
    return rt_time_now_nanos();
#else
    struct timespec now = {0, 0};
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) return -1;
    return (int64_t)now.tv_sec * 1000000000LL + (int64_t)now.tv_nsec;
#endif
}

bool rt_progress_tls_is_initialized(void) { return g_progress_initialized; }
int64_t rt_progress_tls_start_nanos(void) { return g_progress_start_nanos; }

void rt_progress_tls_store_start_nanos(int64_t start_nanos) {
    g_progress_start_nanos = start_nanos;
    g_progress_initialized = true;
}

void rt_progress_tls_clear(void) {
    g_progress_start_nanos = 0;
    g_progress_initialized = false;
}

/* The Rust seed cannot link Pure Simple modules. Keep its historical ABI as
 * an explicitly bootstrap-only compatibility lane; production Stage4 does
 * not define this macro and therefore has no duplicate policy provider. */
#ifdef SIMPLE_BOOTSTRAP_TIMESTAMP_COMPAT
#include "test/runtime_timestamp_calendar_oracle.c"
int32_t rt_timestamp_get_year(int64_t v) { return rt_timestamp_oracle_get_year(v); }
int32_t rt_timestamp_get_month(int64_t v) { return rt_timestamp_oracle_get_month(v); }
int32_t rt_timestamp_get_day(int64_t v) { return rt_timestamp_oracle_get_day(v); }
int32_t rt_timestamp_get_hour(int64_t v) { return rt_timestamp_oracle_get_hour(v); }
int32_t rt_timestamp_get_minute(int64_t v) { return rt_timestamp_oracle_get_minute(v); }
int32_t rt_timestamp_get_second(int64_t v) { return rt_timestamp_oracle_get_second(v); }
int32_t rt_timestamp_get_microsecond(int64_t v) { return rt_timestamp_oracle_get_microsecond(v); }
int64_t rt_timestamp_from_components(int32_t y, int32_t m, int32_t d, int32_t h,
                                     int32_t min, int32_t s, int32_t us) {
    return rt_timestamp_oracle_from_components(y, m, d, h, min, s, us);
}
int64_t rt_timestamp_add_days(int64_t v, int64_t d) { return rt_timestamp_oracle_add_days(v, d); }
int64_t rt_timestamp_diff_days(int64_t a, int64_t b) { return rt_timestamp_oracle_diff_days(a, b); }
/* rt_time_now_seconds: historical i64 ABI. Defined in runtime_time.c (the
 * designated C companion of time.rs, alongside its sibling clocks) since
 * 5362c2345c6; defining it here too made the seed link fail with a duplicate
 * symbol. See doc/08_tracking/bug/seed_rt_time_now_seconds_unlinkable_2026-08-28.md. */
bool rt_progress_init(void) {
    int64_t now = rt_progress_clock_now_nanos();
    if (now < 0) { rt_progress_tls_clear(); return false; }
    rt_progress_tls_store_start_nanos(now);
    return true;
}
bool rt_progress_reset(void) { return rt_progress_init(); }
double rt_progress_get_elapsed_seconds(void) {
    if (!rt_progress_tls_is_initialized()) {
        if (!rt_progress_init()) return -1.0;
        return 0.0;
    }
    int64_t now = rt_progress_clock_now_nanos();
    if (now < 0) return -1.0;
    int64_t elapsed = now - rt_progress_tls_start_nanos();
    return elapsed < 0 ? -1.0 : (double)elapsed / 1000000000.0;
}
#endif

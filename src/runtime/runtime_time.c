/*
 * Simple Runtime — Clock FFI Functions
 *
 * C equivalents of src/compiler_rust/runtime/src/value/ffi/time.rs.
 * Build: cc -c -fPIC -O2 -std=gnu11 runtime_time.c -o runtime_time.o
 */

#include <stdint.h>
#include <time.h>
#ifdef _WIN32
#include <windows.h>

static int64_t win_filetime_unix_micros(void) {
    FILETIME ft;
    GetSystemTimePreciseAsFileTime(&ft);
    ULARGE_INTEGER uli;
    uli.LowPart = ft.dwLowDateTime;
    uli.HighPart = ft.dwHighDateTime;
    if (uli.QuadPart < 116444736000000000ULL) return -1;
    uint64_t micros = (uli.QuadPart - 116444736000000000ULL) / 10ULL;
    return micros > (uint64_t)INT64_MAX ? -1 : (int64_t)micros;
}

static int64_t win_qpc_delta_to_nanos(int64_t delta_ticks, int64_t frequency) {
    if (delta_ticks <= 0 || frequency <= 0) {
        return 0;
    }
    int64_t seconds = delta_ticks / frequency;
    int64_t remainder = delta_ticks % frequency;
    if (seconds > INT64_MAX / 1000000000LL) {
        return -1;
    }
    int64_t nanos = seconds * 1000000000LL;
    if (remainder > INT64_MAX / 1000000000LL) return -1;
    int64_t fractional = (remainder * 1000000000LL) / frequency;
    return fractional > INT64_MAX - nanos ? -1 : nanos + fractional;
}

static INIT_ONCE win_qpc_once = INIT_ONCE_STATIC_INIT;
static LARGE_INTEGER win_qpc_frequency;

static BOOL CALLBACK win_qpc_init(PINIT_ONCE once, PVOID parameter, PVOID* context) {
    (void)once;
    (void)parameter;
    (void)context;
    return QueryPerformanceFrequency(&win_qpc_frequency);
}

static int64_t win_monotonic_nanos(void) {
    LARGE_INTEGER now;
    if (!InitOnceExecuteOnce(&win_qpc_once, win_qpc_init, NULL, NULL) ||
        !QueryPerformanceCounter(&now)) return -1;
    return win_qpc_delta_to_nanos(
        (int64_t)now.QuadPart, (int64_t)win_qpc_frequency.QuadPart);
}
#endif

/* ---- Wall clock: microseconds since Unix epoch ---- */
int64_t rt_time_now_unix_micros(void) {
#ifdef _WIN32
    return win_filetime_unix_micros();
#else
    struct timespec ts = {0, 0};
    if (clock_gettime(CLOCK_REALTIME, &ts) != 0) return -1;
    if (ts.tv_sec < 0 || (int64_t)ts.tv_sec > INT64_MAX / 1000000LL) return -1;
    if ((int64_t)ts.tv_sec == INT64_MAX / 1000000LL &&
        ts.tv_nsec / 1000 > INT64_MAX % 1000000LL) return -1;
    return (int64_t)ts.tv_sec * 1000000LL + ts.tv_nsec / 1000;
#endif
}

/* ---- Monotonic clock: nanoseconds from process-local epoch ---- */
int64_t rt_time_now_nanos(void) {
#ifdef _WIN32
    return win_monotonic_nanos();
#else
    struct timespec now = {0, 0};
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) return -1;
    if (now.tv_sec < 0 || (int64_t)now.tv_sec > INT64_MAX / 1000000000LL) return -1;
    if ((int64_t)now.tv_sec == INT64_MAX / 1000000000LL &&
        now.tv_nsec > INT64_MAX % 1000000000LL) return -1;
    return (int64_t)now.tv_sec * 1000000000LL + (int64_t)now.tv_nsec;
#endif
}

/* ---- Monotonic clock: microseconds (= nanos / 1000) ---- */
int64_t rt_time_now_micros(void) {
    int64_t nanos = rt_time_now_nanos();
    return nanos < 0 ? -1 : nanos / 1000;
}

/* ---- Monotonic clock: milliseconds (= nanos / 1000000) ---- */
int64_t rt_time_now_monotonic_ms(void) {
    int64_t nanos = rt_time_now_nanos();
    return nanos < 0 ? -1 : nanos / 1000000;
}

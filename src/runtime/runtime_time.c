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
    return (int64_t)((uli.QuadPart - 116444736000000000ULL) / 10ULL);
}

static int64_t win_qpc_delta_to_nanos(int64_t delta_ticks, int64_t frequency) {
    if (delta_ticks <= 0 || frequency <= 0) {
        return 0;
    }
    int64_t seconds = delta_ticks / frequency;
    int64_t remainder = delta_ticks % frequency;
    if (seconds > INT64_MAX / 1000000000LL) {
        return INT64_MAX;
    }
    int64_t nanos = seconds * 1000000000LL;
    return nanos + (int64_t)((remainder * 1000000000LL) / frequency);
}

static int64_t win_monotonic_nanos(void) {
    static LARGE_INTEGER freq;
    static LARGE_INTEGER start;
    static int initialized = 0;
    LARGE_INTEGER now;
    if (!initialized) {
        QueryPerformanceFrequency(&freq);
        QueryPerformanceCounter(&start);
        initialized = 1;
    }
    QueryPerformanceCounter(&now);
    return win_qpc_delta_to_nanos((int64_t)(now.QuadPart - start.QuadPart), (int64_t)freq.QuadPart);
}
#endif

/* ---- Wall clock: microseconds since Unix epoch ---- */
int64_t rt_time_now_unix_micros(void) {
#ifdef _WIN32
    return win_filetime_unix_micros();
#else
    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    return (int64_t)ts.tv_sec * 1000000LL + ts.tv_nsec / 1000;
#endif
}

/* ---- Monotonic clock: nanoseconds from process-local epoch ---- */
int64_t rt_time_now_nanos(void) {
#ifdef _WIN32
    return win_monotonic_nanos();
#else
    static struct timespec start;
    static int initialized = 0;
    if (!initialized) {
        clock_gettime(CLOCK_MONOTONIC, &start);
        initialized = 1;
    }
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    int64_t diff = (int64_t)(now.tv_sec - start.tv_sec) * 1000000000LL
                 + (int64_t)(now.tv_nsec - start.tv_nsec);
    return diff < 0 ? 0 : diff;
#endif
}

/* ---- Monotonic clock: microseconds (= nanos / 1000) ---- */
int64_t rt_time_now_micros(void) {
    return rt_time_now_nanos() / 1000;
}

/* Windows: runtime_time.c takes its `#ifdef _WIN32` branch and never calls clock_gettime,
 * so the behaviour exercised below does not exist on this platform.  The file is
 * still fed to the compiler by scripts/check/check-c-runtime-compiles-push.shs and
 * still proves it parses; it compiles to a well-formed no-op rather than being
 * excluded from the scan.  The POSIX body below is unchanged. */
#if defined(_WIN32)
int main(void) { return 0; }
#else
#include <stdint.h>
#include <time.h>

static int rt_test_clock_gettime(clockid_t clock_id, struct timespec *value) {
    (void)clock_id;
    if (value) {
        value->tv_sec = 123;
        value->tv_nsec = 456;
    }
    return -1;
}

#define clock_gettime rt_test_clock_gettime
#include "../runtime_time.c"
#undef clock_gettime

int main(void) {
    if (rt_time_now_unix_micros() != -1) return 1;
    if (rt_time_now_nanos() != -1) return 2;
    if (rt_time_now_micros() != -1) return 3;
    if (rt_time_now_monotonic_ms() != -1) return 4;
    return 0;
}
#endif /* !_WIN32 */

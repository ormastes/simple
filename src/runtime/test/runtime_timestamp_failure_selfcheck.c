#include <stdbool.h>
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
#include "../runtime_timestamp.c"
#undef clock_gettime

int main(void) {
    if (rt_time_now_seconds_f64() != -1.0) return 1;
    if (rt_progress_init()) return 2;
    if (rt_progress_reset()) return 3;
    if (rt_progress_get_elapsed_seconds() != -1.0) return 4;
    return 0;
}

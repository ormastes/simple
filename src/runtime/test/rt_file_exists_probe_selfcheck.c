#define SIMPLE_RUNTIME_TESTING 1
#include "../runtime.h"

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

/* This harness is linked once against runtime.c and once against
 * runtime_native.c.  It uses a PID-isolated path which must already be absent;
 * it never creates or deletes that fixture.  The runtime's testing hooks expose
 * counter/generation seeding, but deliberately do not expose a controllable
 * post-admission, pre-I/O lease barrier.  Therefore this checks the observable
 * close lifecycle and all token/error contracts without synthesizing an I/O
 * implementation or reaching into the provider's private probe state. */
int main(void) {
    char missing[160];
    int written = snprintf(
        missing, sizeof(missing),
        "/tmp/simple_rt_file_exists_probe_selfcheck_%ld", (long)getpid());
    if (written < 0 || (size_t)written >= sizeof(missing)) return 10;
    if (access(missing, F_OK) == 0 || errno != ENOENT) return 11;

    /* A second begin must not overlap the accepting session. */
    int64_t first = rt_file_exists_probe_begin();
    if (first <= 0) return 12;
    if (rt_file_exists_probe_begin() != -1) return 13;
    if (rt_file_exists_probe_end(first) != 0) return 14;

    /* Closed sessions reject their stale/non-reusable tokens.  A call while
     * closed remains a real facade call, then the next session must start with
     * a fresh empty snapshot. */
    if (rt_file_exists((const uint8_t*)missing, strlen(missing)) != 0) return 15;
    int64_t second = rt_file_exists_probe_begin();
    if (second <= first) return 16;
    if (rt_file_exists_probe_end(first) != -2) return 17;
    if (rt_file_exists_probe_end(second) != 0) return 18;
    if (rt_file_exists_probe_end(second) != -2) return 19;

    /* A max-1 seeded counter accepts one failed probe and then saturates both
     * packed fields, rather than wrapping or admitting failed > total. */
    int64_t token = rt_file_exists_probe_begin();
    if (token <= second) return 20;
    if (rt_file_exists_probe_test_seed_counters(
            INT64_C(0x7ffffffe), INT64_C(0x7ffffffe)) != 0) return 21;
    if (rt_file_exists((const uint8_t*)missing, strlen(missing)) != 0) return 22;
    if (rt_file_exists((const uint8_t*)missing, strlen(missing)) != 0) return 23;

    int64_t packed = rt_file_exists_probe_end(token);
    if (packed < 0 || (packed >> 32) != INT64_C(0x7fffffff) ||
        (packed & INT64_C(0xffffffff)) != INT64_C(0x7fffffff)) return 24;

    /* The test-only generation seed makes the non-wrapping terminal case
     * practical: MAX is a valid final token, then begin fails closed. */
    if (rt_file_exists_probe_test_seed_generation(
            INT64_C(0x7ffffffffffffffe)) != 0) return 25;
    int64_t maximum = rt_file_exists_probe_begin();
    if (maximum != INT64_C(0x7fffffffffffffff)) return 26;
    if (rt_file_exists_probe_end(maximum) != 0) return 27;
    if (rt_file_exists_probe_begin() != -3) return 28;
    return 0;
}

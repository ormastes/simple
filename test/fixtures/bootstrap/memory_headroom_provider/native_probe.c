/* Link once with the genuine Rust058 archive plus runtime_memory_headroom.o,
 * then once with the canonical core-C capsule archive. The oracle is sampled
 * on both sides of the provider call so host pressure during the probe is
 * tolerated without accepting the generated `return 3` fallback. */
#include "runtime.h"
#include <windows.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static unsigned checks;

static void checked(int ok, const char* label) {
    checks++;
    if (!ok) {
        fprintf(stderr, "memory-headroom check=%u failed: %s\n", checks, label);
        exit(1);
    }
}

static int64_t oracle(void) {
    MEMORYSTATUSEX status;
    memset(&status, 0, sizeof(status));
    status.dwLength = sizeof(status);
    if (!GlobalMemoryStatusEx(&status)) return 0;
    uint64_t headroom = status.ullAvailPhys < status.ullAvailPageFile
        ? status.ullAvailPhys
        : status.ullAvailPageFile;
    if (headroom > (uint64_t)INT64_MAX) return 0;
    return (int64_t)headroom;
}

int main(void) {
    static const uint8_t runtime_marker[] = "memory-headroom-probe";
    int64_t boxed = rt_string_new_literal(runtime_marker, sizeof(runtime_marker) - 1);
    checked(boxed != 0, "runtime string ABI links");
    rt_string_free(boxed);

    int64_t before = oracle();
    int64_t actual = rt_host_memory_headroom_bytes_v1();
    int64_t after = oracle();
    checked(before > 3 && after > 3, "OS oracle is available");
    checked(actual > 3, "provider is a measured value, not fallback three");

    int64_t low = before < after ? before : after;
    int64_t high = before > after ? before : after;
    int64_t tolerance = (256LL * 1024 * 1024) + high / 16;
    int64_t delta = actual < low ? low - actual : actual > high ? actual - high : 0;
    checked(delta <= tolerance, "provider matches pressure-tolerant OS oracle");

    printf("memory-headroom-provider assertions=%u before=%" PRId64
           " actual=%" PRId64 " after=%" PRId64 " tolerance=%" PRId64 "\n",
           checks, before, actual, after, tolerance);
    return 0;
}

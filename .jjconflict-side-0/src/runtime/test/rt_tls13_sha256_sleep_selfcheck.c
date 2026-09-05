#include "../runtime.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

static int failures = 0;

static void check_digest(const uint8_t* input, size_t input_len,
                         const uint8_t expected[32]) {
    SplArray* bytes = rt_byte_array_new_len((uint64_t)input_len);
    for (size_t i = 0; i < input_len; i++) {
        if (!rt_bytes_u8_set(bytes, (int64_t)i, (int64_t)input[i])) {
            failures++;
            return;
        }
    }
    int64_t digest_value = rt_tls13_sha256((int64_t)(uintptr_t)bytes);
    SplArray* digest = (SplArray*)(uintptr_t)digest_value;
    if (rt_array_len(digest) != 32) {
        failures++;
        return;
    }
    for (int64_t i = 0; i < 32; i++) {
        if (rt_bytes_u8_at(digest, i) != expected[i]) {
            failures++;
            return;
        }
    }
}

int main(void) {
    static const uint8_t empty_digest[32] = {
        0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
        0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
        0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
        0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55
    };
    static const uint8_t abc_digest[32] = {
        0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
        0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
        0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
        0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad
    };
    static const uint8_t abc[3] = {'a', 'b', 'c'};

    check_digest(NULL, 0, empty_digest);
    check_digest(abc, sizeof(abc), abc_digest);

    struct timespec before;
    struct timespec after;
    if (clock_gettime(CLOCK_MONOTONIC, &before) != 0) failures++;
    rt_sleep_nanos(1000000);
    if (clock_gettime(CLOCK_MONOTONIC, &after) != 0) failures++;
    int64_t elapsed_ns =
        (int64_t)(after.tv_sec - before.tv_sec) * 1000000000LL +
        (int64_t)(after.tv_nsec - before.tv_nsec);
    if (elapsed_ns <= 0) failures++;

    printf("SELFCHECK %s (%d failures)\n",
           failures == 0 ? "PASSED" : "FAILED", failures);
    return failures == 0 ? 0 : 1;
}

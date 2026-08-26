#define _POSIX_C_SOURCE 200809L
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

static int read_monotonic_ns(uint64_t *value) {
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) return 1;
    *value = (uint64_t)now.tv_sec * UINT64_C(1000000000) + (uint64_t)now.tv_nsec;
    return *value == 0;
}

int main(int argc, char **argv) {
    uint64_t first;
    if (read_monotonic_ns(&first) != 0) return 1;
    if (argc == 1) {
        printf("%" PRIu64 "\n", first);
        return 0;
    }
    if (argc == 2 && strcmp(argv[1], "--self-test") == 0) {
        const struct timespec delay = {0, 1000000};
        uint64_t second;
        if (nanosleep(&delay, NULL) != 0 || read_monotonic_ns(&second) != 0 || second <= first) return 1;
        puts("STATUS: PASS rust-go-benchmark-monotonic-ns");
        return 0;
    }
    return 2;
}

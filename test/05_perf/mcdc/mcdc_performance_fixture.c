/* Controlled fixture for check-mcdc-performance-gate.shs contract testing. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef POST_SEAL_ALLOC_COUNT
#define POST_SEAL_ALLOC_COUNT 0
#endif

static int write_receipt(const char *path) {
    FILE *f = fopen(path, "wb");
    if (f == NULL) return 20;
    if (fprintf(f,
            "coverage_alloc_count=0\n"
            "coverage_alloc_bytes=0\n"
            "post_seal_alloc_count=%d\n"
            "post_seal_alloc_bytes=0\n"
            "event_capacity_bytes=0\n"
            "log_capacity_bytes=0\n"
            "mapped_pack_count=0\n"
            "overflow=0\n"
            "evidence_loss=0\n", POST_SEAL_ALLOC_COUNT) < 0) return 21;
    return fclose(f) == 0 ? 0 : 22;
}

int main(int argc, char **argv) {
    uint64_t iterations = 0;
    const char *receipt = NULL;
    for (int i = 1; i + 1 < argc; i += 2) {
        if (strcmp(argv[i], "--mcdc-perf-iterations") == 0)
            iterations = strtoull(argv[i + 1], NULL, 10);
        else if (strcmp(argv[i], "--mcdc-allocation-receipt") == 0)
            receipt = argv[i + 1];
        else
            return 10;
    }
    if (iterations == 0 || receipt == NULL) return 11;
    volatile uint64_t value = UINT64_C(0x9e3779b97f4a7c15);
    for (uint64_t i = 0; i < iterations; ++i)
        value = (value ^ i) * UINT64_C(0xbf58476d1ce4e5b9);
    printf("oracle=%llu\n", (unsigned long long)value);
    return write_receipt(receipt);
}

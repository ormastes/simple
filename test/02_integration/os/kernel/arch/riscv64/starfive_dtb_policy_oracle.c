#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define FDT_MAGIC UINT32_C(0xd00dfeed)
#define FALLBACK_DTB UINT64_C(0x42200000)

/* Frozen independent oracle: scalar transcription of the pre-migration C
 * selection order, with memory acquisition deliberately removed. */
__attribute__((noinline)) static uint64_t
legacy_select(uint64_t candidate, uint32_t candidate_magic,
              uint32_t fallback_magic) {
    if (candidate != 0 && candidate_magic == FDT_MAGIC) return candidate;
    if (fallback_magic == FDT_MAGIC) return FALLBACK_DTB;
    return 0;
}

static int run_vectors(const char *path) {
    FILE *input = fopen(path, "r");
    if (input == NULL) return 2;
    char line[256];
    unsigned rows = 0;
    while (fgets(line, sizeof line, input) != NULL) {
        char name[64];
        uint64_t candidate, expected;
        uint32_t candidate_magic, fallback_magic;
        if (sscanf(line, "%63[^,],%" SCNu64 ",%" SCNu32 ",%" SCNu32
                         ",%" SCNu64,
                   name, &candidate, &candidate_magic, &fallback_magic,
                   &expected) != 5) {
            fclose(input);
            return 3;
        }
        uint64_t selected = legacy_select(candidate, candidate_magic, fallback_magic);
        if (selected != expected) {
            fclose(input);
            return 4;
        }
        printf("%s,%" PRIu64 "\n", name, selected);
        rows++;
    }
    fclose(input);
    return rows == 8 ? 0 : 5;
}

static int run_bench(uint64_t iterations) {
    uint64_t checksum = 0;
    for (uint64_t i = 0; i < iterations; ++i) {
        uint64_t candidate = (i & 3) == 0 ? 0 : (UINT64_C(0x80000000) + i);
        uint32_t candidate_magic = (i & 1) == 0 ? FDT_MAGIC : 0;
        uint32_t fallback_magic = (i & 7) == 0 ? FDT_MAGIC : 0;
        checksum += legacy_select(candidate, candidate_magic, fallback_magic);
    }
    printf("checksum=%" PRIu64 "\n", checksum);
    return 0;
}

int main(int argc, char **argv) {
    if (argc == 3 && strcmp(argv[1], "--bench") == 0)
        return run_bench(strtoull(argv[2], NULL, 10));
    if (argc != 2) return 64;
    return run_vectors(argv[1]);
}

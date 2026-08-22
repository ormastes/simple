/* Host-side memory model for the Pure-Simple streaming source-owner lifecycle.
 * This does not implement compiler behavior.  It models the exact ownership
 * shape: one original buffer plus one independent owner copy per physical
 * source, with logical aliases sharing the owner copy. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PHYSICAL_SOURCES 128
#define LOGICAL_ALIASES_PER_SOURCE 3
#define SOURCE_BYTES (256 * 1024)

int main(void) {
    char *originals[PHYSICAL_SOURCES];
    char *owners[PHYSICAL_SOURCES];
    char *aliases[PHYSICAL_SOURCES * LOGICAL_ALIASES_PER_SOURCE];
    uint64_t original_bytes = 0;
    uint64_t owner_bytes = 0;

    for (size_t i = 0; i < PHYSICAL_SOURCES; i++) {
        originals[i] = malloc(SOURCE_BYTES);
        owners[i] = malloc(SOURCE_BYTES);
        if (!originals[i] || !owners[i]) return 2;
        memset(originals[i], (int)i, SOURCE_BYTES);
        memcpy(owners[i], originals[i], SOURCE_BYTES);
        original_bytes += SOURCE_BYTES;
        owner_bytes += SOURCE_BYTES;
        for (size_t alias = 0; alias < LOGICAL_ALIASES_PER_SOURCE; alias++)
            aliases[i * LOGICAL_ALIASES_PER_SOURCE + alias] = owners[i];
    }

    const uint64_t retained_before = original_bytes + owner_bytes;
    for (size_t i = 0; i < PHYSICAL_SOURCES; i++) {
        free(owners[i]);
        owners[i] = NULL;
    }
    owner_bytes = 0;
    memset(aliases, 0, sizeof aliases); /* drop dangling logical aliases */
    const uint64_t retained_after = original_bytes + owner_bytes;

    printf("physical_sources=%d\n", PHYSICAL_SOURCES);
    printf("logical_aliases=%d\n", PHYSICAL_SOURCES * LOGICAL_ALIASES_PER_SOURCE);
    printf("retained_before_bytes=%llu\n", (unsigned long long)retained_before);
    printf("retained_after_bytes=%llu\n", (unsigned long long)retained_after);
    printf("reclaimed_owner_bytes=%llu\n",
           (unsigned long long)(retained_before - retained_after));
    printf("owner_allocations_after=0\n");

    for (size_t i = 0; i < PHYSICAL_SOURCES; i++) free(originals[i]);
    return retained_before == 2 * retained_after && retained_after > 0 ? 0 : 1;
}

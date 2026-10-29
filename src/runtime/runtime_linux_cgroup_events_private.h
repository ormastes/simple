/* Parse cgroup v2 subtree occupancy without accepting ambiguous evidence. */
#ifndef RUNTIME_LINUX_CGROUP_EVENTS_PRIVATE_H
#define RUNTIME_LINUX_CGROUP_EVENTS_PRIVATE_H
#include <stddef.h>
#include <string.h>
static int rt_lg_parse_populated(const char *bytes, size_t length, int *populated) {
    if (!bytes || !populated) return 0;
    size_t pos = 0; int found = 0, frozen_found = 0, value = 0;
    while (pos < length) {
        size_t start = pos;
        while (pos < length && bytes[pos] != '\n') {
            if (bytes[pos] == '\0') return 0;
            pos++;
        }
        /* A partial final record is not a complete kernel observation. */
        if (pos == length) return 0;
        size_t count = pos - start;
        if (count == 11 && memcmp(bytes + start, "populated ", 10) == 0) {
            if (found || (bytes[start + 10] != '0' && bytes[start + 10] != '1')) return 0;
            value = bytes[start + 10] == '1'; found = 1;
        } else if (count == 8 && memcmp(bytes + start, "frozen ", 7) == 0) {
            if (frozen_found || (bytes[start + 7] != '0' && bytes[start + 7] != '1')) return 0;
            frozen_found = 1;
        } else {
            /* Unknown schema requires explicit admission, never empty proof. */
            return 0;
        }
        pos++;
    }
    if (!found) return 0;
    *populated = value; return 1;
}
#endif

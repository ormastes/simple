/* Parse cgroup v2 subtree occupancy without accepting ambiguous evidence. */
#ifndef RUNTIME_LINUX_CGROUP_EVENTS_PRIVATE_H
#define RUNTIME_LINUX_CGROUP_EVENTS_PRIVATE_H
#include <stddef.h>
#include <string.h>
static int rt_lg_parse_populated(const char *bytes, size_t length, int *populated) {
    if (!bytes || !populated) return 0;
    size_t pos = 0; int found = 0, value = 0;
    while (pos < length) {
        size_t start = pos;
        while (pos < length && bytes[pos] != '\n') {
            if (bytes[pos] == '\0') return 0;
            pos++;
        }
        size_t count = pos - start;
        if (count >= 9 && memcmp(bytes + start, "populated", 9) == 0 &&
            (count == 9 || bytes[start + 9] == ' ' || bytes[start + 9] == '\t')) {
            if (found || count != 11 || bytes[start + 9] != ' ' || (bytes[start + 10] != '0' && bytes[start + 10] != '1')) return 0;
            value = bytes[start + 10] == '1'; found = 1;
        }
        if (pos < length) pos++;
    }
    if (!found) return 0;
    *populated = value; return 1;
}
#endif

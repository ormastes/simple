#include <stdint.h>
#include <stdio.h>
#include <string.h>

int64_t rt_cache_host_open_root_v1(const uint8_t *, int64_t);

static int rejected(const char *path) {
    return rt_cache_host_open_root_v1((const uint8_t *)path,
                                      (int64_t)strlen(path)) == -1;
}

int main(void) {
    const char *aliases[] = {"/", "/tmp/", "/tmp//cache",
                             "/tmp/./cache", "/tmp/../cache"};
    for (size_t i = 0; i < sizeof aliases / sizeof aliases[0]; ++i) {
        if (!rejected(aliases[i])) {
            fprintf(stderr, "accepted noncanonical cache root: %s\n", aliases[i]);
            return 1;
        }
    }
    return 0;
}

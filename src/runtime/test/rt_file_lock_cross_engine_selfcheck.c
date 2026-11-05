/* Process fixture for check-file-lock-cross-engine.shs. The linked runtime
 * provider is the production rt_file_lock/rt_file_unlock implementation. */
#include "../runtime.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

extern int64_t rt_file_lock(const uint8_t* path_ptr, uint64_t path_len, int64_t timeout_secs);
extern bool rt_file_unlock(int64_t handle);

static int write_result(const char* path, const char* text) {
    FILE* file = fopen(path, "wb");
    if (!file) return 0;
    size_t len = strlen(text);
    int ok = fwrite(text, 1, len, file) == len && fclose(file) == 0;
    return ok;
}

static int hold(const char* path, const char* ready, const char* release) {
    int64_t handle = rt_file_lock((const uint8_t*)path, strlen(path), 0);
    if (handle < 0) {
        write_result(ready, "ERROR");
        return 1;
    }
    if (!write_result(ready, "LOCKED")) {
        rt_file_unlock(handle);
        return 1;
    }
    for (int waited = 0; waited < 10000 && access(release, F_OK) != 0; waited += 50) {
        usleep(50000);
    }
    if (access(release, F_OK) != 0) {
        rt_file_unlock(handle);
        return 1;
    }
    return rt_file_unlock(handle) ? 0 : 1;
}

static int probe(const char* path, const char* output) {
    int64_t handle = rt_file_lock((const uint8_t*)path, strlen(path), 0);
    if (handle >= 0) {
        if (!rt_file_unlock(handle)) return 1;
        return write_result(output, "ACQUIRED") ? 0 : 1;
    }
    return write_result(output, "BUSY") ? 0 : 1;
}

int main(int argc, char** argv) {
    if (argc == 5 && strcmp(argv[1], "hold") == 0) return hold(argv[2], argv[3], argv[4]);
    if (argc == 4 && strcmp(argv[1], "probe") == 0) return probe(argv[2], argv[3]);
    fprintf(stderr, "usage: hold PATH READY RELEASE | probe PATH OUTPUT\n");
    return 64;
}

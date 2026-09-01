#include "runtime.h"
#if !defined(_WIN32)
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

int main(void) {
    char parent[] = "/tmp/simple-secure-stage-test-XXXXXX";
    assert(mkdtemp(parent) != NULL);
    int64_t value = rt_secure_temp_dir((const uint8_t*)parent, strlen(parent), (const uint8_t*)"llvm", 4);
    const char* staging = (const char*)rt_string_data(value);
    struct stat metadata;
    assert(staging && stat(staging, &metadata) == 0 && S_ISDIR(metadata.st_mode));
    assert((metadata.st_mode & 0777) == 0700);
    char source[320], destination[320];
    snprintf(source, sizeof(source), "%s/module.o", staging);
    snprintf(destination, sizeof(destination), "%s/module.o", parent);
    FILE* file = fopen(source, "wb");
    assert(file && fwrite("staged", 1, 6, file) == 6 && fclose(file) == 0);
    assert(rt_file_publish_noreplace((const uint8_t*)source, strlen(source), (const uint8_t*)destination, strlen(destination)) == 1);
    assert(access(source, F_OK) != 0 && access(destination, F_OK) == 0);
    file = fopen(source, "wb");
    assert(file && fclose(file) == 0);
    assert(rt_file_publish_noreplace((const uint8_t*)source, strlen(source), (const uint8_t*)destination, strlen(destination)) == 0);
    assert(access(source, F_OK) == 0);
    assert(rt_file_publish_noreplace((const uint8_t*)"/missing/staged", 15, (const uint8_t*)"/missing/destination", 20) == -1);
    assert(unlink(source) == 0 && unlink(destination) == 0 && rmdir(staging) == 0 && rmdir(parent) == 0);
    return 0;
}
#else
/* Windows behavior is exercised by the platform runtime lane; this POSIX
 * executable intentionally avoids Unix headers on Windows cross-builds. */
int main(void) { return 0; }
#endif

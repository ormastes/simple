#include <dlfcn.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

typedef long (*probe_fn)(void);

int64_t spl_dynlib_snapshot_linux(int64_t path_value);
int64_t spl_dlopen(int64_t path_value);
int64_t spl_dlclose(int64_t handle);

const char *rt_interp_cstr(int64_t value) {
    return (const char *)(intptr_t)value;
}

int main(int argc, char **argv) {
    if (argc != 4) {
        fprintf(stderr, "usage: %s PROVIDER REPLACEMENT EXPECTED\n", argv[0]);
        return 2;
    }
    char *end = NULL;
    errno = 0;
    long expected = strtol(argv[3], &end, 10);
    if (errno != 0 || end == argv[3] || *end != '\0') {
        fprintf(stderr, "invalid expected value\n");
        return 2;
    }
    int64_t snapshot = spl_dynlib_snapshot_linux((int64_t)(intptr_t)argv[1]);
    if (snapshot < 0) {
        fprintf(stderr, "snapshot failed\n");
        return 1;
    }
    errno = 0;
    if (write((int)snapshot, "x", 1) >= 0 || errno != EPERM) {
        fprintf(stderr, "snapshot is not write-sealed: %s\n", strerror(errno));
        close((int)snapshot);
        return 1;
    }
    if (rename(argv[2], argv[1]) != 0) {
        fprintf(stderr, "replacement rename failed: %s\n", strerror(errno));
        close((int)snapshot);
        return 1;
    }
    char descriptor_path[64];
    snprintf(descriptor_path, sizeof(descriptor_path), "/proc/self/fd/%lld",
             (long long)snapshot);
    int64_t raw_handle = spl_dlopen((int64_t)(intptr_t)descriptor_path);
    void *handle = (void *)(intptr_t)raw_handle;
    if (handle == NULL) {
        fprintf(stderr, "dlopen: %s\n", dlerror());
        close((int)snapshot);
        return 1;
    }
    void *address = dlsym(handle, "sffi_exact_probe");
    if (address == NULL) {
        fprintf(stderr, "dlsym: %s\n", dlerror());
        spl_dlclose(raw_handle);
        close((int)snapshot);
        return 1;
    }
    probe_fn probe = NULL;
    *(void **)(&probe) = address;
    long actual = probe();
    spl_dlclose(raw_handle);
    close((int)snapshot);
    if (actual != expected) {
        fprintf(stderr, "expected %ld, got %ld\n", expected, actual);
        return 1;
    }
    return 0;
}

/*
 * Core-C exports for symbols stranded in the uncompiled runtime.c.
 *
 * Group E of the Stage 2 Windows unresolved-symbol inventory
 * (doc/08_tracking/bug/stage2_windows_unresolved_inventory_2026-08-31.md):
 * seven rt_* entry points whose only definitions live in
 * src/runtime/runtime.c, which is NOT in the core-C source list
 * (native_project/tools.rs, build_c_runtime_library) and must not be added
 * wholesale -- measured, runtime.c's 121 rt_* definitions collide with 53
 * symbols in the core-C supplement objects and 69 in the Rust runtime
 * authority archives (same trap as the disproved "just add runtime_native.c"
 * fix, 8ca87866c6: 475 collisions). This TU therefore defines EXACTLY the
 * seven missing symbols, self-contained, with every helper static:
 *
 *   rt_mkdir, rt_random_i64,
 *   rt_readdir, rt_readdir_count, rt_readdir_entry, rt_readdir_free,
 *   rt_shell_output
 *
 * Unlike runtime.c (whose _WIN32 branch stubs readdir/mkdir to failure),
 * the Windows paths here are real implementations -- this lane exists
 * because the Windows MSVC Stage 2 link needs them.
 *
 * Verified zero-overlap (llvm-nm --defined-only, LC_ALL=C comm) against
 * core_c_bootstrap_supplement *.obj, simple_native_all.lib and
 * simple_compiler_backfill.lib before landing; keep it that way when
 * extending this file.
 */

#include "runtime.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <errno.h>

#ifdef _WIN32
#include <windows.h>
#include <direct.h>
#else
#include <dirent.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#endif

/* ---- directory listing (mirrors runtime.c's handle contract) ---- */

typedef struct {
    char** entries;
    int64_t count;
    int64_t cap;
} rt_core_dir_listing;

static rt_core_dir_listing* rt_core_dir_listing_new(void) {
    rt_core_dir_listing* dl = (rt_core_dir_listing*)calloc(1, sizeof(rt_core_dir_listing));
    if (!dl) return NULL;
    dl->cap = 64;
    dl->entries = (char**)malloc(sizeof(char*) * (size_t)dl->cap);
    if (!dl->entries) { free(dl); return NULL; }
    dl->count = 0;
    return dl;
}

static void rt_core_dir_listing_push(rt_core_dir_listing* dl, const char* name) {
    if (dl->count >= dl->cap) {
        dl->cap *= 2;
        char** grown = (char**)realloc(dl->entries, sizeof(char*) * (size_t)dl->cap);
        if (!grown) return;
        dl->entries = grown;
    }
    char* copy = (char*)malloc(strlen(name) + 1);
    if (!copy) return;
    memcpy(copy, name, strlen(name) + 1);
    dl->entries[dl->count++] = copy;
}

int64_t rt_readdir(const char* path) {
    if (!path) return 0;
#ifdef _WIN32
    size_t len = strlen(path);
    char* pattern = (char*)malloc(len + 3);
    if (!pattern) return 0;
    memcpy(pattern, path, len);
    while (len > 0 && (pattern[len - 1] == '\\' || pattern[len - 1] == '/')) len--;
    pattern[len] = '\\';
    pattern[len + 1] = '*';
    pattern[len + 2] = '\0';
    WIN32_FIND_DATAA fd;
    HANDLE h = FindFirstFileA(pattern, &fd);
    free(pattern);
    if (h == INVALID_HANDLE_VALUE) return 0;
    rt_core_dir_listing* dl = rt_core_dir_listing_new();
    if (!dl) { FindClose(h); return 0; }
    do {
        if (strcmp(fd.cFileName, ".") == 0 || strcmp(fd.cFileName, "..") == 0) continue;
        rt_core_dir_listing_push(dl, fd.cFileName);
    } while (FindNextFileA(h, &fd));
    FindClose(h);
    return (int64_t)(uintptr_t)dl;
#else
    DIR* d = opendir(path);
    if (!d) return 0;
    rt_core_dir_listing* dl = rt_core_dir_listing_new();
    if (!dl) { closedir(d); return 0; }
    struct dirent* ent;
    while ((ent = readdir(d)) != NULL) {
        if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0) continue;
        rt_core_dir_listing_push(dl, ent->d_name);
    }
    closedir(d);
    return (int64_t)(uintptr_t)dl;
#endif
}

int64_t rt_readdir_count(int64_t handle) {
    if (!handle) return 0;
    return ((rt_core_dir_listing*)(uintptr_t)handle)->count;
}

const char* rt_readdir_entry(int64_t handle, int64_t index) {
    if (!handle) return "";
    rt_core_dir_listing* dl = (rt_core_dir_listing*)(uintptr_t)handle;
    if (index < 0 || index >= dl->count) return "";
    return dl->entries[index];
}

void rt_readdir_free(int64_t handle) {
    if (!handle) return;
    rt_core_dir_listing* dl = (rt_core_dir_listing*)(uintptr_t)handle;
    for (int64_t i = 0; i < dl->count; i++) free(dl->entries[i]);
    free(dl->entries);
    free(dl);
}

/* ---- mkdir ---- */

int64_t rt_mkdir(const char* path, int64_t mode) {
#ifdef _WIN32
    (void)mode;
    if (!path) return -1;
    if (_mkdir(path) == 0) return 0;
    if (errno == EEXIST) return -(int64_t)EEXIST;
    return -(int64_t)errno;
#else
    if (!path) return -1;
    if (mode == 0) mode = 0755;
    return mkdir(path, (mode_t)mode) == 0 ? 0 : -(int64_t)errno;
#endif
}

/* ---- cryptographically random i64 (mirrors runtime.c) ---- */

int64_t rt_random_i64(void) {
#ifdef _WIN32
    /* BCryptGenRandom via LoadLibrary: no bcrypt.lib link dependency. */
    int64_t val = 0;
    typedef long (WINAPI *BCryptGenRandomFn)(void*, unsigned char*, unsigned long, unsigned long);
    HMODULE hLib = LoadLibraryA("bcrypt.dll");
    if (hLib) {
        BCryptGenRandomFn fn = (BCryptGenRandomFn)GetProcAddress(hLib, "BCryptGenRandom");
        if (fn) {
            /* BCRYPT_USE_SYSTEM_PREFERRED_RNG */
            fn(NULL, (unsigned char*)&val, sizeof(val), 0x00000002);
        }
        FreeLibrary(hLib);
    }
    return val;
#else
    int64_t val = 0;
    int fd = open("/dev/urandom", O_RDONLY);
    if (fd >= 0) {
        ssize_t n = read(fd, &val, sizeof(val));
        (void)n;
        close(fd);
    }
    return val;
#endif
}

/* ---- shell output capture (self-contained: spl_shell_output lives in the
*      uncompiled runtime.c, so it cannot be delegated to here) ---- */



const char* rt_shell_output(const char* cmd) {
#ifdef _WIN32
#define RT_CORE_POPEN _popen
#define RT_CORE_PCLOSE _pclose
#else
#define RT_CORE_POPEN popen
#define RT_CORE_PCLOSE pclose
#endif
    if (!cmd) return SPL_STRDUP("", "shell");
    FILE* pipe = RT_CORE_POPEN(cmd, "r");
    if (!pipe) return SPL_STRDUP("", "shell");
    char* buf = (char*)SPL_MALLOC(4096, "shell");
    int64_t buf_cap = 4096;
    int64_t pos = 0;
    char tmp[1024];
    while (fgets(tmp, sizeof(tmp), pipe)) {
        size_t chunk = strlen(tmp);
        while (pos + (int64_t)chunk + 1 > buf_cap) {
            buf_cap *= 2;
            buf = (char*)SPL_REALLOC(buf, buf_cap, "shell");
        }
        memcpy(buf + pos, tmp, chunk);
        pos += (int64_t)chunk;
    }
    buf[pos] = '\0';
    RT_CORE_PCLOSE(pipe);
    return buf;
#undef RT_CORE_POPEN
#undef RT_CORE_PCLOSE
}

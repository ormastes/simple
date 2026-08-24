/* Hosted dynamic loading for pure-Simple native binaries. */

#ifdef _WIN32
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#else
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>
#if defined(__linux__)
/* F_ADD_SEALS and the F_SEAL_* flags used by the artifact-sealing path below
 * are Linux-specific fcntl commands. glibc's <fcntl.h> exposes them only under
 * _GNU_SOURCE and only on new enough releases, so include the UAPI header
 * directly -- the same thing this block already does for memfd. Without it
 * `clang -fsyntax-only` and every native-build fail with "use of undeclared
 * identifier 'F_ADD_SEALS'".
 *
 * <linux/fcntl.h> canNOT be included here to get them: it pulls in
 * asm-generic/fcntl.h, which redefines `struct flock` against glibc's
 * <fcntl.h> above ("error: redefinition of 'flock'"). Define the constants
 * directly instead -- they are stable UAPI values that the kernel cannot
 * change without breaking every existing binary. */
#include <linux/memfd.h>
#include <sys/syscall.h>
/* Defensive fallbacks: these are stable UAPI constants, so defining them when
 * an older header omits them is safe and keeps the sealing path compiling. */
#ifndef F_ADD_SEALS
#define F_ADD_SEALS 1033
#endif
#ifndef F_SEAL_SEAL
#define F_SEAL_SEAL 0x0001
#endif
#ifndef F_SEAL_SHRINK
#define F_SEAL_SHRINK 0x0002
#endif
#ifndef F_SEAL_GROW
#define F_SEAL_GROW 0x0004
#endif
#ifndef F_SEAL_WRITE
#define F_SEAL_WRITE 0x0008
#endif
#endif
#endif

#include "runtime.h"

int64_t spl_dynlib_snapshot_linux(int64_t path_value) {
#if defined(__linux__)
    const char* path = rt_interp_cstr(path_value);
    if (!path) return -1;
    int source = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK);
    if (source < 0) return -1;
    struct stat source_stat;
    if (fstat(source, &source_stat) != 0 || !S_ISREG(source_stat.st_mode) ||
        source_stat.st_size < 0 || (uint64_t)source_stat.st_size > UINT64_C(1073741824)) {
        close(source);
        return -1;
    }
    int snapshot = (int)syscall(SYS_memfd_create, "simple-sffi-provider",
                                MFD_CLOEXEC | MFD_ALLOW_SEALING);
    if (snapshot < 0) { close(source); return -1; }
    uint8_t buffer[65536];
    uint64_t total = 0;
    for (;;) {
        ssize_t got = read(source, buffer, sizeof(buffer));
        if (got == 0) break;
        if (got < 0) {
            if (errno == EINTR) continue;
            close(source); close(snapshot); return -1;
        }
        if ((uint64_t)got > UINT64_C(1073741824) - total) {
            close(source); close(snapshot); return -1;
        }
        total += (uint64_t)got;
        ssize_t offset = 0;
        while (offset < got) {
            ssize_t put = write(snapshot, buffer + offset, (size_t)(got - offset));
            if (put < 0 && errno == EINTR) continue;
            if (put <= 0) { close(source); close(snapshot); return -1; }
            offset += put;
        }
    }
    if (total != (uint64_t)source_stat.st_size || close(source) != 0 ||
        lseek(snapshot, 0, SEEK_SET) < 0 ||
        fcntl(snapshot, F_ADD_SEALS,
              F_SEAL_WRITE | F_SEAL_GROW | F_SEAL_SHRINK | F_SEAL_SEAL) != 0) {
        close(snapshot);
        return -1;
    }
    return (int64_t)snapshot;
#else
    (void)path_value;
    return -1;
#endif
}

int64_t spl_dlopen(int64_t path_value) {
    const char* path = rt_interp_cstr(path_value);
    if (!path) return 0;
#ifdef _WIN32
    return (int64_t)(intptr_t)LoadLibraryA(path);
#else
    return (int64_t)(intptr_t)dlopen(path, RTLD_NOW | RTLD_LOCAL);
#endif
}

int64_t spl_dlsym(int64_t handle, int64_t name_value) {
    const char* name = rt_interp_cstr(name_value);
    if (!handle || !name) return 0;
#ifdef _WIN32
    return (int64_t)(intptr_t)GetProcAddress((HMODULE)(intptr_t)handle, name);
#else
    return (int64_t)(intptr_t)dlsym((void*)(intptr_t)handle, name);
#endif
}

int64_t spl_dlclose(int64_t handle) {
    if (!handle) return -1;
#ifdef _WIN32
    return FreeLibrary((HMODULE)(intptr_t)handle) ? 0 : -1;
#else
    return (int64_t)dlclose((void*)(intptr_t)handle);
#endif
}

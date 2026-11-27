/*
 * Small filesystem ABI providers for the Rust-hosted runtime archive.
 *
 * The monolithic core-C runtime owns the same symbols for application links;
 * this component is linked only into the Rust-hosted bootstrap runtime, where
 * pulling runtime.c would reintroduce hundreds of duplicate providers.
 */

#include <errno.h>
#include <stdint.h>
#include <sys/stat.h>

#if defined(_WIN32)
#include <direct.h>
#include <io.h>
#else
#include <unistd.h>
#endif

int64_t rt_remove(const char *path) {
    if (!path) return -1;

#if defined(_WIN32)
    struct _stat st;
    if (_stat(path, &st) != 0) return -(int64_t)errno;
    if ((st.st_mode & _S_IFMT) == _S_IFDIR)
        return _rmdir(path) == 0 ? 0 : -(int64_t)errno;
    return _unlink(path) == 0 ? 0 : -(int64_t)errno;
#else
    struct stat st;
    if (stat(path, &st) != 0) return -(int64_t)errno;
    if (S_ISDIR(st.st_mode))
        return rmdir(path) == 0 ? 0 : -(int64_t)errno;
    return unlink(path) == 0 ? 0 : -(int64_t)errno;
#endif
}

#if defined(_WIN32)
#include "platform/runtime_windows_private_atomic.h"
/* Rust mode-provider bridge: byte-slice ABI, not tagged text handles. */
int32_t rt_hosted_fs_private_atomic_write_utf8(const uint8_t *path, uint64_t path_len,
        const uint8_t *content, uint64_t content_len, int32_t mode) {
    if (!path || !path_len || path_len >= SIZE_MAX ||
            memchr(path, 0, (size_t)path_len) || (!content && content_len) ||
            content_len > SIZE_MAX) return 0;
    char *terminated = (char *)malloc((size_t)path_len + 1);
    if (!terminated) return 0;
    memcpy(terminated, path, (size_t)path_len);
    terminated[path_len] = 0;
    int ok = rt_win_private_atomic_write(terminated, content, (size_t)content_len, mode);
    free(terminated);
    return ok;
}
#endif

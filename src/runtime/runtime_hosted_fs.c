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

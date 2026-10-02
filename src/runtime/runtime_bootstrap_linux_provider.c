/* Hosted Rust seed's narrow Linux providers. The full C runtime owns these
 * entry points in runtime_native.c and runtime_thread.c; those translation
 * units cannot be linked into the Rust seed without duplicate rt_* owners. */
#include "runtime.h"
#include "runtime_thread.h"

#include <pthread.h>
#include <stdint.h>
#include <string.h>
#include <sys/stat.h>

int rt_dir_is_real_no_follow(const uint8_t* path_ptr, uint64_t path_len) {
    char path[4096];
    if ((!path_ptr && path_len != 0) || path_len >= sizeof(path)) return 0;
    if (path_len != 0) memcpy(path, path_ptr, (size_t)path_len);
    path[path_len] = '\0';
    if (!path[0]) return 0;
    struct stat st;
    return lstat(path, &st) == 0 && S_ISDIR(st.st_mode);
}

int64_t spl_thread_current_id(void) {
    return (int64_t)pthread_self();
}

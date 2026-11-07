/* Hosted non-Linux POSIX close uncertainty, authored NOT_RUN. Never relabel
 * this as Linux/Windows evidence. Actual descriptors are used and consumed by
 * the selected fault; production cannot know that, so quarantines generation. */
#if !(defined(__APPLE__) || defined(__FreeBSD__))
#error "requires an authorized macOS or FreeBSD native test slot"
#endif
#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
static int fault_once;
static int close_calls;
static int test_close(int fd) {
    ++close_calls;
    int result = close(fd) == 0;
    if (fault_once) { fault_once = 0; assert(result); errno = EINTR; return 0; }
    return result;
}
#define SPL_OWNED_LOCK_CLOSE_V2(h) test_close(h)
#include "../runtime_file_lock_owned_v2.h"
int main(void) {
    char root[] = "/tmp/simple-owned-unknown-XXXXXX";
    assert(mkdtemp(root));
    char path[256];
    assert(snprintf(path, sizeof(path), "%s/parent.lock", root) > 0);
    int64_t token = rt_file_lock_owned_acquire_v2((const uint8_t *)path, strlen(path), 0);
    assert(token > 0 && rt_file_lock_owned_state_v2(token) == 1);
    fault_once = 1;
    assert(rt_file_lock_owned_release_v2(token) == 3);
    assert(rt_file_lock_owned_state_v2(token) == 3);
    int closes = close_calls;
    assert(rt_file_lock_owned_release_v2(token) == 3 && close_calls == closes);
    assert(rt_file_lock_owned_acquire_v2((const uint8_t *)path, strlen(path), 0) == 0);
    assert(close_calls == closes);
    assert(unlink(path) == 0 && rmdir(root) == 0);
    return 0;
}

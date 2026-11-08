/* Authored native owner regressions. NOT_RUN: no compiler campaign authorized.
 * Faults wrap actual OS operations; no production fault environment exists. */
#if defined(__linux__)
#define _GNU_SOURCE 1
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/wait.h>
#include <unistd.h>
static int fail_unlock_once;
static int consumed_close_error_once;
static int native_unlock_calls;
static int native_close_calls;
static int test_unlock(int fd) {
    ++native_unlock_calls;
    if (fail_unlock_once) { fail_unlock_once = 0; errno = EIO; return 0; }
    return flock(fd, LOCK_UN) == 0;
}
static int test_close(int fd) {
    ++native_close_calls;
    int result = close(fd) == 0;
    if (consumed_close_error_once) {
        consumed_close_error_once = 0;
        assert(result); /* Linux has consumed the real descriptor. */
        errno = EINTR;
        return 0;
    }
    return result;
}
#define SPL_OWNED_LOCK_UNLOCK_V2(h, o) test_unlock(h)
#define SPL_OWNED_LOCK_CLOSE_V2(h) test_close(h)
#include "../runtime_file_lock_owned_v2.c"

static int64_t acquire(const char *path) {
    return rt_file_lock_owned_acquire_v2((const uint8_t *)path, strlen(path), 0);
}
int main(int argc, char **argv) {
    if (argc == 4 && strcmp(argv[1], "crash-owner") == 0) {
        int pipe_write = atoi(argv[3]);
        int64_t held = acquire(argv[2]);
        assert(held > 0);
        assert(write(pipe_write, &held, sizeof(held)) == sizeof(held));
        _exit(0); /* genuine process death with held native lock */
    }
    char root[] = "/tmp/simple-owned-lock-XXXXXX";
    assert(mkdtemp(root));
    char path[256];
    assert(snprintf(path, sizeof(path), "%s/parent.lock", root) > 0);
    int64_t first = acquire(path);
    assert(first > 0 && rt_file_lock_owned_state_v2(first) == 1);
    assert(acquire(path) == 0); /* real flock contention, not a fake adapter */
    int before_close = native_close_calls;
    fail_unlock_once = 1;
    assert(rt_file_lock_owned_release_v2(first) == 2);
    assert(native_close_calls == before_close);
    assert(rt_file_lock_owned_state_v2(first) == 1);
    assert(acquire(path) == 0);
    assert(rt_file_lock_owned_release_v2(first) == 1);
    int64_t second = acquire(path);
    assert(second > 0 && second != first);
    int before_unlock = native_unlock_calls;
    assert(rt_file_lock_owned_release_v2(first) == 0);
    assert(native_unlock_calls == before_unlock);
    assert(rt_file_lock_owned_state_v2(second) == 1);
    assert(acquire(path) == 0);
    consumed_close_error_once = 1;
    assert(rt_file_lock_owned_release_v2(second) == 4);
    assert(rt_file_lock_owned_state_v2(second) == 0);
    int64_t third = acquire(path);
    assert(third > 0 && third != second);
    before_close = native_close_calls;
    assert(rt_file_lock_owned_release_v2(second) == 0);
    assert(native_close_calls == before_close);
    assert(rt_file_lock_owned_state_v2(third) == 1);
    /* A copied generation in another process cannot unlock the parent's lock. */
    assert(spl_owned_lock_enter_v2());
    pid_t child = fork();
    assert(child >= 0);
    if (child == 0) {
        alarm(2); /* a regression deadlock fails rather than hanging forever */
        assert(rt_file_lock_owned_state_v2(third) == 3);
        assert(rt_file_lock_owned_release_v2(third) == 3);
        assert(acquire(path) == 0);
        _exit(0);
    }
    int status;
    assert(waitpid(child, &status, 0) == child && WIFEXITED(status) && WEXITSTATUS(status) == 0);
    spl_owned_lock_leave_v2();
    assert(acquire(path) == 0);
    assert(rt_file_lock_owned_release_v2(third) == 1);
    /* Process death closes the actual owner; no synthetic recovery receipt. */
    int pipefd[2];
    assert(pipe(pipefd) == 0);
    child = fork();
    assert(child >= 0);
    if (child == 0) {
        close(pipefd[0]);
        char pipe_argument[32];
        assert(snprintf(pipe_argument, sizeof(pipe_argument), "%d", pipefd[1]) > 0);
        execl("/proc/self/exe", argv[0], "crash-owner", path, pipe_argument, (char *)NULL);
        _exit(127);
    }
    close(pipefd[1]);
    int64_t child_token;
    assert(read(pipefd[0], &child_token, sizeof(child_token)) == sizeof(child_token));
    close(pipefd[0]);
    assert(waitpid(child, &status, 0) == child && WIFEXITED(status) && WEXITSTATUS(status) == 0);
    int64_t recovered = acquire(path);
    assert(recovered > 0);
    assert(rt_file_lock_owned_release_v2(recovered) == 1);
    assert(unlink(path) == 0 && rmdir(root) == 0);
    return 0;
}
#else
/* This authored file qualifies Linux semantics only; do not emit a fake pass
 * on other providers. Windows retained-close cases require their own runner. */
#error "runtime_file_lock_owned_v2_test requires a Linux native test slot"
#endif

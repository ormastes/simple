#include "../runtime_sosix_freebsd_reaper_v1.h"
#include <assert.h>
#if defined(__FreeBSD__)
#include <unistd.h>
static volatile sig_atomic_t test_child = -1;
static void cleanup_failure(int sig) {
    pid_t child = (pid_t)test_child;
    if (child > 0) {
        (void)kill(-child, SIGKILL);
        (void)kill(child, SIGKILL);
    }
    _exit(128 + sig);
}
#endif

int main(void) {
    uint32_t count = 99;
    assert(sosix_freebsd_reaper_kill_v1(NULL) < 0 && errno == EINVAL);
    assert(sosix_freebsd_reaper_status_v1(NULL) < 0 && errno == EINVAL);
#if defined(__FreeBSD__)
    /* The test process is a fresh supervisor; acquire before its first fork. */
    assert(signal(SIGALRM, cleanup_failure) != SIG_ERR);
    assert(signal(SIGABRT, cleanup_failure) != SIG_ERR);
    alarm(15);
    assert(sosix_freebsd_reaper_kill_v1(&count) < 0 && errno == EPERM && count == 99);
    assert(sosix_freebsd_reaper_acquire_v1() == 0);
    int ready[2];
    assert(pipe(ready) == 0);
    pid_t child = fork();
    assert(child >= 0);
    if (child == 0) {
        close(ready[0]);
        if (setsid() < 0) _exit(4);
        pid_t grandchild = fork();
        if (grandchild < 0) _exit(2);
        if (grandchild == 0) {
            if (write(ready[1], "x", 1) != 1) _exit(3);
            for (;;) pause();
        }
        for (;;) pause();
    }
    test_child = child;
    close(ready[1]);
    char byte;
    assert(read(ready[0], &byte, 1) == 1);
    close(ready[0]);
    assert(sosix_freebsd_reaper_status_v1(&count) == 0 && count >= 2);
    assert(sosix_freebsd_reaper_kill_v1(&count) == 0 && count >= 2);
    int status;
    while (waitpid(-1, &status, 0) > 0) { }
    assert(errno == ECHILD);
    test_child = -1;
    assert(sosix_freebsd_reaper_status_v1(&count) == 0 && count == 0);
    alarm(0);
#else
    assert(sosix_freebsd_reaper_acquire_v1() < 0 && errno == ENOTSUP);
    assert(sosix_freebsd_reaper_kill_v1(&count) < 0 && errno == ENOTSUP && count == 99);
    count = 99;
    assert(sosix_freebsd_reaper_status_v1(&count) < 0 && errno == ENOTSUP && count == 99);
#endif
    return 0;
}

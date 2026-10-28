/* Link this against runtime.c and runtime_legacy_core.c separately on macOS.
 * Each route must spawn the same child and reject invalid argument shapes. */
#include "runtime.h"

#if defined(__APPLE__)
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

static atomic_int thread_live = 1;

static void* keep_thread_live(void* unused) {
    (void)unused;
    while (atomic_load(&thread_live)) usleep(1000);
    return NULL;
}

static int fail(const char* reason) {
    fprintf(stderr, "rt_process_spawn_async: %s\n", reason);
    return 1;
}

static int descriptor_child(int sentinel, int absent) {
    errno = 0;
    if (fcntl(sentinel, F_GETFD) != -1 || errno != EBADF) return 81;
    for (int fd = 0; fd < 3; fd++) {
        int flags = fcntl(fd, F_GETFD);
        if (fd == absent) {
            if (flags != -1 || errno != EBADF) return 82;
        } else if (flags < 0) return 83;
    }
    if (absent < 0) {
        char input;
        if (read(0, &input, 1) != 1 || input != 'I' ||
            write(1, "O", 1) != 1 || write(2, "E", 1) != 1) return 84;
    }
    return 0;
}

static int descriptor_case(const char* self, int absent, int cloexec) {
    int saved[3], channels[3][2];
    for (int fd = 0; fd < 3; fd++) {
        saved[fd] = fcntl(fd, F_DUPFD_CLOEXEC, 3);
        if (saved[fd] < 0 || pipe(channels[fd]) != 0) return fail("pipe setup");
    }
    int sentinel = open("/dev/null", O_RDONLY);
    if (sentinel < 3 || write(channels[0][1], "I", 1) != 1) return fail("sentinel setup");
    for (int fd = 0; fd < 3; fd++)
        if (dup2(channels[fd][fd == 0 ? 0 : 1], fd) != fd) return fail("stdio setup");
    if (absent >= 0) {
        if (cloexec) (void)fcntl(absent, F_SETFD, FD_CLOEXEC);
        else (void)close(absent);
    }
    char sentinel_arg[32], absent_arg[32];
    snprintf(sentinel_arg, sizeof(sentinel_arg), "%d", sentinel);
    snprintf(absent_arg, sizeof(absent_arg), "%d", absent);
    const char* args[] = {"--descriptor-child", sentinel_arg, absent_arg};
    int64_t pid = rt_process_spawn_async(self, args, 3);
    for (int fd = 0; fd < 3; fd++) {
        if (dup2(saved[fd], fd) != fd) _exit(85);
        close(saved[fd]);
    }
    int status = 0;
    int failed = pid <= 0 || waitpid((pid_t)pid, &status, 0) != (pid_t)pid ||
        !WIFEXITED(status) || WEXITSTATUS(status) != 0;
    /* The parent retains its sentinel; only the child's copy must close. */
    if (fcntl(sentinel, F_GETFD) < 0) failed = 1;
    close(sentinel);
    for (int fd = 0; fd < 3; fd++) close(channels[fd][1]);
    if (!failed && absent < 0) {
        char output;
        if (read(channels[1][0], &output, 1) != 1 || output != 'O' ||
            read(channels[2][0], &output, 1) != 1 || output != 'E') failed = 1;
    }
    for (int fd = 0; fd < 3; fd++) close(channels[fd][0]);
    return failed ? fail("descriptor isolation/stdio contract") : 0;
}

int main(int argc, char** argv) {
    alarm(10);
    if (argc == 4 && strcmp(argv[1], "--descriptor-child") == 0)
        return descriptor_child(atoi(argv[2]), atoi(argv[3]));
    char self[PATH_MAX];
    if (!realpath(argv[0], self)) return fail("self path unavailable");
    const char* args[] = {"-c", "exit 7"};
    pthread_t thread;
    if (pthread_create(&thread, NULL, keep_thread_live, NULL) != 0)
        return fail("second thread unavailable");
    int64_t pid = rt_process_spawn_async("/bin/sh", args, 2);
    int failed = 0;
    if (pid <= 0) failed |= fail("spawn failed");
    int status = 0;
    if (pid > 0 && (waitpid((pid_t)pid, &status, 0) != (pid_t)pid ||
            !WIFEXITED(status) || WEXITSTATUS(status) != 7))
        failed |= fail("child exit mismatch");
    if (rt_process_spawn_async("/bin/sh", NULL, 1) != -1)
        failed |= fail("null argv accepted");
    const char* null_element[] = {"-c", NULL};
    if (rt_process_spawn_async("/bin/sh", null_element, 2) != -1)
        failed |= fail("null arg accepted");
    if (rt_process_spawn_async("/bin/sh", args, -1) != -1)
        failed |= fail("negative argc accepted");
    if (rt_process_spawn_async("/bin/sh", args, 32769) != -1)
        failed |= fail("oversized argc accepted");
    if (rt_process_spawn_async("/no-such-simple-spawn-selfcheck", NULL, 0) != -1)
        failed |= fail("missing executable accepted");
    failed |= descriptor_case(self, -1, 0);
    for (int fd = 0; fd < 3; fd++) {
        failed |= descriptor_case(self, fd, 0);
        failed |= descriptor_case(self, fd, 1);
    }
    atomic_store(&thread_live, 0);
    if (pthread_join(thread, NULL) != 0) failed |= fail("second thread join failed");
    return failed;
}
#else
int main(void) { return 77; /* unsupported: macOS-only */ }
#endif

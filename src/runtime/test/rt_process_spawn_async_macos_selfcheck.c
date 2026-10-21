/* Link this against runtime.c and runtime_legacy_core.c separately on macOS.
 * Each route must spawn the same child and reject invalid argument shapes. */
#include "runtime.h"

#if defined(__APPLE__)
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
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

int main(void) {
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
    atomic_store(&thread_live, 0);
    if (pthread_join(thread, NULL) != 0) failed |= fail("second thread join failed");
    return failed;
}
#else
int main(void) { return 77; /* unsupported: macOS-only */ }
#endif

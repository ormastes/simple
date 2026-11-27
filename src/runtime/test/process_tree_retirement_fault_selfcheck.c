/* Canonical session-owner retirement faults. Source/test authoring NOT_RUN.
 * Standalone fixture: include the actual owner with syscall interception only
 * in this translation unit; no production runtime hooks or replacement owner.
 * cc -Wall -Wextra -Werror -I src/runtime -o /tmp/ptree-retirement \
 *    src/runtime/test/process_tree_retirement_fault_selfcheck.c
 * /tmp/ptree-retirement
 * Parent alarm bounds the test; helpers have their own independent alarm.
 */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#if defined(__APPLE__) && !defined(_DARWIN_C_SOURCE)
#define _DARWIN_C_SOURCE
#endif
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if !defined(_WIN32)
#include <signal.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static int fault_mode;
static pid_t fault_pid;
static int observed_reap;
static int injected_calls;
enum { F_NONE, F_SIGNAL_DENIED, F_WAIT_DEADLINE, F_WAIT_ERROR,
       F_WAIT_INTERRUPTED, F_POST_REAP_ENUM, F_CLOCK_ERROR };
static int test_kill(pid_t pid, int sig);
static pid_t test_waitpid(pid_t pid, int *status, int options);
static void *test_malloc(size_t size);
static int test_clock_gettime(clockid_t clock_id, struct timespec *value);
#define kill test_kill
#define waitpid test_waitpid
#define malloc test_malloc
#define clock_gettime test_clock_gettime
#endif
#include "../runtime_process_tree.c"
#if !defined(_WIN32)
#undef kill
#undef waitpid
#undef malloc
#undef clock_gettime

static int test_kill(pid_t pid, int sig) {
    if (fault_mode == F_SIGNAL_DENIED && pid == fault_pid && sig == SIGKILL) {
        injected_calls++; errno = EPERM; return -1;
    }
    return kill(pid, sig);
}
static pid_t test_waitpid(pid_t pid, int *status, int options) {
    if (pid == fault_pid && options == WNOHANG) {
        if (fault_mode == F_WAIT_DEADLINE) { injected_calls++; return 0; }
        if (fault_mode == F_WAIT_ERROR) { injected_calls++; errno = EIO; return -1; }
        if (fault_mode == F_WAIT_INTERRUPTED) {
            struct timespec pause = {0, 1000000L};
            nanosleep(&pause, NULL);
            injected_calls++; errno = EINTR; return -1;
        }
    }
    pid_t result = waitpid(pid, status, options);
    if (result == fault_pid) observed_reap = 1;
    return result;
}
static void *test_malloc(size_t size) {
    if (fault_mode == F_POST_REAP_ENUM && observed_reap) {
        injected_calls++; errno = ENOMEM; return NULL;
    }
    return malloc(size);
}
static int test_clock_gettime(clockid_t clock_id, struct timespec *value) {
    if (fault_mode == F_CLOCK_ERROR) {
        injected_calls++; errno = EIO; return -1;
    }
    return clock_gettime(clock_id, value);
}
#endif

static int failures;
#define CHECK(condition, label) do { \
    if (!(condition)) { failures++; fprintf(stderr, "FAIL %s\n", label); } \
    else fprintf(stderr, "ok %s\n", label); \
} while (0)

#if !defined(_WIN32)
static int64_t spawn_helper(const char *binary, const char *ready) {
    unlink(ready);
    const char *args[] = {"--ignore-term", ready};
    int64_t pid = rt_process_spawn_session(binary, args, 2);
    if (pid <= 1) return pid;
    for (int i = 0; i < 200; i++) {
        if (access(ready, F_OK) == 0) return pid;
        struct timespec pause = {0, 10000000L};
        nanosleep(&pause, NULL);
    }
    kill((pid_t)pid, SIGKILL);
    waitpid((pid_t)pid, NULL, 0);
    return -1;
}
static void check_fault(const char *binary, const char *ready, int mode,
                        int64_t expected, const char *label) {
    int64_t pid = spawn_helper(binary, ready);
    CHECK(pid > 1, "fault fixture launched through session owner");
    if (pid <= 1) return;
    fault_pid = (pid_t)pid; observed_reap = 0; injected_calls = 0;
    fault_mode = mode;
    int64_t result = rt_process_kill_tree(pid);
    fault_mode = F_NONE;
    CHECK(result == expected, label);
    CHECK(injected_calls > 0, "required fault actually reached canonical owner");
    if (mode == F_POST_REAP_ENUM) {
        CHECK(observed_reap, "post-reap failure has consumed leader ownership");
        errno = 0;
        CHECK(waitpid((pid_t)pid, NULL, WNOHANG) == -1 && errno == ECHILD,
              "post-reap sentinel must not permit another raw PID cleanup");
    } else {
        CHECK(!observed_reap, "ordinary failure did not consume leader wait ownership");
        CHECK(rt_process_kill_tree(pid) == 0, "retained owner can finish cleanup after fault removal");
        errno = 0;
        CHECK(waitpid((pid_t)pid, NULL, WNOHANG) == -1 && errno == ECHILD,
              "successful retry already reaped leader");
    }
    unlink(ready);
}
#endif

int main(int argc, char **argv) {
#if !defined(_WIN32)
    if (argc == 3 && strcmp(argv[1], "--ignore-term") == 0) {
        signal(SIGTERM, SIG_IGN);
        alarm(12); /* Independent bound even if the test parent dies. */
        FILE *ready = fopen(argv[2], "w");
        if (!ready) return 2;
        fputs("ready\n", ready); fclose(ready);
        for (;;) pause();
    }
#else
    (void)argc; (void)argv;
#endif
    if (rt_process_tree_support() != 0) {
        CHECK(rt_process_kill_tree(12345) == RT_PTREE_UNSUPPORTED,
              "unsupported owner cannot claim retirement");
        return failures ? 1 : 0;
    }
#if !defined(_WIN32)
    alarm(30);
    char directory[] = "/tmp/ptree_retirement_XXXXXX";
    if (!mkdtemp(directory)) return 2;
    char ready[256];
    snprintf(ready, sizeof(ready), "%s/ready", directory);
    int64_t pid = spawn_helper(argv[0], ready);
    CHECK(pid > 1, "real TERM-ignoring helper launched");
    if (pid > 1) {
        CHECK(kill((pid_t)pid, SIGTERM) == 0, "TERM delivered to ignoring helper");
        CHECK(rt_process_session_wait(pid, 25) == -2, "original timeout remains a failure");
        CHECK(rt_process_kill_tree(pid) == 0, "forced retirement succeeds without TERM grace");
        errno = 0;
        CHECK(waitpid((pid_t)pid, NULL, WNOHANG) == -1 && errno == ECHILD,
              "successful forced retirement already reaped leader");
    }
    check_fault(argv[0], ready, F_SIGNAL_DENIED, -EPERM, "signal denial refuses success");
    check_fault(argv[0], ready, F_WAIT_DEADLINE, -ETIMEDOUT, "reap deadline refuses success");
    check_fault(argv[0], ready, F_WAIT_ERROR, -EIO, "wait failure refuses success");
    check_fault(argv[0], ready, F_WAIT_INTERRUPTED, -ETIMEDOUT, "repeated EINTR cannot reset deadline");
    check_fault(argv[0], ready, F_POST_REAP_ENUM, RT_PTREE_SWEEP_FAILED_AFTER_REAP,
                "second sweep failure retains explicit partial-retirement result");
    check_fault(argv[0], ready, F_CLOCK_ERROR, -EIO, "clock failure cannot create an unbounded wait");
    unlink(ready); rmdir(directory); alarm(0);
#endif
    return failures ? 1 : 0;
}

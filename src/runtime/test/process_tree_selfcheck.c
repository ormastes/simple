/* Conformance check for runtime_process_tree.c: the session-owner contract.
 *
 * Build and run (any POSIX host with an owner arm):
 *   cc -Wall -Wextra -Werror -I src/runtime -o /tmp/ptree \
 *      src/runtime/test/process_tree_selfcheck.c src/runtime/runtime_process_tree.c && /tmp/ptree
 *
 * On a host without an owner (Windows, SimpleOS) every call must answer
 * RT_PTREE_UNSUPPORTED; the check then passes by asserting exactly that. */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#if defined(__APPLE__) && !defined(_DARWIN_C_SOURCE)
#define _DARWIN_C_SOURCE
#endif
#include "runtime_process_tree.h"

#include <errno.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if !defined(_WIN32)
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#endif

static int failures = 0;
#define CHECK(cond, ...) do { \
    if (!(cond)) { failures++; fprintf(stderr, "FAIL %s:%d: ", __FILE__, __LINE__); fprintf(stderr, __VA_ARGS__); fputc('\n', stderr); } \
    else { fprintf(stderr, "ok   "); fprintf(stderr, __VA_ARGS__); fputc('\n', stderr); } \
} while (0)

#if !defined(_WIN32)
static void sleep_ms(int ms) {
    struct timespec ts = { ms / 1000, (long)(ms % 1000) * 1000000L };
    while (nanosleep(&ts, &ts) != 0 && errno == EINTR) {}
}

static int alive(pid_t pid) {
    return kill(pid, 0) == 0 || errno == EPERM;
}

static pid_t read_pidfile(const char* path) {
    for (int i = 0; i < 100; i++) {
        FILE* f = fopen(path, "r");
        if (f) {
            long value = 0;
            int got = fscanf(f, "%ld", &value);
            fclose(f);
            if (got == 1 && value > 1) return (pid_t)value;
        }
        sleep_ms(50);
    }
    return -1;
}
#endif

int main(void) {
    int64_t support = rt_process_tree_support();
    if (support != 0) {
        /* No owner here: the whole family must say so, never succeed. */
        CHECK(support == RT_PTREE_UNSUPPORTED, "support reports unsupported (%lld)", (long long)support);
        const char* args[] = { "-c", "exit 0" };
        CHECK(rt_process_spawn_session("/bin/sh", args, 2) == RT_PTREE_UNSUPPORTED, "spawn_session unsupported");
        CHECK(rt_process_kill_session(12345, 9) == RT_PTREE_UNSUPPORTED, "kill_session unsupported");
        CHECK(rt_process_kill_tree(12345) == RT_PTREE_UNSUPPORTED, "kill_tree unsupported");
        CHECK(rt_process_session_wait(12345, 10) == RT_PTREE_UNSUPPORTED, "session_wait unsupported");
        CHECK(rt_process_session_is_running(12345) == RT_PTREE_UNSUPPORTED, "session_is_running unsupported");
        return failures ? 1 : 0;
    }
#if defined(_WIN32)
    CHECK(0, "owner reported on Windows: Job object is the owner there");
    return 1;
#else
    char pidfile[256];
    snprintf(pidfile, sizeof(pidfile), "/tmp/ptree_selfcheck_%ld.pid", (long)getpid());
    unlink(pidfile);

    /* 1. Spawn: the child is a session leader; an escaped grandchild (own
     *    process group, reparented to init) still carries the session id. */
    const char* script = "(set -m; sleep 300 & echo $! > \"$1\"); exec sleep 300";
    const char* args[] = { "-c", script, "ptree", pidfile };
    int64_t pid = rt_process_spawn_session("/bin/sh", args, 4);
    CHECK(pid > 1, "spawn_session returned pid %lld", (long long)pid);
    CHECK(getsid((pid_t)pid) == (pid_t)pid, "leader is its own session (sid %ld)", (long)getsid((pid_t)pid));
    CHECK(rt_process_session_is_running(pid) == 1, "leader is running");
    pid_t grandchild = read_pidfile(pidfile);
    CHECK(grandchild > 1, "grandchild pid recorded (%ld)", (long)grandchild);
    CHECK(alive(grandchild), "grandchild alive before kill");
    CHECK(getsid(grandchild) == (pid_t)pid, "grandchild shares the session");
    /* Fixture note, not a contract check: with job control (`set -m`, needs a
     * shell that honours it without a tty: macOS /bin/sh does, busybox ash
     * does not) the grandchild sits in its OWN process group, which is the
     * case a pgid kill cannot reach. Either way it must die below. */
    fprintf(stderr, "note grandchild pgid %ld vs leader pid %lld: escaped-group fixture %s\n",
            (long)getpgid(grandchild), (long long)pid,
            getpgid(grandchild) != (pid_t)pid ? "ACTIVE" : "not available in this sh");
    CHECK(rt_process_session_wait(pid, 50) == -2, "session_wait reports timeout while running");

    /* 2. Safety refusals. */
    CHECK(rt_process_kill_session((int64_t)getsid(0), SIGKILL) == -EINVAL, "refuses to kill the caller's own session");
    CHECK(rt_process_kill_session(1, SIGKILL) == -EINVAL, "refuses sid 1");
    CHECK(rt_process_kill_tree(grandchild) == RT_PTREE_NOT_SESSION_LEADER, "refuses a live pid that is not a session leader");
    CHECK(alive(grandchild), "refusal signalled nothing");

    /* 3. Kill the tree. Both must be gone; the leader must be reaped. */
    int64_t rc = rt_process_kill_tree(pid);
    CHECK(rc == 0, "kill_tree -> %lld", (long long)rc);
    int gone = 0;
    for (int i = 0; i < 50 && !gone; i++) {
        gone = !alive(grandchild);
        if (!gone) sleep_ms(20);
    }
    CHECK(gone, "escaped grandchild died");
    CHECK(rt_process_session_is_running(pid) == 0, "leader not running after kill");
    int64_t waited = rt_process_session_wait(pid, 100);
    CHECK(waited == -1, "leader already reaped by kill_tree (wait -> %lld)", (long long)waited);
    if (alive(grandchild)) kill(grandchild, SIGKILL);
    unlink(pidfile);

    /* 4. wait/exit-code contract for a normal exit and a signal death. */
    const char* exit_args[] = { "-c", "exit 7" };
    int64_t p2 = rt_process_spawn_session("/bin/sh", exit_args, 2);
    CHECK(p2 > 1, "spawn for exit code");
    CHECK(rt_process_session_wait(p2, 5000) == 7, "wait returns the exit code");
    const char* sig_args[] = { "-c", "kill -TERM $$" };
    int64_t p3 = rt_process_spawn_session("/bin/sh", sig_args, 2);
    CHECK(p3 > 1, "spawn for signal death");
    CHECK(rt_process_session_wait(p3, 5000) == -(128 + SIGTERM), "wait returns -(128+signo) on signal death");

    /* 5. exec failure is reported as -errno, not as a pid. */
    const char* none[] = { 0 };
    int64_t bad = rt_process_spawn_session("/nonexistent/definitely-not-here", none, 0);
    CHECK(bad == -ENOENT, "exec failure -> -ENOENT (%lld)", (long long)bad);

    /* 6. is_running does not reap: exit status survives the probe. */
    const char* quick[] = { "-c", "exit 3" };
    int64_t p4 = rt_process_spawn_session("/bin/sh", quick, 2);
    sleep_ms(200);
    CHECK(rt_process_session_is_running(p4) == 0, "exited child reported not running");
    CHECK(rt_process_session_wait(p4, 1000) == 3, "exit status still available after is_running");

    /* 7. Birth identity and parent-death signal arms. */
    CHECK(rt_proc_start_time((int64_t)getpid()) > 0, "start time of self is non-zero");
    CHECK(rt_proc_start_time(0) == 0, "start time of pid 0 is 0");
    pid_t probe = fork();
    if (probe == 0) {
        int64_t arm = rt_child_set_pdeathsig(SIGKILL);
#if defined(__linux__) || defined(__FreeBSD__)
        _exit(arm == 0 ? 0 : 1);
#else
        _exit(arm == RT_PTREE_UNSUPPORTED ? 0 : 1);
#endif
    }
    int status = 0;
    while (waitpid(probe, &status, 0) < 0 && errno == EINTR) {}
    CHECK(WIFEXITED(status) && WEXITSTATUS(status) == 0, "pdeathsig arm answers per host contract");

    fprintf(stderr, failures ? "process_tree_selfcheck: %d FAILURE(S)\n" : "process_tree_selfcheck: all checks passed\n", failures);
    return failures ? 1 : 0;
#endif
}

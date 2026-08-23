/* Self-check: rt_process_wait() must survive an interrupted wait and must
 * report a signal-terminated child distinguishably from a failed wait.
 *
 * Regression pinned (doc/08_tracking/bug/
 * native_build_wrapper_wait_eintr_misreported_as_abnormal_2026-08-23.md):
 * runtime_process.c's rt_process_wait() did `if (waitpid(...) < 0) return -1;`
 * with no EINTR retry, and collapsed every non-WIFEXITED status onto the same
 * -1. Both feed src/lib/nogc_sync_mut/io/process_ops.spl's
 * process_run_timeout_live(), whose -1 branch printed "native-build worker
 * wrapper exited abnormally (signal or wait failure, code -1)" and then killed
 * the worker's whole SESSION -- turning a signal delivered to the WRAPPER into
 * a lost ~70-minute stage1 attempt. Three independent lanes hit it in one
 * window.
 *
 * Proves two things about the real function in runtime_process.c:
 *   1. a wait interrupted by a signal whose handler is installed WITHOUT
 *      SA_RESTART is RETRIED, and still returns the child's true exit code
 *      (pre-fix: -1, "abnormal");
 *   2. a child killed by SIGKILL reports 128+SIGKILL (=137), not -1, so the
 *      caller can tell "died by signal" from "I could not determine status".
 *
 * Build + run (Linux/POSIX):
 *   clang -O1 -I src/runtime -o /tmp/pw_selfcheck \
 *       src/runtime/test/rt_process_wait_eintr_selfcheck.c src/runtime/runtime_process.c
 *   /tmp/pw_selfcheck
 *
 * Exit 0 = PASS, 1 = FAIL.
 */
#include <stdio.h>
#include <stdint.h>
#include <signal.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/wait.h>

extern int64_t rt_process_wait(int64_t pid, int64_t timeout_ms);

/* Link stubs: runtime_process.c references the rt_* value API, which this
 * wait path never touches. Never let a stub be silently reached. */
static void stub_unreachable(const char *who) {
    fprintf(stderr, "FAIL: unreachable runtime stub called: %s\n", who);
    _exit(1);
}
void *rt_array_new(void) { stub_unreachable("rt_array_new"); return 0; }
void *rt_array_get(void *a, int64_t i) { (void)a; (void)i; stub_unreachable("rt_array_get"); return 0; }
int64_t rt_array_len(void *a) { (void)a; stub_unreachable("rt_array_len"); return 0; }
void *rt_array_push(void *a, void *v) { (void)a; (void)v; stub_unreachable("rt_array_push"); return 0; }
void *rt_string_new(const char *s, int64_t n) { (void)s; (void)n; stub_unreachable("rt_string_new"); return 0; }
const char *rt_string_data(void *s) { (void)s; stub_unreachable("rt_string_data"); return 0; }
void *rt_value_int(int64_t v) { (void)v; stub_unreachable("rt_value_int"); return 0; }
void rt_fork_child_exit(void) { stub_unreachable("rt_fork_child_exit"); }
void rt_fork_child_setup(void) { stub_unreachable("rt_fork_child_setup"); }
int rt_fork_parent_signaled(void) { stub_unreachable("rt_fork_parent_signaled"); return 0; }
void *rt_fork_parent_stderr(void) { stub_unreachable("rt_fork_parent_stderr"); return 0; }
void *rt_fork_parent_stdout(void) { stub_unreachable("rt_fork_parent_stdout"); return 0; }
int rt_fork_parent_timed_out(void) { stub_unreachable("rt_fork_parent_timed_out"); return 0; }
int rt_fork_parent_wait(void) { stub_unreachable("rt_fork_parent_wait"); return 0; }
int rt_fork_parent_wait_bounded(void) { stub_unreachable("rt_fork_parent_wait_bounded"); return 0; }

static volatile sig_atomic_t g_ticks = 0;
static void on_alarm(int sig) { (void)sig; g_ticks++; }

static int failures = 0;
static void check(int ok, const char *what, int64_t got, int64_t want) {
    if (ok) { printf("  ok: %s (got %lld)\n", what, (long long)got); return; }
    printf("  FAIL: %s: got %lld, want %lld\n", what, (long long)got, (long long)want);
    failures++;
}

/* 1. Interrupted wait must be retried, not reported as failure. */
static void test_eintr_is_retried(void) {
    struct sigaction sa;
    sa.sa_handler = on_alarm;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0;                  /* deliberately NOT SA_RESTART */
    if (sigaction(SIGALRM, &sa, NULL) != 0) { printf("  FAIL: sigaction\n"); failures++; return; }

    pid_t pid = fork();
    if (pid == 0) { usleep(600 * 1000); _exit(7); }
    if (pid < 0) { printf("  FAIL: fork\n"); failures++; return; }

    struct itimerval it;
    it.it_value.tv_sec = 0;  it.it_value.tv_usec = 60 * 1000;
    it.it_interval.tv_sec = 0; it.it_interval.tv_usec = 60 * 1000;
    setitimer(ITIMER_REAL, &it, NULL);

    int64_t code = rt_process_wait((int64_t)pid, 0);   /* blocking wait */

    it.it_value.tv_usec = 0; it.it_interval.tv_usec = 0;
    setitimer(ITIMER_REAL, &it, NULL);

    check(g_ticks > 0, "the wait really was interrupted at least once", (int64_t)g_ticks, 1);
    check(code == 7, "interrupted blocking wait retries and returns the child's exit code", code, 7);
}

/* 2. A signal-terminated child must be distinguishable from a wait failure. */
static void test_signal_death_is_not_minus_one(void) {
    pid_t pid = fork();
    if (pid == 0) { usleep(2000 * 1000); _exit(0); }
    if (pid < 0) { printf("  FAIL: fork\n"); failures++; return; }
    usleep(50 * 1000);
    kill(pid, SIGKILL);
    int64_t code = rt_process_wait((int64_t)pid, 5000);
    check(code == 128 + SIGKILL, "SIGKILLed child reports 128+signo, not the -1 error sentinel", code, 128 + SIGKILL);
    check(code != -1, "signal death is never conflated with an indeterminate wait", code, -1);
}

int main(void) {
    printf("rt_process_wait EINTR/signal self-check\n");
    test_eintr_is_retried();
    test_signal_death_is_not_minus_one();
    if (failures) { printf("FAIL: %d check(s) failed\n", failures); return 1; }
    printf("PASS\n");
    return 0;
}

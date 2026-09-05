/* Self-check: the browser-renderer seccomp jail is an ALLOW-list.
 *
 * Proves, with a real fork()ed child that enters the real jail via
 * rt_browser_renderer_sandbox_enter():
 *   1. read()/write() on inherited pipe fds still work inside the jail;
 *   2. a syscall NOT on the allow-list (socket()) does not return EPERM --
 *      it KILLS the process via SECCOMP_RET_KILL_PROCESS (SIGSYS).
 *
 * Build + run (Linux only):
 *   clang -O1 -o /tmp/seccomp_allowlist_selfcheck \
 *       src/runtime/test/rt_browser_renderer_seccomp_allowlist_selfcheck.c
 *   /tmp/seccomp_allowlist_selfcheck
 *
 * Exit 0 = PASS, 1 = FAIL, 77 = SKIP (kernel lacks landlock/seccomp).
 */
#ifndef __linux__
#include <stdio.h>
int main(void) {
    puts("rt_browser_renderer_seccomp_allowlist_selfcheck: SKIP (non-Linux)");
    return 77;
}
#else

#include "../runtime_process.c"

#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <unistd.h>

int main(void) {
    int in_pipe[2];  /* parent -> child */
    int out_pipe[2]; /* child -> parent */
    if (pipe(in_pipe) != 0 || pipe(out_pipe) != 0) return 1;
    if (write(in_pipe[1], "P", 1) != 1) return 1;

    pid_t pid = fork();
    if (pid < 0) return 1;
    if (pid == 0) {
        /* Mimic the real worker fd layout (fds 0..3 only): the jail sets
           RLIMIT_NOFILE=4, and the in-jail landlock ruleset fd must still
           be allocatable below that limit during sandbox entry. */
        if (dup2(in_pipe[0], 0) != 0 || dup2(out_pipe[1], 1) != 1) _exit(122);
        close(in_pipe[0]);
        close(in_pipe[1]);
        close(out_pipe[0]);
        close(out_pipe[1]);
        /* Simulate the renderer-worker entry contract so the preinit
           hardening (no_new_privs + landlock + startup seccomp) runs. */
        char* fake_argv[] = { (char*)"simple-browser-renderer", NULL };
        char* fake_envp[] = { NULL };
        browser_renderer_preinit(1, fake_argv, fake_envp); /* _exit(126) on
            kernels without landlock/seccomp support */
        if (!rt_browser_renderer_sandbox_enter()) _exit(125);
        /* Allowed: read + write on inherited fds. */
        char b = 0;
        if (read(0, &b, 1) != 1 || b != 'P') _exit(124);
        if (write(1, "R", 1) != 1) _exit(124);
        /* Not on the allow-list: must KILL the process (SIGSYS), and
           must NOT return (an EPERM-style deny-list would return -1). */
        (void)socket(AF_INET, SOCK_STREAM, 0);
        /* Reached only if the filter failed open. */
        (void)write(1, "X", 1);
        _exit(123);
    }
    close(in_pipe[0]);
    close(in_pipe[1]);
    close(out_pipe[1]);

    char got = 0;
    ssize_t n = read(out_pipe[0], &got, 1);
    char extra = 0;
    ssize_t n2 = read(out_pipe[0], &extra, 1); /* EOF expected: child killed */
    int status = 0;
    if (waitpid(pid, &status, 0) < 0) return 1;

    if (WIFEXITED(status) && WEXITSTATUS(status) == 126) {
        puts("rt_browser_renderer_seccomp_allowlist_selfcheck: SKIP "
             "(preinit hardening unsupported on this kernel)");
        return 77;
    }
    if (WIFEXITED(status) && WEXITSTATUS(status) == 125) {
        puts("rt_browser_renderer_seccomp_allowlist_selfcheck: SKIP "
             "(rt_browser_renderer_sandbox_enter unavailable)");
        return 77;
    }
    int failures = 0;
    if (n != 1 || got != 'R') {
        puts("FAIL: allowed read/write on inherited fds did not work in jail");
        failures++;
    }
    if (n2 != 0) {
        puts("FAIL: child survived a non-allow-listed syscall (fail-open)");
        failures++;
    }
    if (!(WIFSIGNALED(status) && WTERMSIG(status) == SIGSYS)) {
        printf("FAIL: expected SIGSYS kill on socket(), got status 0x%x\n",
               status);
        failures++;
    }
    if (failures == 0) {
        puts("rt_browser_renderer_seccomp_allowlist_selfcheck: PASS");
        return 0;
    }
    return 1;
}
#endif

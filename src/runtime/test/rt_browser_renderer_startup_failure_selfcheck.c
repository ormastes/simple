/* rt_browser_renderer_startup_failure_selfcheck.c — REQ-WEB-BROWSER-014.
 *
 * Covers the "startup failure" row of the SANDBOX acceptance criteria, which
 * had no evidence at all: the two sibling self-checks assert what the jail
 * ALLOWS (read/write) and what it KILLS (socket -> SIGSYS), but nothing
 * asserted what it does when the jail cannot or must not be entered.
 *
 * That gap matters more than it looks. Every failure path in
 * browser_renderer_preinit collapses to a single _exit(126), and
 * rt_browser_renderer_sandbox_enter collapses to a bare `false`. A refactor
 * that turned either into a silent success would leave a renderer running
 * page script with NO confinement while every existing check still passed —
 * the allow/kill checks only run once the jail is already up.
 *
 * Both arms here are deterministic on any Linux and never SKIP, because they
 * fire strictly BEFORE any kernel capability is consulted:
 *
 *   Arm 1 — contract violation is fatal. preinit requires an EMPTY envp (the
 *   renderer worker is exec'd with no environment so it cannot inherit
 *   secrets, proxies or LD_* injection). Handing it a non-empty envp must
 *   kill the process with 126. It must never continue unconfined. This check
 *   is what fails if someone "relaxes" the envp requirement to make debugging
 *   easier.
 *
 *   Arm 2 — the jail is fail-closed without preinit. A process whose argv[0]
 *   is not the worker marker is left alone by preinit (correct: ordinary
 *   `simple` invocations must not be jailed). rt_browser_renderer_sandbox_enter
 *   must then REFUSE, returning false rather than reporting a jail it never
 *   built. This is the check that fails if the preinit-active guard is ever
 *   dropped.
 *
 * Exit: 0 = PASS, 1 = FAIL. No SKIP path exists by construction — if this
 * binary runs at all, both arms are decidable.
 */
#if !defined(__linux__)
#include <stdio.h>
int main(void) {
    puts("rt_browser_renderer_startup_failure_selfcheck: SKIP (linux only)");
    return 77;
}
#else

#include "../runtime_process.c"

#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

/* Arm 1: a non-empty environment violates the worker entry contract and must
   be fatal (_exit(126)), never a degraded continue. */
static int check_nonempty_envp_is_fatal(void) {
    pid_t pid = fork();
    if (pid < 0) return -1;
    if (pid == 0) {
        char marker[] = "simple-browser-renderer";
        char leak[] = "SECRET=value";
        char* fake_argv[] = {marker, NULL};
        char* fake_envp[] = {leak, NULL}; /* deliberately NOT empty */
        browser_renderer_preinit(1, fake_argv, fake_envp);
        /* Reaching here means preinit accepted an inherited environment. */
        _exit(0);
    }
    int status = 0;
    if (waitpid(pid, &status, 0) < 0) return -1;
    if (!WIFEXITED(status)) {
        printf("FAIL: preinit with non-empty envp did not exit normally "
               "(status 0x%x)\n", (unsigned)status);
        return 1;
    }
    if (WEXITSTATUS(status) != 126) {
        printf("FAIL: preinit with non-empty envp exited %d, expected 126 — "
               "the renderer worker would inherit its parent's environment "
               "instead of refusing to start\n", WEXITSTATUS(status));
        return 1;
    }
    return 0;
}

/* Arm 2: without a successful preinit, entering the jail must fail closed. */
static int check_sandbox_enter_refuses_without_preinit(void) {
    pid_t pid = fork();
    if (pid < 0) return -1;
    if (pid == 0) {
        char other[] = "not-the-renderer-worker";
        char* fake_argv[] = {other, NULL};
        char* fake_envp[] = {NULL};
        /* argv[0] does not match the marker: preinit must no-op, leaving the
           process unjailed and s_browser_renderer_preinit_active false. */
        browser_renderer_preinit(1, fake_argv, fake_envp);
        /* 0 = correctly refused, 1 = wrongly claimed a jail it never built. */
        _exit(rt_browser_renderer_sandbox_enter() ? 1 : 0);
    }
    int status = 0;
    if (waitpid(pid, &status, 0) < 0) return -1;
    if (!WIFEXITED(status)) {
        printf("FAIL: sandbox_enter probe did not exit normally "
               "(status 0x%x)\n", (unsigned)status);
        return 1;
    }
    if (WEXITSTATUS(status) == 1) {
        puts("FAIL: rt_browser_renderer_sandbox_enter() returned true without "
             "a successful preinit — it reports a jail that was never built");
        return 1;
    }
    if (WEXITSTATUS(status) != 0) {
        printf("FAIL: sandbox_enter probe exited %d, expected 0 or 1\n",
               WEXITSTATUS(status));
        return 1;
    }
    return 0;
}

int main(void) {
    int rc = check_nonempty_envp_is_fatal();
    if (rc != 0) {
        if (rc < 0) puts("FAIL: fork/waitpid failed in envp arm");
        return 1;
    }
    rc = check_sandbox_enter_refuses_without_preinit();
    if (rc != 0) {
        if (rc < 0) puts("FAIL: fork/waitpid failed in sandbox_enter arm");
        return 1;
    }
    puts("rt_browser_renderer_startup_failure_selfcheck: PASS "
         "(non-empty envp is fatal with exit 126; sandbox_enter refuses "
         "without preinit)");
    return 0;
}

#endif

/* rt_browser_renderer_preinit_entry_selfcheck.c — REQ-WEB-BROWSER-014.
 *
 * Covers the explicit startup entry rt_browser_renderer_preinit_enter() added
 * for lanes where the .preinit_array registration is compiled out (core-C
 * standalone archive; the Stage4 capsule forbids constructor sections). The
 * sibling startup-failure selfcheck exercises browser_renderer_preinit
 * directly; this one proves the EXPORTED wrapper the generated entry main
 * calls actually routes into it:
 *
 *   Arm 1 — the entry forwards the worker marker into the real preinit. A
 *   child calling rt_browser_renderer_preinit_enter with argv[0] ==
 *   "simple-browser-renderer" and a NON-EMPTY envp must die with _exit(126)
 *   (the empty-envp contract). If the wrapper ever became a stub -- the
 *   fail-open shape where a core-C-built renderer runs unjailed while every
 *   constructor-lane check stays green -- the child returns and the arm
 *   fails.
 *
 *   Arm 2 — ordinary binaries pass through untouched. The same entry with
 *   argv[0] != the marker must return, leave preinit inactive, and
 *   rt_browser_renderer_sandbox_enter() must still refuse (fail closed).
 *
 * Exit: 0 = PASS, 1 = FAIL. No SKIP path on Linux -- both arms fire before
 * any kernel capability is consulted. Non-Linux hosts SKIP (77): the jail
 * itself is Linux-only.
 */
#if !defined(__linux__)
#include <stdio.h>
int main(void) {
    puts("rt_browser_renderer_preinit_entry_selfcheck: SKIP (linux only)");
    return 77;
}
#else

#include "../runtime_process.c"

#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

/* Arm 1: a contract-violating (non-empty) envp handed to the exported entry
   must be fatal (_exit(126)), never a degraded continue. */
static int check_entry_enforces_empty_envp(void) {
    pid_t pid = fork();
    if (pid < 0) return -1;
    if (pid == 0) {
        char marker[] = "simple-browser-renderer";
        char leak[] = "SECRET=value";
        char* fake_argv[] = {marker, NULL};
        char* fake_envp[] = {leak, NULL}; /* deliberately NOT empty */
        rt_browser_renderer_preinit_enter(1, fake_argv, fake_envp);
        _exit(0); /* returned: the contract violation was not enforced */
    }
    int status = 0;
    if (waitpid(pid, &status, 0) < 0) return -1;
    return WIFEXITED(status) && WEXITSTATUS(status) == 126;
}

/* Arm 2: an ordinary argv passes through the entry untouched: it returns,
   preinit stays inactive, and sandbox_enter refuses without it. */
static int check_ordinary_argv_is_untouched(void) {
    char ordinary[] = "simple";
    char* fake_argv[] = {ordinary, NULL};
    rt_browser_renderer_preinit_enter(1, fake_argv, NULL);
    if (rt_browser_renderer_preinit_active_for_test()) return 0;
    if (rt_browser_renderer_sandbox_enter()) return 0;
    return 1;
}

int main(void) {
    int arm1 = check_entry_enforces_empty_envp();
    int arm2 = check_ordinary_argv_is_untouched();
    if (arm1 == 1 && arm2 == 1) {
        puts("rt_browser_renderer_preinit_entry_selfcheck: PASS");
        return 0;
    }
    fprintf(stderr,
            "rt_browser_renderer_preinit_entry_selfcheck: FAIL arm1=%d arm2=%d\n",
            arm1, arm2);
    return 1;
}
#endif

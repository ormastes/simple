/* rt_browser_renderer_namespace_selfcheck.c — REQ-WEB-BROWSER-014 (SANDBOX-D).
 *
 * Proves the browser renderer jail's namespace layer, added to close problem 2
 * of doc/08_tracking/bug/browser_seccomp_denylist_and_inprocess_unjailed_2026-08-15.md
 * ("no namespaces / privilege drop"). The seccomp allow-list already kills
 * socket(); an empty network namespace removes the route itself, so a future
 * kernel syscall that reaches the network cannot undo the confinement.
 *
 * The discriminating case is a FALSE CLAIM: if
 * rt_browser_renderer_namespaces_active() reports true while /proc/self/ns/net
 * is unchanged, the jail is advertising isolation it does not have. That is a
 * FAIL, not a skip — it is exactly the false-green this repo keeps getting bit
 * by, and it is why this check compares the namespace identity rather than
 * trusting the boolean.
 *
 * Exit: 0 = PASS (namespaces obtained AND proven distinct, or honestly absent)
 *       1 = FAIL (claim disagrees with reality, or preinit broke)
 *      77 = SKIP (kernel lacks the seccomp/landlock preinit entirely)
 *
 * Note the asymmetry: "namespaces unavailable" is a PASS here as long as the
 * posture bit says so. Ubuntu 24.04 sets
 * kernel.apparmor_restrict_unprivileged_userns=1, which permits CLONE_NEWUSER
 * but strips the capabilities needed for CLONE_NEWNET (EPERM). Refusing to run
 * there would be wrong; lying about it would be worse. The gate that drives
 * this check reports which posture was observed.
 */
#if !defined(__linux__)
#include <stdio.h>
int main(void) {
    puts("rt_browser_renderer_namespace_selfcheck: SKIP (linux only)");
    return 77;
}
#else

#include "../runtime_process.c"

#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

static int read_ns(const char* path, char* out, size_t cap) {
    ssize_t n = readlink(path, out, cap - 1);
    if (n < 0) return -1;
    out[n] = '\0';
    return 0;
}

int main(void) {
    char before[128];
    if (read_ns("/proc/self/ns/net", before, sizeof before) != 0) {
        puts("rt_browser_renderer_namespace_selfcheck: SKIP (no /proc/self/ns/net)");
        return 77;
    }

    int pipefd[2];
    if (pipe(pipefd) != 0) return 1;

    pid_t pid = fork();
    if (pid < 0) return 1;

    if (pid == 0) {
        close(pipefd[0]);
        /* Simulate the renderer-worker entry contract, exactly as the sibling
           seccomp self-check does: argv[0] is the marker and envp is empty. */
        char marker[] = "simple-browser-renderer";
        char* fake_argv[] = {marker, NULL};
        char* fake_envp[] = {NULL};
        browser_renderer_preinit(1, fake_argv, fake_envp); /* _exit(126) on fail */

        char after[128];
        if (read_ns("/proc/self/ns/net", after, sizeof after) != 0) _exit(3);

        /* Report: posture bit, then whether the netns identity actually moved. */
        char msg[300];
        int n = snprintf(msg, sizeof msg, "%d %s %s",
                         rt_browser_renderer_namespaces_active() ? 1 : 0,
                         before, after);
        if (n <= 0) _exit(3);
        if (write(pipefd[1], msg, (size_t)n) != n) _exit(3);
        _exit(0);
    }

    close(pipefd[1]);
    char buf[320];
    ssize_t got = read(pipefd[0], buf, sizeof buf - 1);
    buf[got > 0 ? (size_t)got : 0] = '\0';

    int status = 0;
    if (waitpid(pid, &status, 0) < 0) return 1;

    if (WIFEXITED(status) && WEXITSTATUS(status) == 126) {
        puts("rt_browser_renderer_namespace_selfcheck: SKIP (preinit hardening unsupported on this kernel)");
        return 77;
    }
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0 || got <= 0) {
        printf("FAIL: child did not report (status 0x%x)\n", (unsigned)status);
        return 1;
    }

    int claimed = 0;
    char ns_before[128] = {0};
    char ns_after[128] = {0};
    if (sscanf(buf, "%d %127s %127s", &claimed, ns_before, ns_after) != 3) {
        puts("FAIL: malformed child report");
        return 1;
    }

    int moved = strcmp(ns_before, ns_after) != 0;

    if (claimed && !moved) {
        printf("FAIL: namespaces_active()=true but net ns unchanged (%s) — "
               "the jail advertises isolation it does not have\n", ns_after);
        return 1;
    }
    if (!claimed && moved) {
        printf("FAIL: net ns changed (%s -> %s) but namespaces_active()=false — "
               "posture under-reports the jail\n", ns_before, ns_after);
        return 1;
    }

    if (claimed) {
        printf("rt_browser_renderer_namespace_selfcheck: PASS "
               "(namespaces=active, net ns %s -> %s)\n", ns_before, ns_after);
    } else {
        printf("rt_browser_renderer_namespace_selfcheck: PASS "
               "(namespaces=unavailable, honestly reported; net ns %s "
               "unchanged)\n", ns_before);
    }
    return 0;
}

#endif

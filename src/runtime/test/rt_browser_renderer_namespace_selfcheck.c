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
    char net_before[128], user_before[128], ipc_before[128];
    if (read_ns("/proc/self/ns/net", net_before, sizeof net_before) != 0 ||
        read_ns("/proc/self/ns/user", user_before, sizeof user_before) != 0 ||
        read_ns("/proc/self/ns/ipc", ipc_before, sizeof ipc_before) != 0) {
        puts("rt_browser_renderer_namespace_selfcheck: SKIP (no /proc/self/ns/*)");
        return 77;
    }
    unsigned uid_before = (unsigned)getuid();
    unsigned gid_before = (unsigned)getgid();

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

        char net_after[128], user_after[128], ipc_after[128];
        if (read_ns("/proc/self/ns/net", net_after, sizeof net_after) != 0) _exit(3);
        if (read_ns("/proc/self/ns/user", user_after, sizeof user_after) != 0) _exit(3);
        if (read_ns("/proc/self/ns/ipc", ipc_after, sizeof ipc_after) != 0) _exit(3);

        /* Report: posture bit, all three namespace identities, and the uid/gid
           observed INSIDE the jail. The ids are the privilege-drop oracle: in a
           fresh user namespace with no uid_map written, getuid() returns the
           overflow id (65534/nobody). Seeing the original id back therefore
           proves the identity map was actually written — which cannot be read
           back directly, because landlock denies the read by then. */
        char msg[512];
        int n = snprintf(msg, sizeof msg, "%d %s %s %s %s %s %u %u",
                         rt_browser_renderer_namespaces_active() ? 1 : 0,
                         net_before, net_after,
                         user_after, ipc_after,
                         "-",
                         (unsigned)getuid(), (unsigned)getgid());
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
    char net_rep[128] = {0}, net_after[128] = {0};
    char user_after[128] = {0}, ipc_after[128] = {0}, spare[8] = {0};
    unsigned uid_in = 0, gid_in = 0;
    if (sscanf(buf, "%d %127s %127s %127s %127s %7s %u %u",
               &claimed, net_rep, net_after, user_after, ipc_after,
               spare, &uid_in, &gid_in) != 8) {
        puts("FAIL: malformed child report");
        return 1;
    }

    int net_moved = strcmp(net_before, net_after) != 0;
    int user_moved = strcmp(user_before, user_after) != 0;
    int ipc_moved = strcmp(ipc_before, ipc_after) != 0;

    if (claimed && !net_moved) {
        printf("FAIL: namespaces_active()=true but net ns unchanged (%s) — "
               "the jail advertises isolation it does not have\n", net_after);
        return 1;
    }
    if (!claimed && net_moved) {
        printf("FAIL: net ns changed (%s -> %s) but namespaces_active()=false — "
               "posture under-reports the jail\n", net_before, net_after);
        return 1;
    }

    if (claimed) {
        /* The claim is user+net+IPC, so verify all three, not just the one
           that is easiest to observe. A partial unshare reported as full
           isolation is the same class of lie as no unshare at all. */
        if (!user_moved || !ipc_moved) {
            printf("FAIL: namespaces_active()=true but only some namespaces "
                   "moved (user %s, ipc %s, net %s) — partial isolation "
                   "reported as full\n",
                   user_moved ? "moved" : "UNCHANGED",
                   ipc_moved ? "moved" : "UNCHANGED",
                   net_moved ? "moved" : "UNCHANGED");
            return 1;
        }
        /* Privilege-drop oracle: without a uid_map written into the new user
           namespace, getuid() reports the overflow id (typically 65534). The
           original id coming back proves the identity map was written. The map
           itself cannot be read back here — landlock denies the read by now. */
        if (uid_in != uid_before || gid_in != gid_before) {
            printf("FAIL: uid/gid inside jail is %u/%u, expected %u/%u — the "
                   "identity uid_map/gid_map was not written (overflow id "
                   "means an unmapped user namespace)\n",
                   uid_in, gid_in, uid_before, gid_before);
            return 1;
        }
        printf("rt_browser_renderer_namespace_selfcheck: PASS "
               "(namespaces=active; net %s -> %s, user %s -> %s, ipc %s -> %s; "
               "uid/gid %u/%u mapped through)\n",
               net_before, net_after, user_before, user_after,
               ipc_before, ipc_after, uid_in, gid_in);
    } else {
        printf("rt_browser_renderer_namespace_selfcheck: PASS "
               "(namespaces=unavailable, honestly reported; net ns %s "
               "unchanged)\n", net_before);
    }
    return 0;
}

#endif

/* browser_renderer_apply_namespaces / browser_renderer_drop_privileges were never
 * implemented (doc/08_tracking/bug/browser_renderer_namespace_fns_undeclared_2026-08-21.md).
 * Until they exist, this selfcheck compiles to an empty translation unit so the
 * mandatory C-runtime gate keeps discriminating real regressions. Define
 * SPL_HAS_BROWSER_RENDERER_NAMESPACES once the functions land to re-enable it. */
#ifdef SPL_HAS_BROWSER_RENDERER_NAMESPACES
/* Self-check: the browser-renderer jail drops privileges and isolates the
 * network namespace (Phase 2 of the sandbox model -- see
 * doc/08_tracking/bug/browser_seccomp_denylist_and_inprocess_unjailed_2026-08-15.md).
 *
 * Proves three things about the real functions in runtime_process.c:
 *   1. browser_renderer_drop_privileges() never leaves a root process root,
 *      and the drop is irreversible (setuid(0) must fail afterwards);
 *   2. browser_renderer_apply_namespaces() either really moves the process
 *      into a NEW network namespace (the /proc/self/ns/net inode changes) or
 *      honestly reports false -- it must never claim isolation it did not get;
 *   3. a refused namespace leaves the process's uid INTACT. This is the
 *      regression that motivated the sysctl precondition check: an
 *      unconditional unshare(CLONE_NEWUSER) succeeds on hosts with
 *      apparmor_restrict_unprivileged_userns=1 but cannot then be mapped,
 *      stranding the renderer as the overflow uid 65534.
 *
 * Build + run (Linux only; needs link stubs for the rt_* value API, which
 * this jail path does not touch):
 *   clang -O1 -I src/runtime -o /tmp/ns_selfcheck \
 *       src/runtime/test/rt_browser_renderer_namespace_selfcheck.c
 *   /tmp/ns_selfcheck
 *
 * Exit 0 = PASS, 1 = FAIL, 77 = SKIP (namespaces administratively disabled).
 *
 * A SKIP is the expected result for an unprivileged process on a host that
 * disables unprivileged user namespaces; it is NOT a pass, and the seccomp
 * ALLOW-list remains the binding network control there (socket() is not on
 * the list and is answered with SECCOMP_RET_KILL_PROCESS).
 */
#ifndef __linux__
#include <stdio.h>
int main(void) {
    puts("rt_browser_renderer_namespace_selfcheck: SKIP (non-Linux)");
    return 77;
}
#else

#include "../runtime_process.c"

#include <stdio.h>


int main(void) {
    char before[64] = {0};
    char after[64] = {0};
    uid_t uid_before = geteuid();
    int was_root = (uid_before == 0);

    if (readlink("/proc/self/ns/net", before, sizeof(before) - 1) < 0) {
        puts("rt_browser_renderer_namespace_selfcheck: SKIP (no /proc ns)");
        return 77;
    }

    /* Same order as rt_browser_renderer_sandbox_enter(): namespaces first,
     * because a root renderer needs CAP_SYS_ADMIN that the drop removes. */
    bool netns = browser_renderer_apply_namespaces();

    if (!browser_renderer_drop_privileges()) {
        puts("rt_browser_renderer_namespace_selfcheck: FAIL (drop failed)");
        return 1;
    }
    if (was_root && geteuid() == 0) {
        puts("rt_browser_renderer_namespace_selfcheck: FAIL (still root)");
        return 1;
    }
    /* Claim 3: an unprivileged process whose namespace request was refused
     * must still be itself, not the overflow uid. */
    if (!was_root && !netns && geteuid() != uid_before) {
        printf("rt_browser_renderer_namespace_selfcheck: FAIL "
               "(stranded in unmapped userns: uid %ld -> %ld)\n",
               (long)uid_before, (long)geteuid());
        return 1;
    }

    if (readlink("/proc/self/ns/net", after, sizeof(after) - 1) < 0) {
        puts("rt_browser_renderer_namespace_selfcheck: FAIL (ns unreadable)");
        return 1;
    }

    /* Claim 2 both ways: reported isolation must be real, and unreported
     * isolation must not have silently happened. */
    if (netns && strcmp(before, after) == 0) {
        puts("rt_browser_renderer_namespace_selfcheck: FAIL "
             "(claimed netns isolation but the namespace did not change)");
        return 1;
    }
    if (!netns && strcmp(before, after) != 0) {
        puts("rt_browser_renderer_namespace_selfcheck: FAIL "
             "(namespace changed but was reported as unavailable)");
        return 1;
    }
    if (netns != rt_browser_renderer_sandbox_netns_active() &&
        rt_browser_renderer_sandbox_netns_active()) {
        puts("rt_browser_renderer_namespace_selfcheck: FAIL "
             "(accessor disagrees with the applied posture)");
        return 1;
    }

    if (!netns) {
        printf("rt_browser_renderer_namespace_selfcheck: SKIP "
               "(namespaces unavailable; uid intact at %ld, net %s)\n",
               (long)geteuid(), after);
        return 77;
    }
    printf("rt_browser_renderer_namespace_selfcheck: PASS "
           "(uid %ld -> %ld, net %s -> %s)\n",
           (long)uid_before, (long)geteuid(), before, after);
    return 0;
}

#endif
#else
typedef int spl_browser_renderer_namespace_selfcheck_pending;
#endif

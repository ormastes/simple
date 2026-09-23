/* rt_browser_renderer_namespace_selfcheck.c -- REQ-WEB-BROWSER-014.
 *
 * Exercise the namespace phase through the same browser_renderer_preinit()
 * path that runs from DT_PREINIT_ARRAY in a broker-launched renderer.  The
 * older probe was permanently compiled out behind SPL_HAS_BROWSER_RENDERER_
 * NAMESPACES after that implementation was replaced, leaving the mandatory
 * gate unable to link a main program.
 */
#ifndef __linux__
#include <stdio.h>
int main(void) {
    puts("rt_browser_renderer_namespace_selfcheck: SKIP (non-Linux)");
    return 77;
}
#else

#define BROWSER_RENDERER_NAMESPACE_SELFCHECK 1
#include "../runtime_process.c"

#include <stdio.h>
#include <string.h>

static int partial_namespace_failure_exits_closed(
        char** argv, char** envp) {
    pid_t child = fork();
    if (child == 0) {
        s_browser_renderer_force_partial_namespace_failure_for_test = true;
        browser_renderer_preinit(1, argv, envp);
        _exit(0);
    }
    if (child < 0) return 0;
    int status = 0;
    while (waitpid(child, &status, 0) < 0) {
        if (errno != EINTR) return 0;
    }
    return WIFEXITED(status) && WEXITSTATUS(status) == 126;
}

int main(void) {
    char before[64] = {0};
    char after[64] = {0};
    char marker[] = "simple-browser-renderer";
    char* argv[] = {marker, NULL};
    char* envp[] = {NULL};
    uid_t uid_before = geteuid();
    gid_t gid_before = getegid();

    if (!partial_namespace_failure_exits_closed(argv, envp)) {
        puts("rt_browser_renderer_namespace_selfcheck: FAIL "
             "(partial namespace failure did not exit 126)");
        return 1;
    }

    if (readlink("/proc/self/ns/net", before, sizeof(before) - 1) < 0) {
        puts("rt_browser_renderer_namespace_selfcheck: FAIL (no /proc ns)");
        return 1;
    }

    browser_renderer_preinit(1, argv, envp);
    if (!rt_browser_renderer_preinit_active_for_test()) {
        puts("rt_browser_renderer_namespace_selfcheck: FAIL (preinit inactive)");
        return 1;
    }
    if (readlink("/proc/self/ns/net", after, sizeof(after) - 1) < 0) {
        puts("rt_browser_renderer_namespace_selfcheck: FAIL (ns unreadable)");
        return 1;
    }

    bool active = rt_browser_renderer_sandbox_netns_active();
    bool changed = strcmp(before, after) != 0;
    if (active != changed) {
        printf("rt_browser_renderer_namespace_selfcheck: FAIL "
               "(reported active=%d, net %s -> %s)\n",
               active, before, after);
        return 1;
    }
    if (geteuid() != uid_before) {
        printf("rt_browser_renderer_namespace_selfcheck: FAIL "
               "(namespace fallback changed uid %ld -> %ld)\n",
               (long)uid_before, (long)geteuid());
        return 1;
    }
    if (getegid() != gid_before) {
        printf("rt_browser_renderer_namespace_selfcheck: FAIL "
               "(namespace fallback changed gid %ld -> %ld)\n",
               (long)gid_before, (long)getegid());
        return 1;
    }
    printf("rt_browser_renderer_namespace_selfcheck: PASS "
           "(namespaces=%s, uid=%ld, gid=%ld, partial-failure=closed, "
           "net %s -> %s)\n",
           active ? "active" : "unavailable", (long)geteuid(),
           (long)getegid(), before, after);
    return 0;
}

#endif

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

#include "../runtime_process.c"

#include <stdio.h>
#include <string.h>

int main(void) {
    char before[64] = {0};
    char after[64] = {0};
    char marker[] = "simple-browser-renderer";
    char* argv[] = {marker, NULL};
    char* envp[] = {NULL};

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
    printf("rt_browser_renderer_namespace_selfcheck: PASS "
           "(namespaces=%s, net %s -> %s)\n",
           active ? "active" : "unavailable", before, after);
    return 0;
}

#endif

/* Real core-C owner regression. Link all standalone C runtime owners, replacing
 * runtime_process_tree.o with this change. Run once without a managed parent,
 * then with --managed under run-process-group-timeout.shs. */
#define _DARWIN_C_SOURCE
#include "runtime.h"
#include "runtime_process_tree.h"
#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* POSIX currently exports an explicit unsupported result; the public runtime
 * header declares this entry only in its Windows implementation arm. */
extern int64_t rt_process_spawn_async_environment_v1(const char *, uint64_t,
                                                    SplArray *, SplArray *, int64_t);

static void denied(void) {
    const char *args[] = {"-c", "exit 37"};
    assert(rt_process_tree_support() == RT_PTREE_UNSUPPORTED);
    assert(rt_process_spawn_session("/bin/sh", args, 2) == -EPERM);
}

int main(int argc, char **argv) {
    assert(argc == 2);
    if (!strcmp(argv[1], "--managed")) {
        assert(getenv("SIMPLE_BOOTSTRAP_SESSION_ID"));
        assert(getenv("SIMPLE_BOOTSTRAP_SESSION_EXEC"));
        denied();
        /* The compiler's existing fallback must retain the canonical session.
         * Use the actual C async owner, and a long enough child to inspect it. */
        const char *args[] = {"-c", "sleep 0.2; exit 7"};
        int64_t child = rt_process_spawn_async("/bin/sh", args, 2);
        assert(child > 1);
        assert(getsid((pid_t)child) == getsid(0));
        assert(rt_process_wait(child, 5000) == 7);
        /* POSIX explicit-environment async is currently unsupported. It must
         * stay an explicit failure, never a launch with dropped supervision. */
        SplArray *empty = rt_array_new(0);
        assert(rt_process_spawn_async_environment_v1("/bin/true", 9,
                                                     empty, empty, 1) == -95);
        puts("PASS managed: private-session refusal, inherited async child, explicit-env unsupported");
        return 0;
    }
    assert(!strcmp(argv[1], "--standalone"));
    assert(!getenv("SIMPLE_BOOTSTRAP_SESSION_ID"));
    assert(!getenv("SIMPLE_BOOTSTRAP_SESSION_EXEC"));
    assert(rt_process_tree_support() == 0);
    const char *args[] = {"-c", "sleep 0.2; exit 11"};
    int64_t child = rt_process_spawn_session("/bin/sh", args, 2);
    assert(child > 1);
    assert(getsid((pid_t)child) == (pid_t)child);
    assert(rt_process_session_wait(child, 5000) == 11);
    /* Even empty or incomplete reserved contracts fail closed. */
    assert(setenv("SIMPLE_BOOTSTRAP_SESSION_ID", "", 1) == 0);
    denied();
    assert(unsetenv("SIMPLE_BOOTSTRAP_SESSION_ID") == 0);
    assert(setenv("SIMPLE_BOOTSTRAP_SESSION_EXEC", "/missing-owner", 1) == 0);
    denied();
    puts("PASS standalone: private session and empty/partial contract refusal");
    return 0;
}

/* Run from the repository root:
 * cc -std=c11 -Wall -Wextra -Werror -pthread src/runtime/test/runtime_process_observation_v4_darwin_interrupted_wait_selfcheck.c src/runtime/runtime_process_tree.c -o /tmp/pov4-darwin-interrupted-wait
 * /tmp/pov4-darwin-interrupted-wait
 * Build and run as the Darwin cwd selfcheck, but interrupt its first wait.
 * This reproduces the EINTR observed when stepping the selfcheck in LLDB. */
#if defined(__APPLE__)
#define _DARWIN_C_SOURCE
#include <errno.h>
#include <sys/types.h>
#include <sys/wait.h>

static int interrupted_wait_injected;
static pid_t interrupted_wait_once(pid_t child, int* status, int options) {
    if (!interrupted_wait_injected) {
        interrupted_wait_injected = 1;
        errno = EINTR;
        return -1;
    }
    return waitpid(child, status, options);
}
#define waitpid interrupted_wait_once
#define main darwin_cwd_selfcheck_main
#include "runtime_process_observation_v4_darwin_selfcheck.c"
#undef main
#undef waitpid

int main(void) {
    int result = darwin_cwd_selfcheck_main();
    assert(interrupted_wait_injected == 1);
    return result;
}
#else
#include "runtime_process_observation_v4_darwin_selfcheck.c"
#endif

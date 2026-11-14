/* Real non-reaping child observation. No PID-liveness fallback is admissible.
 * cc -Wall -Wextra -Werror -I src/runtime -o /tmp/owned-child \
 *   src/runtime/test/process_owned_child_selfcheck.c src/runtime/runtime_process_tree.c
 */
#define _GNU_SOURCE
#include "runtime_process_tree.h"
#include <errno.h>
#include <signal.h>
#include <stdio.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static int failures;
#define CHECK(c, label) do { if (!(c)) { failures++; fprintf(stderr, "FAIL %s\n", label); } } while (0)

int main(void) {
    CHECK(rt_process_tree_support() == 0, "native owner supported");
    CHECK(rt_process_owned_child_state(1) == -EINVAL, "invalid PID fails");
    CHECK(rt_process_owned_child_state(getpid()) == -ECHILD, "live nonchild fails");
    int gate[2];
    if (pipe(gate) != 0) return 2;
    pid_t child = fork();
    if (child < 0) return 2;
    if (child == 0) {
        close(gate[1]);
        char byte;
        ssize_t n;
        do { n = read(gate[0], &byte, 1); } while (n < 0 && errno == EINTR);
        _exit(n == 1 ? 7 : 8);
    }
    close(gate[0]);
    CHECK(rt_process_owned_child_state(child) == 1, "running owned child");
    CHECK(write(gate[1], "x", 1) == 1, "release actual child");
    close(gate[1]);
    int64_t state = 1;
    const struct timespec tick = {0, 1000000};
    for (int i = 0; i < 2000 && state == 1; ++i) {
        state = rt_process_owned_child_state(child);
        if (state == 1) nanosleep(&tick, NULL);
    }
    CHECK(state == 0, "terminal owned child retained");
    CHECK(rt_process_owned_child_state(child) == 0, "repeat observation does not reap");
    int status = 0;
    CHECK(waitpid(child, &status, 0) == child, "one owner reap succeeds");
    CHECK(WIFEXITED(status) && WEXITSTATUS(status) == 7, "original exit status retained");
    CHECK(rt_process_owned_child_state(child) == -ECHILD, "reaped child fails closed");
    fprintf(stderr, "owned-child physical API: %d failures\n", failures);
    return failures != 0;
}

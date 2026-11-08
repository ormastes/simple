/* Authored NOT_RUN. Link against the ACTUAL legacy runtime.c/platform provider
 * profile. Exclude runtime_native.c, runtime_host_file_exports.c and Rust's
 * strong rt_file_lock twin; otherwise a PASS would not test unix_common.h.
 * This test uses the exact public three-word ABI from runtime.h. */
#if defined(_WIN32)
#error "requires a POSIX legacy runtime.c provider test slot"
#endif
#define _POSIX_C_SOURCE 200809L
#include "../runtime.h"
#include <assert.h>
#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

static void blocking_regression(int signal_number) {
    (void)signal_number;
    _exit(124);
}
static void contended_single_attempt(const char *path, int64_t timeout) {
    int report[2];
    assert(pipe(report) == 0);
    pid_t child = fork();
    assert(child >= 0);
    if (child == 0) {
        close(report[0]);
        signal(SIGALRM, blocking_regression);
        alarm(3);
        /* Parent retains its real lock until this report and child exit.
         * Do not unlock the inherited descriptor: it shares the parent's OFD. */
        int64_t result = rt_file_lock((const uint8_t *)path, strlen(path), timeout);
        if (result >= 0) {
            rt_file_unlock(result);
            _exit(2);
        }
        assert(write(report[1], &result, sizeof(result)) == (ssize_t)sizeof(result));
        _exit(result == -1 ? 0 : 3);
    }
    close(report[1]);
    int64_t result = 0;
    ssize_t count;
    do { count = read(report[0], &result, sizeof(result)); } while (count < 0 && errno == EINTR);
    close(report[0]);
    int status;
    assert(waitpid(child, &status, 0) == child);
    assert(WIFEXITED(status) && WEXITSTATUS(status) == 0);
    assert(count == (ssize_t)sizeof(result) && result == -1);
}
int main(void) {
    char root[] = "/tmp/simple-legacy-trylock-XXXXXX";
    assert(mkdtemp(root));
    char path[256];
    assert(snprintf(path, sizeof(path), "%s/parent.lock", root) > 0);
    int64_t owner = rt_file_lock((const uint8_t *)path, strlen(path), 0);
    assert(owner >= 0); /* actual successful uncontended acquisition */
    contended_single_attempt(path, 0);
    contended_single_attempt(path, -1);
    assert(rt_file_unlock(owner));
    int64_t reopened = rt_file_lock((const uint8_t *)path, strlen(path), 0);
    assert(reopened >= 0);
    assert(rt_file_unlock(reopened));
    assert(unlink(path) == 0 && rmdir(root) == 0);
    return 0;
}

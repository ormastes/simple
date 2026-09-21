/* Bootstrap syscall boundary: keep nested worker groups in the guard's session.
 * Build once before guarded execution; never compile in a worker launch path. */
#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static int reject(const char *reason) {
    fprintf(stderr, "bootstrap-session: %s\n", reason);
    return 125;
}

int main(int argc, char **argv) {
    /* Batch observer for the parent guard. 0 means the PID disappeared; other
     * errors fail sampling. getsid(), not Darwin ps's session-address column,
     * is the authoritative POSIX session identity. */
    if (argc >= 3 && !strcmp(argv[1], "--sid")) {
        for (int i = 2; i < argc; ++i) {
            char *end;
            errno = 0;
            long pid = strtol(argv[i], &end, 10);
            if (errno || *end || !*argv[i] || pid < 0 || pid > INT_MAX)
                return reject("invalid observation PID");
            pid_t sid = getsid((pid_t)pid);
            if (sid < 0 && errno != ESRCH) return reject("getsid failed");
            printf("%ld %ld\n", pid, sid < 0 ? 0L : (long)sid);
        }
        return 0;
    }
    const char *value = getenv("SIMPLE_BOOTSTRAP_SESSION_ID");
    const char *helper = getenv("SIMPLE_BOOTSTRAP_SESSION_EXEC");
    if (!value || !*value || !helper || helper[0] != '/')
        return reject("missing session contract");
    for (const char *p = value; *p; ++p)
        if (*p < '0' || *p > '9') return reject("invalid session ID");
    char *end;
    errno = 0;
    long expected = strtol(value, &end, 10);
    if (errno || *end || expected <= 0 || expected > INT_MAX)
        return reject("invalid session ID");
    if (getsid(0) != (pid_t)expected)
        return reject("unexpected session ID");
    if (argc == 2 && !strcmp(argv[1], "--check")) return 0;
    if (argc < 3 || strcmp(argv[1], "--")) return reject("expected -- COMMAND");
    /* A runtime-spawned child may already lead its own group. In particular a
     * session leader cannot call setpgid(), but already has the required PGID. */
    if (getpgrp() != getpid() && setpgid(0, 0))
        return reject("setpgid failed");
    if (getsid(0) != (pid_t)expected || getpgrp() != getpid())
        return reject("worker identity mismatch");
    execvp(argv[2], argv + 2);
    perror("bootstrap-session: exec");
    return 127;
}

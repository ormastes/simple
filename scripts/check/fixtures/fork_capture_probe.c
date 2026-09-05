/*
 * Probe for rt_fork_parent_wait_bounded() capture completeness.
 * Driven by scripts/check/check-fork-capture-complete.shs.
 *
 * Modes:
 *   exact <bytes>  child writes <bytes> to BOTH stdout and stderr, then exits.
 *                  Capture must be byte-exact and carry no truncation marker.
 *   bound <bytes>  child writes more than the 4 MiB retention limit.
 *                  Capture must be bounded AND announce the omitted count.
 *   early          child exits immediately but a descendant keeps the pipe
 *                  write end and writes only after a long silence, forcing the
 *                  grace-period early exit. Capture must ANNOUNCE that it is
 *                  incomplete -- silent truncation is the defect under test.
 *
 * Prints one machine-readable line: KEY=VALUE pairs.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "runtime_fork.h"

#define CHUNK 4096

static long write_n(int fd, long bytes) {
    char buf[CHUNK];
    memset(buf, 'A' + (fd == 2), sizeof buf);
    long done = 0;
    while (done < bytes) {
        ssize_t n = write(fd, buf, sizeof buf);
        if (n <= 0) break;
        done += n;
    }
    return done;
}

int main(int argc, char** argv) {
    const char* mode = argc > 1 ? argv[1] : "exact";
    long bytes = argc > 2 ? atol(argv[2]) : (256L * 1024L);
    int early = strcmp(mode, "early") == 0;

    int64_t pid = rt_fork_child_setup();
    if (pid < 0) { printf("ERROR=fork_failed\n"); return 2; }
    if (pid == 0) {
        if (early) {
            if (fork() == 0) { sleep(5); write_n(1, bytes); _exit(0); }
            rt_fork_child_exit(0);
        }
        write_n(1, bytes);
        write_n(2, bytes);
        rt_fork_child_exit(0);
    }

    int64_t rc = rt_fork_parent_wait(pid, 0);
    const char* out = rt_fork_parent_stdout();
    const char* err = rt_fork_parent_stderr();
    long written = ((bytes + CHUNK - 1) / CHUNK) * CHUNK;
    printf("MODE=%s RC=%lld WRITTEN=%ld OUT=%zu ERR=%zu "
           "OUT_TRUNC=%d OUT_INCOMPLETE=%d ERR_TRUNC=%d ERR_INCOMPLETE=%d\n",
           mode, (long long)rc, written, strlen(out), strlen(err),
           strstr(out, "[output truncated:") != NULL,
           strstr(out, "[capture incomplete:") != NULL,
           strstr(err, "[output truncated:") != NULL,
           strstr(err, "[capture incomplete:") != NULL);
    return 0;
}

#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

static void resident(int mb) {
    size_t bytes = (size_t)mb * 1024 * 1024;
    volatile char *p = malloc(bytes);
    if (!p) _exit(71);
    for (size_t i = 0; i < bytes; i += 4096) p[i] = 1;
    sleep(2);
    _exit(0);
}
int main(int argc, char **argv) {
    if (argc != 4) return 64;
    FILE *pids = fopen(argv[3], "a");
    if (!pids) return 73;
    fprintf(pids, "%ld\n", (long)getpid()); fflush(pids);
    pid_t child = fork();
    if (child < 0) return 71;
    if (!child) {
        if (!strcmp(argv[2], "escape")) setsid();
        fprintf(pids, "%ld\n", (long)getpid()); fflush(pids);
        // Stay observable before any escape/fork, then allocate across children.
        usleep(250000);
        if (!strcmp(argv[2], "fork")) {
            for (int i = 0; i < 12; ++i) {
                pid_t grandchild = fork();
                if (!grandchild) {
                    fprintf(pids, "%ld\n", (long)getpid()); fflush(pids);
                    resident(4);
                }
                usleep(10000);
            }
        }
        resident(atoi(argv[1]));
    }
    if (!strcmp(argv[2], "orphan")) { usleep(500000); return 0; }
    int status;
    waitpid(child, &status, 0);
    return 0;
}

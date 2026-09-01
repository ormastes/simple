#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

extern char **environ;

static int isolated(void) {
    int fd;
    if (environ && environ[0] != NULL) return 0;
    for (fd = 3; fd < 1024; ++fd) {
        errno = 0;
        if (fcntl(fd, F_GETFD) >= 0 || errno != EBADF) return 0;
    }
    return 1;
}

int main(int argc, char **argv) {
    char request[4096];
    size_t size = 0;
    long provider;
    if (argc == 2 && strcmp(argv[1], "session") == 0) {
        unsigned long long generation = 0, sequence = 0, invocation = 0;
        if (dprintf(STDOUT_FILENO, "HALWORKER1\n") < 0) return 84;
        for (;;) {
            size = 0;
            while (size + 1 < sizeof(request)) {
                ssize_t count = read(STDIN_FILENO, request + size, 1);
                if (count < 0 && errno == EINTR) continue;
                if (count != 1) return count == 0 ? 0 : 85;
                if (request[size++] == '\n') break;
            }
            request[size] = 0;
            if (sscanf(request, "HALRESET1|%llu|%llu|%llu\n",
                       &generation, &sequence, &invocation) != 3) return 86;
            if (dprintf(STDOUT_FILENO, "HALRESETOK1|%llu|%llu|%llu\n",
                        generation, sequence, invocation) < 0) return 87;
            size = 0;
            while (size + 1 < sizeof(request)) {
                ssize_t count = read(STDIN_FILENO, request + size, 1);
                if (count < 0 && errno == EINTR) continue;
                if (count != 1) return 88;
                if (request[size++] == '\n') break;
            }
            if (size < 9 || memcmp(request, "HALREQ1|", 8) != 0) return 89;
            if (dprintf(STDOUT_FILENO,
                    "HALRES1|0|%llu|0|0|10|20|30|40|32|64|8|8|0|-1|0|5\n",
                    invocation) < 0) return 90;
        }
    }
    if (argc != 3 || !isolated()) return 80;
    provider = strtol(argv[1], NULL, 10);
    while (size + 1 < sizeof(request)) {
        ssize_t count = read(STDIN_FILENO, request + size, 1);
        if (count < 0 && errno == EINTR) continue;
        if (count != 1) return 81;
        if (request[size++] == '\n') break;
    }
    if (size < 2 || request[size - 1] != '\n' ||
        memcmp(request, "HALREQ1|", 8) != 0) return 82;
    if (strcmp(argv[2], "slow") == 0) {
        const struct timespec delay = {.tv_sec = 2, .tv_nsec = 0};
        nanosleep(&delay, NULL);
    }
    if (strcmp(argv[2], "close-then-slow") == 0) {
        const struct timespec delay = {.tv_sec = 2, .tv_nsec = 0};
        close(STDOUT_FILENO);
        nanosleep(&delay, NULL);
        return 0;
    }
    if (dprintf(STDOUT_FILENO,
            "HALRES1|%ld|7|0|0|10|20|30|40|32|64|8|8|0|-1|0|5\n",
            provider) < 0) return 83;
    return 0;
}

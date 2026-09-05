#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static void delay_ms(unsigned milliseconds) {
    struct timespec delay = {
        .tv_sec = milliseconds / 1000,
        .tv_nsec = (long)(milliseconds % 1000) * 1000000L,
    };
    while (nanosleep(&delay, &delay) != 0 && errno == EINTR) {}
}

static uint64_t self_starttime(void) {
    FILE *stream = fopen("/proc/self/stat", "r");
    if (!stream) return 0;
    char line[4096];
    if (!fgets(line, sizeof(line), stream)) { fclose(stream); return 0; }
    fclose(stream);
    char *right = strrchr(line, ')');
    if (!right || right[1] != ' ') return 0;
    char *save = NULL;
    char *token = strtok_r(right + 2, " ", &save);
    unsigned field = 3;
    while (token) {
        if (field == 22) return strtoull(token, NULL, 10);
        token = strtok_r(NULL, " ", &save);
        ++field;
    }
    return 0;
}

static void publish_identity(const char *path) {
    if (!path || path[0] != '/') _exit(90);
    int fd = open(path, O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW|O_CLOEXEC, 0600);
    if (fd < 0) _exit(91);
    char text[128];
    int length = snprintf(text, sizeof(text), "%ld %llu\n", (long)getpid(),
                          (unsigned long long)self_starttime());
    if (length <= 0 || (size_t)length >= sizeof(text) ||
        write(fd, text, (size_t)length) != length || fdatasync(fd) != 0 || close(fd) != 0)
        _exit(92);
}

static void publish_execution_side_effect(void) {
    const char *path = getenv("SIMPLE_STAGE3_RSS_TEST_FIXTURE_SIDE_EFFECT_PATH");
    if (!path) return;
    if (path[0] != '/') _exit(94);
    int fd = open(path, O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW|O_CLOEXEC, 0600);
    if (fd < 0) _exit(95);
    static const char observed[] = "measured-executable-ran\n";
    if (write(fd, observed, sizeof(observed) - 1) != (ssize_t)(sizeof(observed) - 1) ||
        fdatasync(fd) != 0 || close(fd) != 0)
        _exit(96);
}

static void linger(const char *identity_path, int detach, int ignore_term) {
    if (detach && setsid() < 0) _exit(93);
    if (ignore_term) signal(SIGTERM, SIG_IGN);
    publish_identity(identity_path);
    for (;;) pause();
}

int main(int argc, char **argv) {
    publish_execution_side_effect();
    if (argc < 2) return 64;
    if (!strcmp(argv[1], "exec-nocldwait-session")) {
        if (argc < 3) return 64;
        struct sigaction disposition;
        memset(&disposition, 0, sizeof(disposition));
        disposition.sa_handler = SIG_IGN;
        sigemptyset(&disposition.sa_mask);
#ifdef SA_NOCLDWAIT
        disposition.sa_flags = SA_NOCLDWAIT;
#endif
        if (sigaction(SIGCHLD, &disposition, NULL) != 0 ||
            setpgid(0, 0) != 0)
            return 72;
        execvp(argv[2], &argv[2]);
        return 73;
    }
    if (!strcmp(argv[1], "fast")) return 0;
    if (!strcmp(argv[1], "normal")) { delay_ms(140); return 0; }
    if (!strcmp(argv[1], "long")) { delay_ms(900); return 0; }
    if (!strcmp(argv[1], "exit7")) { delay_ms(80); return 7; }
    if (argc != 3 || argv[2][0] != '/') return 64;
    if (!strcmp(argv[1], "detached")) {
        pid_t child = fork();
        if (child < 0) return 70;
        if (!child) linger(argv[2], 1, 0);
        delay_ms(140);
        return 0;
    }
    if (!strcmp(argv[1], "term-ignorer")) {
        pid_t child = fork();
        if (child < 0) return 70;
        if (!child) linger(argv[2], 1, 1);
        delay_ms(140);
        return 0;
    }
    if (!strcmp(argv[1], "adopted")) {
        pid_t middle = fork();
        if (middle < 0) return 70;
        if (!middle) {
            pid_t grandchild = fork();
            if (grandchild < 0) _exit(71);
            if (!grandchild) linger(argv[2], 1, 1);
            _exit(0);
        }
        (void)waitpid(middle, NULL, 0);
        delay_ms(140);
        return 0;
    }
    if (!strcmp(argv[1], "root-exits-first")) {
        pid_t child = fork();
        if (child < 0) return 70;
        if (!child) linger(argv[2], 0, 1);
        while (access(argv[2], F_OK) != 0) delay_ms(1);
        delay_ms(30);
        return 0;
    }
    return 64;
}

#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

struct child { pid_t pid; int input; int output; };

static struct child spawn_child(const char *path, const char *mode) {
    int input[2], output[2];
    if (pipe(input) || pipe(output)) exit(10);
    pid_t pid = fork();
    if (pid < 0) exit(11);
    if (pid == 0) {
        dup2(input[0], STDIN_FILENO);
        dup2(output[1], STDOUT_FILENO);
        close(input[0]); close(input[1]); close(output[0]); close(output[1]);
        execl(path, path, mode, NULL);
        _exit(127);
    }
    close(input[0]); close(output[1]);
    return (struct child){pid, input[1], output[0]};
}

static void send_line(struct child child, int kind) {
    char line[256];
    int size = snprintf(line, sizeof line, "KPFW1|1|%d|7|3|-1|0|5|0|x\n", kind);
    if (write(child.input, line, (size_t)size) != size) exit(12);
}

static int read_line(struct child child, char *buffer, size_t cap, int timeout_ms) {
    struct pollfd descriptor = {child.output, POLLIN, 0};
    if (poll(&descriptor, 1, timeout_ms) <= 0) return 0;
    ssize_t size = read(child.output, buffer, cap - 1);
    if (size <= 0) return 0;
    buffer[size] = '\0';
    return 1;
}

static int finish(struct child child, int signal_number) {
    if (signal_number) kill(child.pid, signal_number);
    close(child.input); close(child.output);
    int status = 0;
    if (waitpid(child.pid, &status, 0) != child.pid) exit(13);
    return status;
}

static void clean_case(const char *path) {
    char output[1024] = {0};
    struct child child = spawn_child(path, "normal");
    send_line(child, 0);
    if (!read_line(child, output, sizeof output, 1000) || !strstr(output, "KPFW1|1|1|")) exit(20);
    send_line(child, 5);
    if (!read_line(child, output, sizeof output, 1000) || !strstr(output, "KPFW1|1|6|")) exit(21);
    send_line(child, 7);
    if (!read_line(child, output, sizeof output, 1000) || !strstr(output, "KPFW1|1|8|")) exit(22);
    int status = finish(child, 0);
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) exit(23);
}

static void malformed_case(const char *path) {
    char output[128] = {0};
    struct child child = spawn_child(path, "malformed");
    send_line(child, 0);
    if (!read_line(child, output, sizeof output, 1000) || strcmp(output, "not-a-kpf-frame\n")) exit(30);
    int status = finish(child, 0);
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 25) exit(31);
}

static void crash_case(const char *path) {
    struct child child = spawn_child(path, "crash");
    send_line(child, 0);
    int status = finish(child, 0);
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 23) exit(40);
}

static void timeout_case(const char *path) {
    char output[32];
    struct child child = spawn_child(path, "timeout");
    send_line(child, 0);
    if (read_line(child, output, sizeof output, 50)) exit(50);
    int status = finish(child, SIGKILL);
    if (!WIFSIGNALED(status) || WTERMSIG(status) != SIGKILL) exit(51);
}

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    clean_case(argv[1]);
    malformed_case(argv[1]);
    crash_case(argv[1]);
    timeout_case(argv[1]);
    puts("real worker native acceptance: PASS");
    return 0;
}

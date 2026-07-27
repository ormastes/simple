#include "runtime.h"

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <sys/socket.h>
#include <sys/resource.h>
#include <sys/syscall.h>
#include <time.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

static const char** test_args;
static int64_t test_arg_count;
static volatile sig_atomic_t sigpipe_count;
static volatile sig_atomic_t alarm_count;

int64_t rt_array_len(SplArray* ignored) {
    (void)ignored;
    return test_arg_count;
}

int64_t rt_array_get(SplArray* ignored, int64_t index) {
    (void)ignored;
    return index + 1;
}

const uint8_t* rt_string_data(int64_t value) {
    return (const uint8_t*)test_args[value - 1];
}

static void count_signal(int signal_number) {
    if (signal_number == SIGPIPE) sigpipe_count++;
    if (signal_number == SIGALRM) alarm_count++;
}

static int64_t spawn_shell(const char* script) {
    static const char* args[2];
    static SplArray placeholder;
    args[0] = "-c";
    args[1] = script;
    test_args = args;
    test_arg_count = 2;
    return rt_process_spawn_piped("/bin/sh", &placeholder);
}

static int sandbox_limit_is(int resource, rlim_t current, rlim_t maximum) {
    struct rlimit limit = {0};
    return syscall(SYS_getrlimit, resource, &limit) == 0 &&
        limit.rlim_cur == current && limit.rlim_max == maximum;
}

static int sandbox_probe(int argc, char** argv) {
    if (argc != 3 || strcmp(argv[0], "simple-browser-renderer") != 0 ||
        getenv("SIMPLE_BROWSER_RENDERER_SECRET") != NULL) {
        return 10;
    }
    char cwd[8];
    if (!getcwd(cwd, sizeof(cwd)) || strcmp(cwd, "/") != 0) return 11;
    int inherited_fd = atoi(argv[2]);
    errno = 0;
    if (fcntl(inherited_fd, F_GETFD) >= 0 || errno != EBADF) return 12;
    if (!rt_browser_renderer_sandbox_enter()) return 13;
    if (!sandbox_limit_is(RLIMIT_CORE, 0, 0) ||
        !sandbox_limit_is(
            RLIMIT_AS, 512U * 1024U * 1024U, 512U * 1024U * 1024U) ||
        !sandbox_limit_is(RLIMIT_CPU, 30, 30) ||
        !sandbox_limit_is(RLIMIT_FSIZE, 0, 0) ||
        !sandbox_limit_is(RLIMIT_NPROC, 0, 0) ||
        !sandbox_limit_is(RLIMIT_NOFILE, 4, 4)) {
        return 14;
    }
    errno = 0;
    if (open("/etc/passwd", O_RDONLY) >= 0 || errno != EACCES) return 15;
    errno = 0;
    if (socket(AF_INET, SOCK_STREAM, 0) >= 0 || errno != EPERM) return 16;
    errno = 0;
    if (fork() >= 0 || errno != EPERM) return 17;
    errno = 0;
    if (kill(getpid(), 0) >= 0 || errno != EPERM) return 18;
    char* exec_args[] = {(char*)"true", NULL};
    char* exec_env[] = {NULL};
    errno = 0;
    if (syscall(SYS_execve, "/bin/true", exec_args, exec_env) >= 0 ||
        errno != EPERM) {
        return 19;
    }
    errno = 0;
    if (setpriority(PRIO_PROCESS, getppid(), 1) >= 0 || errno != EPERM) {
        return 20;
    }
    unsigned long affinity = 1;
    errno = 0;
    if (syscall(
            SYS_sched_setaffinity, getppid(), sizeof(affinity),
            &affinity) >= 0 || errno != EPERM) {
        return 21;
    }
    const char* input = rt_browser_renderer_read_stdin_some(8192);
    if (!input || strcmp(input, "small") != 0) return 22;
    if (write(STDOUT_FILENO, "stdout-leak", 11) < 0) return 23;
    if (write(STDERR_FILENO, "stderr-leak", 11) < 0) return 24;
    return rt_browser_renderer_write_protocol_some(
        "sandbox-ok", 10, 0, 10) == 10 ? 0 : 25;
}

static int sandboxed_renderer_is_sanitized_and_contained(void) {
    static SplArray placeholder;
    int inherited_fd = open("/etc/passwd", O_RDONLY);
    if (inherited_fd < 3) return 0;
    char inherited_text[32];
    snprintf(inherited_text, sizeof(inherited_text), "%d", inherited_fd);
    static const char* args[2];
    args[0] = "--sandbox-probe";
    args[1] = inherited_text;
    test_args = args;
    test_arg_count = 2;
    if (setenv("SIMPLE_BROWSER_RENDERER_SECRET", "must-not-leak", 1) != 0) {
        close(inherited_fd);
        return 0;
    }
    int64_t pid = rt_browser_renderer_spawn_sandboxed(
        "/proc/self/exe", &placeholder);
    close(inherited_fd);
    unsetenv("SIMPLE_BROWSER_RENDERER_SECRET");
    if (pid <= 0) return 0;
    if (!rt_process_write_stdin(pid, "small")) {
        rt_process_close_piped(pid);
        return 0;
    }
    int saw_ok = 0;
    for (int i = 0; i < 2000 && !saw_ok; i++) {
        const char* chunk = rt_process_read_stdout(pid);
        saw_ok = chunk && strcmp(chunk, "sandbox-ok") == 0;
        if (!saw_ok) usleep(1000);
    }
    int closed = rt_process_close_piped(pid);
    return saw_ok && closed;
}

static int stopped(pid_t pid) {
    if (pid <= 0) return 0;
    if (kill(pid, 0) != 0) return errno == ESRCH;
#ifdef __linux__
    char path[64];
    snprintf(path, sizeof(path), "/proc/%ld/stat", (long)pid);
    FILE* file = fopen(path, "r");
    if (!file) return 1;
    long ignored = 0;
    char name[256];
    char state = 0;
    int fields = fscanf(file, "%ld %255s %c", &ignored, name, &state);
    fclose(file);
    return fields == 3 && state == 'Z';
#else
    return 0;
#endif
}

static int read_pid_from_child(int64_t pid, pid_t* child_pid) {
    for (int i = 0; i < 1000; i++) {
        const char* chunk = rt_process_read_stdout(pid);
        if (chunk && sscanf(chunk, "%d", child_pid) == 1) return 1;
        usleep(1000);
    }
    return 0;
}

static int closed_child_write_is_nonfatal(void) {
    struct sigaction action = {0};
    action.sa_handler = count_signal;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGPIPE, &action, NULL) != 0) return 0;

    int64_t pid = spawn_shell("exec 0<&-; sleep 1");
    if (pid <= 0) return 0;
    usleep(20000);
    char payload[65537];
    memset(payload, 'x', sizeof(payload) - 1);
    payload[sizeof(payload) - 1] = '\0';
    int ok = !rt_process_write_stdin(pid, payload) && sigpipe_count == 0;
    kill((pid_t)pid, SIGTERM);
    while (rt_process_is_alive(pid)) usleep(1000);
    return ok;
}

static int interrupted_large_write_completes(void) {
    struct sigaction action = {0};
    action.sa_handler = count_signal;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGALRM, &action, NULL) != 0) return 0;

    int64_t pid = spawn_shell(
        "sleep 0.05; dd bs=1 count=262144 of=/dev/null 2>/dev/null; printf ok"
    );
    if (pid <= 0) return 0;
    char* payload = (char*)malloc(262145);
    if (!payload) return 0;
    memset(payload, 'y', 262144);
    payload[262144] = '\0';

    struct itimerval timer = {0};
    timer.it_value.tv_usec = 10000;
    setitimer(ITIMER_REAL, &timer, NULL);
    int wrote = rt_process_write_stdin(pid, payload);
    free(payload);

    int saw_ok = 0;
    for (int i = 0; i < 1000 && !saw_ok; i++) {
        const char* chunk = rt_process_read_stdout(pid);
        saw_ok = chunk && strstr(chunk, "ok") != NULL;
        if (!saw_ok) usleep(1000);
    }
    while (rt_process_is_alive(pid)) usleep(1000);
    return wrote && alarm_count > 0 && saw_ok;
}

static int bounded_write_reports_backpressure(void) {
    int64_t pid = spawn_shell("sleep 1");
    if (pid <= 0) return 0;
    char payload[4096];
    memset(payload, 'z', sizeof(payload));
    int saw_would_block = 0;
    for (int64_t offset = 0; offset < 1048576; offset += sizeof(payload)) {
        int64_t written = rt_process_write_stdin_some(
            pid, payload, sizeof(payload), 0, sizeof(payload));
        if (written < 0) {
            rt_process_close_piped(pid);
            return 0;
        }
        if (written == 0) {
            saw_would_block = 1;
            break;
        }
    }
    int closed = rt_process_close_piped(pid);
    return saw_would_block && closed &&
        rt_process_write_stdin_some(pid, payload, sizeof(payload), 0, sizeof(payload)) == -1;
}

static int inherited_descriptor_is_closed(void) {
#if !defined(__linux__) && !defined(__APPLE__)
    return 1;
#else
    int source_fd = open("/etc/passwd", O_RDONLY);
    if (source_fd < 0) return 0;
    int inherited_fd = fcntl(source_fd, F_DUPFD, 64);
    close(source_fd);
    if (inherited_fd < 0 ||
        fcntl(inherited_fd, F_SETFD, 0) != 0) {
        if (inherited_fd >= 0) close(inherited_fd);
        return 0;
    }
    char script[160];
    snprintf(
        script, sizeof(script),
#ifdef __APPLE__
        "if [ -e /dev/fd/%d ]; then printf leak; else printf clean; fi; sleep 30",
#else
        "if [ -e /proc/self/fd/%d ]; then printf leak; else printf clean; fi; sleep 30",
#endif
        inherited_fd
    );
    int64_t pid = spawn_shell(script);
    if (pid <= 0) {
        close(inherited_fd);
        return 0;
    }
    int clean = 0;
    int leaked = 0;
    for (int i = 0; i < 1000 && !clean; i++) {
        const char* chunk = rt_process_read_stdout(pid);
        clean = chunk && strstr(chunk, "clean") != NULL;
        leaked = chunk && strstr(chunk, "leak") != NULL;
        if (!clean) usleep(1000);
    }
    int closed = rt_process_close_piped(pid);
    close(inherited_fd);
    if (!clean || !closed) {
        fprintf(
            stderr, "inherited fd check: clean=%d leak=%d closed=%d\n",
            clean, leaked, closed);
    }
    return clean && closed;
#endif
}

static int exact_close_kills_and_reaps_group(void) {
    int64_t pid = spawn_shell("sleep 30 & echo $!; wait");
    pid_t grandchild = -1;
    if (pid <= 0 || !read_pid_from_child(pid, &grandchild)) return 0;
    if (!rt_process_close_piped(pid)) return 0;
#ifdef __APPLE__
    for (int i = 0; i < 1000; i++) {
        if (kill(-(pid_t)pid, 0) != 0 && errno == ESRCH) {
            return stopped((pid_t)pid);
        }
        usleep(1000);
    }
    return 0;
#else
    for (int i = 0; i < 1000 && !stopped(grandchild); i++) usleep(1000);
    return stopped((pid_t)pid) && stopped(grandchild);
#endif
}

static int reaped_leader_still_kills_group(void) {
    int64_t pid = spawn_shell("trap '' TERM; sleep 30 & echo $!; exit 0");
    pid_t grandchild = -1;
    if (pid <= 0 || !read_pid_from_child(pid, &grandchild)) return 0;
    usleep(20000);
    if (!rt_process_close_piped(pid)) return 0;
#ifdef __APPLE__
    for (int i = 0; i < 1000; i++) {
        if (kill(-(pid_t)pid, 0) != 0 && errno == ESRCH) return 1;
        usleep(1000);
    }
    return 0;
#else
    for (int i = 0; i < 1000 && !stopped(grandchild); i++) usleep(1000);
    return stopped(grandchild);
#endif
}

static int close_recycles_slots_and_rejects_unknown_handles(void) {
    if (rt_process_close_piped(-1) || rt_process_close_piped(999999999)) return 0;
    struct timespec started;
    struct timespec finished;
    if (clock_gettime(CLOCK_MONOTONIC, &started) != 0) return 0;
    for (int i = 0; i < 32; i++) {
        int64_t pid = spawn_shell("exit 0");
        if (pid <= 0) return 0;
        usleep(1000);
        if (!rt_process_close_piped(pid)) return 0;
        if (rt_process_write_stdin(pid, "late") || rt_process_is_alive(pid)) return 0;
    }
    if (clock_gettime(CLOCK_MONOTONIC, &finished) != 0) return 0;
    double elapsed = (double)(finished.tv_sec - started.tv_sec) +
        (double)(finished.tv_nsec - started.tv_nsec) / 1000000000.0;
    return elapsed < 5.0;
}

static int parent_death_stops_child(void) {
#ifndef __linux__
    return 1;
#else
    char path[128];
    snprintf(path, sizeof(path), "/tmp/simple-piped-parent-%ld.pid", (long)getpid());
    unlink(path);
    pid_t launcher = fork();
    if (launcher == 0) {
        char script[256];
        snprintf(script, sizeof(script), "echo $$ > '%s'; exec sleep 30", path);
        if (spawn_shell(script) <= 0) _exit(2);
        for (int i = 0; i < 1000 && access(path, R_OK) != 0; i++) usleep(1000);
        _exit(access(path, R_OK) == 0 ? 0 : 3);
    }
    if (launcher < 0) return 0;
    int status = 0;
    if (waitpid(launcher, &status, 0) != launcher ||
        !WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        return 0;
    }
    FILE* file = fopen(path, "r");
    long child = -1;
    if (!file || fscanf(file, "%ld", &child) != 1) {
        if (file) fclose(file);
        unlink(path);
        return 0;
    }
    fclose(file);
    unlink(path);
    for (int i = 0; i < 1000 && !stopped((pid_t)child); i++) usleep(1000);
    return stopped((pid_t)child);
#endif
}

int main(int argc, char** argv) {
    if (argc > 1 && strcmp(argv[1], "--sandbox-probe") == 0) {
        return sandbox_probe(argc, argv);
    }
    if (!closed_child_write_is_nonfatal()) return 1;
    if (!interrupted_large_write_completes()) return 2;
    if (!bounded_write_reports_backpressure()) return 3;
    if (!inherited_descriptor_is_closed()) return 4;
    if (!exact_close_kills_and_reaps_group()) return 5;
    if (!reaped_leader_still_kills_group()) return 6;
    if (!close_recycles_slots_and_rejects_unknown_handles()) return 7;
    if (!parent_death_stops_child()) return 8;
    if (!sandboxed_renderer_is_sanitized_and_contained()) return 9;
    return 0;
}

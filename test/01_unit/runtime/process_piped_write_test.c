#include "runtime.h"

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
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

static int inherited_descriptor_is_closed(void) {
#ifndef __linux__
    return 1;
#else
    int inherited_fd = open("/etc/passwd", O_RDONLY);
    if (inherited_fd < 3) return 0;
    char script[160];
    snprintf(
        script, sizeof(script),
        "if [ -e /proc/self/fd/%d ]; then printf leak; else printf clean; fi",
        inherited_fd
    );
    int64_t pid = spawn_shell(script);
    if (pid <= 0) return 0;
    int clean = 0;
    for (int i = 0; i < 1000 && !clean; i++) {
        const char* chunk = rt_process_read_stdout(pid);
        clean = chunk && strstr(chunk, "clean") != NULL;
        if (!clean) usleep(1000);
    }
    int closed = rt_process_close_piped(pid);
    close(inherited_fd);
    return clean && closed;
#endif
}

static int exact_close_kills_and_reaps_group(void) {
    int64_t pid = spawn_shell("sleep 30 & echo $!; wait");
    pid_t grandchild = -1;
    if (pid <= 0 || !read_pid_from_child(pid, &grandchild)) return 0;
    if (!rt_process_close_piped(pid)) return 0;
    for (int i = 0; i < 1000 && !stopped(grandchild); i++) usleep(1000);
    return stopped((pid_t)pid) && stopped(grandchild);
}

static int close_recycles_slots_and_rejects_unknown_handles(void) {
    if (rt_process_close_piped(-1) || rt_process_close_piped(999999999)) return 0;
    for (int i = 0; i < 32; i++) {
        int64_t pid = spawn_shell("exit 0");
        if (pid <= 0) return 0;
        usleep(1000);
        if (!rt_process_close_piped(pid)) return 0;
        if (rt_process_write_stdin(pid, "late") || rt_process_is_alive(pid)) return 0;
    }
    return 1;
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

int main(void) {
    if (!closed_child_write_is_nonfatal()) return 1;
    if (!interrupted_large_write_completes()) return 2;
    if (!inherited_descriptor_is_closed()) return 3;
    if (!exact_close_kills_and_reaps_group()) return 4;
    if (!close_recycles_slots_and_rejects_unknown_handles()) return 5;
    if (!parent_death_stops_child()) return 6;
    return 0;
}

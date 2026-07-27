#include "runtime.h"

#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
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

int main(void) {
    if (!closed_child_write_is_nonfatal()) return 1;
    if (!interrupted_large_write_completes()) return 2;
    return 0;
}

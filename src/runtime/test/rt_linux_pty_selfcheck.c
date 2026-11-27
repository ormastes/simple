#include "runtime.h"
#include <assert.h>
#include <fcntl.h>
#include <stdbool.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static int64_t text(const char* value) {
    return rt_string_new((const uint8_t*)value, strlen(value));
}

static void release_text_array(SplArray* values) {
    for (int64_t i = 0; i < rt_array_len(values); ++i) {
        rt_string_free(rt_array_get_text(values, i));
    }
    rt_array_free(values);
}

static bool read_until(int64_t handle, const char* needle, char* output, size_t capacity) {
    size_t used = 0;
    for (int attempt = 0; attempt < 20; ++attempt) {
        int64_t text = rt_pty_read(handle, 100);
        int64_t length = rt_string_len(text);
        if (length < 0 || (uint64_t)length >= capacity - used) return false;
        if (length > 0) {
            memcpy(output + used, rt_string_data(text), (size_t)length);
            used += (size_t)length;
        }
        rt_string_free(text);
        output[used] = 0;
        if (strstr(output, needle)) return true;
    }
    return false;
}

int main(void) {
    char output[16384];
    assert(rt_pty_open(0, 80) == -1);
    assert(!rt_value_as_bool(rt_pty_close(-1)));
    assert(setenv("SIMPLE_PTY_DROP", "parent-only", 1) == 0);
    int32_t handle = rt_pty_open(24, 80);
    assert(handle > 0);
    assert(rt_pty_exit_code_v1(handle) == -2);
    assert(rt_pty_resize(handle, 31, 57));
    int sockets[2];
    assert(socketpair(AF_UNIX, SOCK_STREAM | SOCK_NONBLOCK, 0, sockets) == 0);
    int inherited = fcntl(sockets[0], F_DUPFD, 50);
    close(sockets[0]);
    assert(inherited >= 50);
    char fd_value[64];
    snprintf(fd_value, sizeof(fd_value), "+SIMPLE_PTY_PARENT_FD=%d", inherited);
    SplArray* args = rt_array_new(2);
    SplArray* changes = rt_array_new(3);
    assert(rt_array_push(args, text("-c")));
    assert(rt_array_push(args, text("test ! -e /proc/$$/fd/$SIMPLE_PTY_PARENT_FD && "
        "test -t 0 && test -t 1 && test -t 2 && "
        "test \"$(pwd)\" = / && test \"$(stty -F /dev/tty size)\" = '31 57' && "
        "test -z \"${SIMPLE_PTY_DROP+x}\" && "
        "printf 'ready:%s\\n' \"$SIMPLE_PTY_KEEP\" && IFS= read -r msg && "
        "printf 'pty-ack:%s\\n' \"$msg\" && exit 7; exit 8")));
    assert(rt_array_push(changes, text("+SIMPLE_PTY_KEEP=child")));
    assert(rt_array_push(changes, text("-SIMPLE_PTY_DROP")));
    assert(rt_array_push(changes, text(fd_value)));
    int64_t program = text("/bin/sh");
    int64_t cwd = text("/");
    assert(rt_pty_spawn_exec_v1(handle, (const char*)(uintptr_t)program, args,
        (const char*)(uintptr_t)cwd, changes) > 1);
    rt_string_free(program);
    rt_string_free(cwd);
    release_text_array(args);
    release_text_array(changes);
    assert(rt_value_as_bool(rt_pty_is_running(handle)));
    assert(rt_pty_exit_code_v1(handle) == -1);
    assert(read_until(handle, "ready:child", output, sizeof(output)));
    close(inherited);
    char peer_byte;
    assert(read(sockets[1], &peer_byte, 1) == 0);
    close(sockets[1]);
    const char input[] = "literal-send\n";
    SplArray* bytes = rt_array_new(sizeof(input) - 1);
    for (size_t i = 0; i < sizeof(input) - 1; ++i) {
        assert(rt_array_push(bytes, rt_value_int(input[i])));
    }
    assert(rt_pty_write_bytes_v1(handle, bytes) == (int64_t)sizeof(input) - 1);
    rt_array_free(bytes);
    assert(read_until(handle, "pty-ack:literal-send", output, sizeof(output)));
    int64_t exit = -1;
    const struct timespec pause = {.tv_nsec = 10000000};
    for (int attempt = 0; attempt < 100 && exit == -1; ++attempt) {
        exit = rt_pty_exit_code_v1(handle);
        if (exit == -1) nanosleep(&pause, NULL);
    }
    assert(exit == 7);
    assert(rt_value_as_bool(rt_pty_close(handle)));
    assert(rt_value_as_bool(rt_pty_close(handle)));
    int64_t stale = text("stale");
    assert(!rt_value_as_bool(rt_pty_write(handle, stale)));
    rt_string_free(stale);

    int32_t legacy = rt_pty_open(24, 80);
    assert(legacy > 0 && legacy != handle);
    int64_t command = text("/bin/sh -c 'read line; printf \"legacy:%s\\n\" \"$line\"; sleep 10'");
    assert(rt_pty_spawn(legacy, command) > 1);
    rt_string_free(command);
    int64_t message = text("yes\n");
    assert(rt_value_as_bool(rt_pty_write(legacy, message)));
    rt_string_free(message);
    assert(read_until(legacy, "legacy:yes", output, sizeof(output)));
    assert(rt_pty_hangup(legacy));
    assert(rt_value_as_bool(rt_pty_close(legacy)));
    assert(!rt_value_as_bool(rt_pty_is_running(legacy)));

    /* Keep the orphan reparented here so the test observes actual termination. */
    assert(prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) == 0);
    int32_t detached = rt_pty_open(24, 80);
    assert(detached > 0);
    command = text("/bin/sh -c 'trap \"\" HUP; sleep 30 & printf \"worker:%s:end\\n\" \"$!\"; exit 0'");
    assert(rt_pty_spawn(detached, command) > 1);
    rt_string_free(command);
    assert(read_until(detached, ":end", output, sizeof(output)));
    const char* worker_line = strstr(output, "worker:");
    int worker;
    assert(worker_line && sscanf(worker_line, "worker:%d:end", &worker) == 1 && worker > 1);
    exit = -1;
    for (int attempt = 0; attempt < 100 && exit == -1; ++attempt) {
        exit = rt_pty_exit_code_v1(detached);
        if (exit == -1) nanosleep(&pause, NULL);
    }
    assert(exit == 0);
    assert(waitpid(worker, NULL, WNOHANG) == 0);
    assert(rt_value_as_bool(rt_pty_close(detached)));
    int status;
    assert(waitpid(worker, &status, 0) == worker);
    assert(WIFSIGNALED(status) && WTERMSIG(status) == SIGKILL);
    puts("PASS Linux core-C PTY controlling terminal, I/O, resize, exit, and cleanup");
}

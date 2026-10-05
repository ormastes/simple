/* Native POSIX process capture must retain byte lengths, not strlen lengths. */
#include "runtime.h"
#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

static const unsigned char out_bytes[] = {'A', 0, 'B', 0};
static const unsigned char err_bytes[] = {'E', 0, 'F', 0};

static SplArray* run(const char* executable, const char* mode, int64_t timeout, int64_t cap) {
    SplArray* args = rt_array_new(1);
    rt_array_push(args, rt_string_new((const uint8_t*)mode, strlen(mode)));
    return rt_process_run_bounded(executable, strlen(executable), args, timeout, cap);
}

static void equals(int64_t text, const void* bytes, size_t len) {
    assert(rt_string_len(text) == (int64_t)len);
    assert(memcmp(rt_string_data(text), bytes, len) == 0);
}

int main(int argc, char** argv) {
    if (argc == 2) {
        if (strcmp(argv[1], "empty") == 0) return 0;
        assert(write(STDOUT_FILENO, out_bytes, sizeof out_bytes) == sizeof out_bytes);
        assert(write(STDERR_FILENO, err_bytes, sizeof err_bytes) == sizeof err_bytes);
        if (strcmp(argv[1], "timeout") == 0) for (;;) pause();
        return 23;
    }

    SplArray* result = run(argv[0], "bytes", 2000, 64);
    equals(rt_array_get(result, 0), out_bytes, sizeof out_bytes);
    equals(rt_array_get(result, 1), err_bytes, sizeof err_bytes);
    assert(rt_value_as_int(rt_array_get(result, 2)) == 23);

    /* The existing head/tail bound and explicit omission marker stay intact. */
    result = run(argv[0], "bytes", 2000, 2);
    static const char capped_out[] = "A\n[output truncated: 2 bytes omitted]\n\0";
    static const char capped_err[] = "E\n[output truncated: 2 bytes omitted]\n\0";
    equals(rt_array_get(result, 0), capped_out, sizeof capped_out - 1);
    equals(rt_array_get(result, 1), capped_err, sizeof capped_err - 1);
    assert(rt_value_as_int(rt_array_get(result, 2)) == 23);

    result = run(argv[0], "timeout", 200, 64);
    int64_t out = rt_array_get(result, 0), err = rt_array_get(result, 1);
    assert(rt_string_len(out) >= sizeof out_bytes);
    assert(rt_string_len(err) > sizeof err_bytes);
    assert(memcmp(rt_string_data(out), out_bytes, sizeof out_bytes) == 0);
    assert(memcmp(rt_string_data(err), err_bytes, sizeof err_bytes) == 0);
    assert(strstr((const char*)rt_string_data(err) + sizeof err_bytes, "[TIMEOUT:") != NULL);
    assert(rt_value_as_int(rt_array_get(result, 2)) == -1);
    int status;
    errno = 0;
    assert(waitpid(-1, &status, WNOHANG) == -1 && errno == ECHILD);

    /* A subsequent capture must reset both stored lengths. */
    result = run(argv[0], "empty", 2000, 64);
    equals(rt_array_get(result, 0), "", 0);
    equals(rt_array_get(result, 1), "", 0);
    assert(rt_value_as_int(rt_array_get(result, 2)) == 0);
    puts("PASS: binary stdout/stderr, exit status, cap, timeout/reap, length reset");
    return 0;
}

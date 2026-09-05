#include "runtime.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

int main(void) {
    int error_pipe[2];
    assert(pipe(error_pipe) == 0);
    int saved_stderr = dup(STDERR_FILENO);
    assert(saved_stderr >= 0);
    assert(dup2(error_pipe[1], STDERR_FILENO) >= 0);
    close(error_pipe[1]);

    assert(rt_array_len_safe(9) == 0);
    assert(rt_array_len_safe(17) == 0);
    assert(rt_array_len_safe(-7) == 0);

    assert(fflush(stderr) == 0);
    assert(dup2(saved_stderr, STDERR_FILENO) >= 0);
    close(saved_stderr);
    char error_log[512] = {0};
    ssize_t error_len = read(error_pipe[0], error_log, sizeof(error_log) - 1);
    close(error_pipe[0]);
    assert(error_len > 0);
    assert(strstr(error_log, "[simple-runtime][error]") != 0);
    assert(strstr(error_log, "probable compiler/FFI ABI mismatch") != 0);
    assert(strstr(error_log, "value_bits=0x0000000000000009") != 0);
    assert(strchr(error_log, '\n') == strrchr(error_log, '\n'));

    SplArray* array = rt_array_new(1);
    assert(array != 0);
    assert(rt_array_push(array, 42));
    assert(rt_array_len_safe((int64_t)(uintptr_t)array) == 1);
    assert(rt_array_get(array, 0) == 42);
    rt_array_free(array);
    return 0;
}

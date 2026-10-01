/* Link against either runtime provider; exercise the real OS child and argv. */
#include "runtime.h"
#include <stdio.h>
#include <string.h>
#include <stdint.h>

static int64_t text(const char *s) {
    return rt_string_new((const uint8_t *)s, (uint64_t)strlen(s));
}
static int spawn_check(const char *self, int raw) {
    SplArray *args = rt_array_new(4);
    rt_array_push(args, text("--child"));
    rt_array_push(args, text("space value"));
    rt_array_push(args, text("quote\"value"));
    rt_array_push(args, text(""));
    int64_t command = raw ? (int64_t)(uintptr_t)self : text(self);
    int64_t pid = rt_process_spawn_async_value(command, args);
    if (pid <= 0) { fprintf(stderr, "spawn failed raw=%d pid=%lld\n", raw, (long long)pid); return 1; }
    int64_t status = rt_process_wait(pid, 10000);
    if (status != 37) { fprintf(stderr, "argv/wait failed raw=%d status=%lld\n", raw, (long long)status); return 1; }
    return 0;
}
int main(int argc, char **argv) {
    if (argc > 1 && strcmp(argv[1], "--child") == 0) {
        return argc == 5 && strcmp(argv[2], "space value") == 0 &&
               strcmp(argv[3], "quote\"value") == 0 && strcmp(argv[4], "") == 0 ? 37 : 99;
    }
    if (argc != 2 || strcmp(argv[1], "--parent") != 0) return 99;
    if (spawn_check(argv[0], 0) || spawn_check(argv[0], 1)) return 1;
    SplArray *empty = rt_array_new(0);
    if (rt_process_spawn_async_value(0, empty) != -1) return 2;
    int64_t missing = rt_process_spawn_async_value(text("__simple_missing_spawn_abi_program__"), empty);
    /* fork/exec C providers report ENOENT in the child; Rust rejects at spawn. */
    if (missing != -1 && (missing <= 0 || rt_process_wait(missing, 10000) != 127)) return 3;
    /* Five-byte native inline text, in addition to the heap-sized self path. */
    int64_t short_missing = rt_process_spawn_async_value(text("./zzz"), empty);
    if (short_missing != -1 && (short_missing <= 0 || rt_process_wait(short_missing, 10000) != 127)) return 4;
#ifdef SIMPLE_RUST_RUNTIME_PROVIDER
    if (rt_process_spawn_async_value((int64_t)(uintptr_t)empty, empty) != -1) return 5;
    if (rt_process_spawn_async_value(text(argv[0]), (SplArray*)(uintptr_t)text("not-array")) != -1) return 6;
    SplArray *invalid = rt_array_new(1);
    rt_array_push(invalid, rt_value_int(7));
    if (rt_process_spawn_async_value(text(argv[0]), invalid) != -1) return 7;
#endif
    puts("PASS: spawn value ABI tagged/raw/short commands, quoted/empty argv, wait exit, missing command");
    return 0;
}

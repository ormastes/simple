/* Non-Windows test: the POSIX session owner it drives has no Windows build here. */
#if defined(_WIN32)
#include <stdio.h>
int main(void) { puts("SKIP: process_spawn_value_counted_text_selfcheck is POSIX-only; no Windows build"); return 77; }
#else
/* The rt_process_spawn_*_value facades must read text by its byte length,
 * never up to a NUL.
 *
 * In the mixed link of a seed-built compiler (Rust simple_runtime + this C
 * supplement), strings come from the Rust alloc_runtime_string, which sizes
 * header + len with NO trailing NUL (value/sffi/package.rs). The C facade read
 * them through rt_interp_cstr as C strings, so heap slack after len leaked into
 * the child's argv: the native codegen pool's "/bin/sh -c '... 2>&1'" ran as
 * "... 2>&1}}" and failed. This check reproduces that layout in the pure-C
 * runtime by overwriting each string's terminator (C allocates len + 1, so the
 * write stays in bounds), then requires the child to see exactly len bytes.
 *
 * Build and run (clang, never GCC): archive the core-C runtime sources
 * (SOURCE_FILES in scripts/check/build-core-c-bootstrap-runtime-capsule.shs,
 * plus runtime_socket_nonblock.c), compiled with
 *   clang -c -Os -fPIC -std=gnu11 -DSIMPLE_CORE_C_STANDALONE=1 \
 *         -DSIMPLE_RUNTIME_MEMORY_OWNER=1 -I src/runtime -I src/runtime/platform
 * then link:
 *   clang -std=gnu11 -O1 -I src/runtime \
 *      src/runtime/test/process_spawn_value_counted_text_selfcheck.c \
 *      libsimple_runtime.a -lm -lpthread -ldl -o /tmp/pscounted && /tmp/pscounted
 */
#include "runtime.h"
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern int64_t rt_string_len(int64_t string);
extern int64_t rt_process_spawn_session_value(int64_t cmd, SplArray* args);
extern int64_t rt_process_spawn_async_value(int64_t cmd, SplArray* args);
extern int64_t rt_process_session_wait(int64_t pid, int64_t timeout_ms);
extern int64_t rt_process_wait(int64_t pid, int64_t timeout_ms);
extern int64_t rt_process_tree_support(void);

static int failures = 0;
#define CHECK(cond, ...) do { \
    if (!(cond)) { failures++; fprintf(stderr, "FAIL %s:%d: ", __FILE__, __LINE__); fprintf(stderr, __VA_ARGS__); fputc('\n', stderr); } \
    else { fprintf(stderr, "ok   "); fprintf(stderr, __VA_ARGS__); fputc('\n', stderr); } \
} while (0)

/* A counted string whose byte after len is NOT a NUL, like a Rust-runtime string. */
static int64_t unterminated(const char* text) {
    int64_t value = rt_string_new((const uint8_t*)text, strlen(text));
    char* data = (char*)rt_string_data(value);
    data[rt_string_len(value)] = '}';
    return value;
}

static SplArray* shell_args(const char* line) {
    SplArray* args = rt_array_new(2);
    rt_array_push(args, unterminated("-c"));
    rt_array_push(args, unterminated(line));
    return args;
}

int main(void) {
    int64_t sh = unterminated("/bin/sh");
    CHECK(rt_string_len(sh) == 7, "counted length survives the overwritten terminator");

    if (rt_process_tree_support() == 0) {
        int64_t pid = rt_process_spawn_session_value(sh, shell_args("exit 7"));
        CHECK(pid > 0, "session spawn of an unterminated command succeeds (pid=%lld)", (long long)pid);
        if (pid > 0) {
            int64_t code = rt_process_session_wait(pid, 10000);
            CHECK(code == 7, "session child sees exactly len bytes (exit=%lld, want 7)", (long long)code);
        }
    } else {
        fprintf(stderr, "skip session arm: no session owner on this host\n");
    }

    int64_t pid = rt_process_spawn_async_value(sh, shell_args("exit 9"));
    CHECK(pid > 0, "async spawn of an unterminated command succeeds (pid=%lld)", (long long)pid);
    if (pid > 0) {
        int64_t code = rt_process_wait(pid, 10000);
        CHECK(code == 9, "async child sees exactly len bytes (exit=%lld, want 9)", (long long)code);
    }

    if (failures) {
        fprintf(stderr, "process_spawn_value_counted_text_selfcheck: %d failure(s)\n", failures);
        return 1;
    }
    puts("process_spawn_value_counted_text_selfcheck: PASS");
    return 0;
}
#endif

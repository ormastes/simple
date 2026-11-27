/* Non-Windows test: the POSIX owners it drives have no Windows build here. */
#if defined(_WIN32)
#include <stdio.h>
int main(void) { puts("SKIP: process_spawn_value_counted_text_selfcheck is POSIX-only; no Windows build"); return 77; }
#else
/* C runtime entry points that hand text to a NUL-dependent consumer (exec,
 * open, getenv, dlsym, strtoll, inet_pton) must read it by its byte length,
 * never up to a NUL.
 *
 * In the mixed link of a seed-built compiler (Rust simple_runtime + this C
 * supplement), strings come from the Rust alloc_runtime_string, which sizes
 * header + len with NO trailing NUL (value/sffi/package.rs). The C side read
 * them through rt_interp_cstr as C strings, so heap slack after len leaked into
 * the consumer: the native codegen pool's "/bin/sh -c '... 2>&1'" ran as
 * "... 2>&1}}" and failed. This check reproduces that layout in the pure-C
 * runtime by overwriting each string's terminator (C allocates len + 1, so the
 * write stays in bounds), then requires each consumer to see exactly len bytes.
 * One case per consumer class. See
 * doc/08_tracking/bug/process_spawn_value_reads_past_counted_text_2026-11-21.md
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
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

extern int64_t rt_string_len(int64_t string);
extern int64_t rt_process_spawn_session_value(int64_t cmd, SplArray* args);
extern int64_t rt_process_spawn_async_value(int64_t cmd, SplArray* args);
extern int64_t rt_process_run_inherit_value(int64_t cmd, SplArray* args);
extern int64_t rt_process_session_wait(int64_t pid, int64_t timeout_ms);
extern int64_t rt_process_wait(int64_t pid, int64_t timeout_ms);
extern int64_t rt_process_tree_support(void);
extern int64_t rt_open_fd(const char* path, int64_t flags, int64_t mode);
extern int64_t rt_env_get_value(int64_t key);
extern int64_t spl_dlsym_process_checked(int64_t name_value, int64_t* out_symbol);
extern int64_t rt_string_to_int_any(int64_t value);
extern int64_t rt_io_udp_bind(int64_t addr_val);

static int failures = 0;
#define CHECK(cond, ...) do { \
    if (!(cond)) { failures++; fprintf(stderr, "FAIL %s:%d: ", __FILE__, __LINE__); fprintf(stderr, __VA_ARGS__); fputc('\n', stderr); } \
    else { fprintf(stderr, "ok   "); fprintf(stderr, __VA_ARGS__); fputc('\n', stderr); } \
} while (0)

/* A counted string whose byte after len is `tail`, not a NUL, like a
 * Rust-runtime string. */
static int64_t unterminated_with(const char* text, char tail) {
    int64_t value = rt_string_new((const uint8_t*)text, strlen(text));
    char* data = (char*)rt_string_data(value);
    data[rt_string_len(value)] = tail;
    return value;
}

static int64_t unterminated(const char* text) { return unterminated_with(text, '}'); }

static SplArray* shell_args(const char* line) {
    SplArray* args = rt_array_new(2);
    rt_array_push(args, unterminated("-c"));
    rt_array_push(args, unterminated(line));
    return args;
}

int main(void) {
    int64_t sh = unterminated("/bin/sh");
    CHECK(rt_string_len(sh) == 7, "counted length survives the overwritten terminator");

    /* exec: session, async and run_inherit facades. */
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

    int64_t inherit = rt_process_run_inherit_value(sh, shell_args("exit 5"));
    CHECK(inherit == 5, "run_inherit args are read by length (exit=%lld, want 5)", (long long)inherit);

    /* open(2): an existing file named by an unterminated path. */
    char path[] = "/tmp/pscounted-open-XXXXXX";
    int tmp = mkstemp(path);
    if (tmp >= 0) close(tmp);
    int64_t fd = rt_open_fd((const char*)(uintptr_t)unterminated_with(path, 'X'), O_RDONLY, 0);
    CHECK(fd >= 0, "open path is read by length (fd=%lld)", (long long)fd);
    if (fd >= 0) close((int)fd);
    unlink(path);

    /* getenv: an unterminated key still names the variable. */
    setenv("PSCOUNTED_KEY", "v", 1);
    int64_t env = rt_env_get_value(unterminated_with("PSCOUNTED_KEY", '_'));
    CHECK(rt_string_len(env) == 1, "getenv key is read by length (len=%lld, want 1)", (long long)rt_string_len(env));

    /* dlsym: an unterminated symbol name resolves. */
    int64_t symbol = 0;
    int64_t rc = spl_dlsym_process_checked(unterminated("malloc"), &symbol);
    CHECK(rc == 0 && symbol != 0, "dlsym name is read by length (rc=%lld)", (long long)rc);

    /* strtoll: a text data pointer (counted by its owner, not C-registered as a
     * handle) must not pick up the digit after len. */
    int64_t twelve = unterminated_with("12", '7');
    int64_t parsed = rt_string_to_int_any((int64_t)(uintptr_t)rt_string_data(twelve));
    CHECK(parsed == 12, "int(text) is bounded by length (got %lld, want 12)", (long long)parsed);

    /* inet: "127.0.0.1" has no port; a ':' after len must not supply one. */
    int64_t udp = rt_io_udp_bind(unterminated_with("127.0.0.1", ':'));
    CHECK(udp < 0, "socket address is read by length (bind=%lld, want rejected)", (long long)udp);
    if (udp >= 0) close((int)udp);

    if (failures) {
        fprintf(stderr, "process_spawn_value_counted_text_selfcheck: %d failure(s)\n", failures);
        return 1;
    }
    puts("process_spawn_value_counted_text_selfcheck: PASS");
    return 0;
}
#endif

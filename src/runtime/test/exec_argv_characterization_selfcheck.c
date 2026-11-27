/* Characterization selfcheck for fork/exec argv construction:
 *   rt_process_spawn_async / rt_process_spawn_guarded  (runtime_legacy_core.c)
 *   rt_process_spawn_session                           (runtime_process_tree.c)
 * Pins argv contents, argument gates, exec-failure reporting, exit-status
 * propagation and the fd-limit path, so a shared argv helper can be proven
 * behaviour-preserving. Build: see scripts/check/check-linux-dedup-characterization.shs. */
#define _GNU_SOURCE
#include "linux_char_harness.h"
#include "runtime_process_tree.h"

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>

int64_t rt_process_spawn_async(const char* cmd, const char** args, int64_t arg_count);
int64_t rt_process_spawn_guarded(const char* cmd, const char** args, int64_t arg_count);

/* runtime_legacy_core.c references these from the full runtime; the spawn
 * entry points under test never call them. */
void* rt_array_new(void) { return 0; }
void* rt_array_push(void) { return 0; }
int64_t rt_heap_live_bytes(void) { return 0; }
int64_t rt_heap_peak_bytes(void) { return 0; }
void* rt_string_new(void) { return 0; }
int64_t rt_text_slice_audit_level(void) { return 0; }
void rt_text_slice_audit_note(void) {}
int64_t rt_time_now_monotonic_ms(void) { return char_now_ms(); }
int64_t rt_value_bool(void) { return 0; }

static char g_out[4096];

/* Child prints "$0|$1|...|" into g_out. */
static const char* SCRIPT = "f=$0; for a in \"$@\"; do printf '%s|' \"$a\"; done > \"$f\"";

static int exit_code(int64_t pid) {
    int st = 0;
    if (waitpid((pid_t)pid, &st, 0) != (pid_t)pid) return -1000;
    if (WIFEXITED(st)) return WEXITSTATUS(st);
    if (WIFSIGNALED(st)) return -WTERMSIG(st);
    return -999;
}

static int slurp(char* buf, size_t cap) {
    int fd = open(g_out, O_RDONLY);
    if (fd < 0) return -1;
    ssize_t n = read(fd, buf, cap - 1);
    close(fd);
    unlink(g_out);
    if (n < 0) return -1;
    buf[n] = 0;
    return (int)n;
}

typedef int64_t (*spawn_fn)(const char*, const char**, int64_t);

static void check_argv_roundtrip(spawn_fn fn, const char* tag) {
    const char* args[] = { "-c", SCRIPT, g_out, "a", "b c", "", "d'e" };
    int64_t pid = fn("/bin/sh", args, 7);
    CHECK(pid > 0);
    CHECK(exit_code(pid) == 0);
    char buf[256];
    CHECK(slurp(buf, sizeof buf) > 0);
    if (strcmp(buf, "a|b c||d'e|") != 0) fprintf(stderr, "%s argv: [%s]\n", tag, buf);
    CHECK(strcmp(buf, "a|b c||d'e|") == 0);
}

static void check_argv_many(spawn_fn fn) {
    enum { N = 100 };
    const char* args[N + 3];
    char store[N][8];
    args[0] = "-c"; args[1] = SCRIPT; args[2] = g_out;
    for (int i = 0; i < N; i++) { snprintf(store[i], sizeof store[i], "%d", i); args[i + 3] = store[i]; }
    int64_t pid = fn("/bin/sh", args, N + 3);
    CHECK(pid > 0);
    CHECK(exit_code(pid) == 0);
    char buf[2048];
    CHECK(slurp(buf, sizeof buf) > 0);
    int bars = 0;
    for (char* p = buf; *p; p++) bars += (*p == '|');
    CHECK(bars == N);
    CHECK(strncmp(buf, "0|1|2|", 6) == 0);
    CHECK(strstr(buf, "|99|") != NULL);
}

static void check_zero_args(spawn_fn fn) {
    int64_t pid = fn("/bin/true", NULL, 0);
    CHECK(pid > 0);
    CHECK(exit_code(pid) == 0);
}

static void check_exec_failure_127(spawn_fn fn) {
    int64_t pid = fn("/nonexistent/simple-char-cmd", NULL, 0);
    CHECK(pid > 0);
    CHECK(exit_code(pid) == 127);
}

static void check_exit_status(spawn_fn fn) {
    const char* args[] = { "-c", "exit 7" };
    int64_t pid = fn("/bin/sh", args, 2);
    CHECK(pid > 0);
    CHECK(exit_code(pid) == 7);
}

static void t_async(void) {
    const char* one[] = { "x" };
    const char* withnull[] = { "x", NULL };
    CHECK(rt_process_spawn_async(NULL, one, 1) == -1);
    CHECK(rt_process_spawn_async("", one, 1) == -1);
    CHECK(rt_process_spawn_async("/bin/true", one, -1) == -1);
    CHECK(rt_process_spawn_async("/bin/true", NULL, 1) == -1);
    CHECK(rt_process_spawn_async("/bin/true", withnull, 2) == -1);
    CHECK(rt_process_spawn_async("/bin/true", one, 32769) == -1); /* gate before deref */
    check_zero_args(rt_process_spawn_async);
    check_argv_roundtrip(rt_process_spawn_async, "async");
    check_argv_many(rt_process_spawn_async);
    check_exec_failure_127(rt_process_spawn_async);
    check_exit_status(rt_process_spawn_async);
}

static void t_guarded(void) {
    const char* one[] = { "x" };
    CHECK(rt_process_spawn_guarded(NULL, one, 1) == -1);
    CHECK(rt_process_spawn_guarded("", one, 1) == -1);
    CHECK(rt_process_spawn_guarded("/bin/true", one, -1) == -1);   /* arg_count < 0 */
    CHECK(rt_process_spawn_guarded("/bin/true", one, INT64_MIN) == -1);
    CHECK(rt_process_spawn_guarded("/bin/true", NULL, 1) == -1);
    check_zero_args(rt_process_spawn_guarded);
    check_argv_roundtrip(rt_process_spawn_guarded, "guarded");
    check_argv_many(rt_process_spawn_guarded);
    check_exec_failure_127(rt_process_spawn_guarded);
    check_exit_status(rt_process_spawn_guarded);
}

static void t_session(void) {
    const char* one[] = { "x" };
    const char* withnull[] = { "x", NULL };
    CHECK(rt_process_spawn_session(NULL, one, 1) == -EINVAL);
    CHECK(rt_process_spawn_session("", one, 1) == -EINVAL);
    CHECK(rt_process_spawn_session("/bin/true", one, -1) == -EINVAL);
    CHECK(rt_process_spawn_session("/bin/true", NULL, 1) == -EINVAL);
    CHECK(rt_process_spawn_session("/bin/true", withnull, 2) == -EINVAL);
    CHECK(rt_process_spawn_session("/bin/true", one, (int64_t)INT32_MAX + 1) == -E2BIG);
    CHECK(rt_process_spawn_session("/nonexistent/simple-char-cmd", NULL, 0) == -ENOENT);
    CHECK(rt_process_spawn_session("/etc/passwd", NULL, 0) == -EACCES);
    check_zero_args(rt_process_spawn_session);
    check_argv_roundtrip(rt_process_spawn_session, "session");
    check_argv_many(rt_process_spawn_session);
    check_exit_status(rt_process_spawn_session);

    /* fd limit: no slot left for the CLOEXEC error pipe. */
    struct rlimit old; getrlimit(RLIMIT_NOFILE, &old);
    struct rlimit lim = old; lim.rlim_cur = char_first_free_fd();
    CHECK(setrlimit(RLIMIT_NOFILE, &lim) == 0);
    int64_t r = rt_process_spawn_session("/bin/true", NULL, 0);
    setrlimit(RLIMIT_NOFILE, &old);
    CHECK(r == -EMFILE);
    if (r > 0) (void)exit_code(r);
}

int main(void) {
    const char* dir = getenv("TMPDIR");
    snprintf(g_out, sizeof g_out, "%s/argv_char_%d.txt", dir ? dir : ".", (int)getpid());
    t_async();
    t_guarded();
    t_session();
    DONE("exec_argv_characterization");
}

/* Linux ProcessGroup retirement for Process Observation V4 (2026-11-12).
 * Profile HIR workers request the ProcessGroup descendant policy; until this
 * check the Linux owner neither advertised POV4_CAP_PROCESS_GROUP_RETIRE nor
 * could retire a group (owned_group_retire_ready had no Linux body), so every
 * HIR pool on Linux refused to start a worker.
 * Run from the repository root:
 *   cc -std=c11 -O0 -Wall -Wextra -pthread \
 *     src/runtime/test/runtime_process_group_retire_linux_selfcheck.c \
 *     src/runtime/runtime_process_tree.c -o /tmp/pov4-group-retire && /tmp/pov4-group-retire
 * A leader is started in its own process group with a grandchild; the leader
 * exits (unreaped, pinning the group id). Retirement must report "not ready"
 * while the grandchild lives, signal it, and report ready only after the
 * grandchild is gone. */
#if !defined(__linux__)
#include <stdio.h>
int main(void) { puts("runtime_process_group_retire_linux_selfcheck: SKIP (requires Linux)"); return 77; }
#else
#define _GNU_SOURCE
#include "../runtime.h"
#include <assert.h>
#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

SplArray* rt_array_new(int64_t capacity) {
    SplArray* a = calloc(1, sizeof(*a)); assert(a);
    a->cap = capacity > 0 ? capacity : 1;
    a->items = calloc((size_t)a->cap, sizeof(*a->items)); assert(a->items);
    return a;
}
int64_t rt_array_len(SplArray* a) { return a ? a->len : -1; }
int64_t rt_array_get(SplArray* a, int64_t i) {
    return a && i >= 0 && i < a->len ? a->items[i].as_int : 0;
}
int8_t rt_array_push(SplArray* a, int64_t value) {
    if (!a || a->len >= a->cap) return 0;
    a->items[a->len++].as_int = value; return 1;
}
int8_t rt_array_set(SplArray* a, int64_t i, int64_t value) {
    if (!a || i < 0 || i >= a->len) return 0;
    a->items[i].as_int = value; return 1;
}
int64_t rt_value_int(int64_t value) { return value; }
int64_t rt_value_as_int(int64_t value) { return value; }
int8_t rt_value_is_int(int64_t value) { (void)value; return 1; }
void* rt_alloc(int64_t size) { return size > 0 ? calloc(1, (size_t)size) : NULL; }
void rt_free(void* value) { free(value); }
int64_t rt_string_len(int64_t value) { (void)value; return -1; }
const uint8_t* rt_string_data(int64_t value) { (void)value; return NULL; }
int64_t rt_string_new(const uint8_t* bytes, uint64_t length) { (void)bytes; (void)length; return 1; }
void rt_array_free(SplArray* a) { if (a) { free(a->items); free(a); } }
int64_t rt_tuple_new(int64_t len) {
    SplArray* a = rt_array_new(len);
    for (int64_t i = 0; i < len; i++) assert(rt_array_push(a, 0));
    return (int64_t)(uintptr_t)a;
}
int8_t rt_tuple_set(int64_t tuple, int64_t index, int64_t value) {
    return rt_array_set((SplArray*)(uintptr_t)tuple, index, value);
}
int64_t rt_free_deep(int64_t value) { (void)value; return 1; }
int64_t rt_array_bytes_validate(int64_t value) {
    SplArray* a = (SplArray*)(uintptr_t)value;
    if (!a) return -1;
    for (int64_t i = 0; i < a->len; i++)
        if (rt_array_get(a, i) < 0 || rt_array_get(a, i) > 255) return -1;
    return a->len;
}
int64_t rt_array_bytes_copy_checked(int64_t value, uint8_t* out, int64_t cap) {
    int64_t n = rt_array_bytes_validate(value); if (n < 0 || n > cap) return -1;
    SplArray* a = (SplArray*)(uintptr_t)value;
    for (int64_t i = 0; i < n; i++) out[i] = (uint8_t)rt_array_get(a, i);
    return n;
}
int64_t rt_process_acquire_pinned_executable(int64_t token) { (void)token; errno = ESTALE; return -1; }
int rt_process_close_pinned_executable_owned_value(int64_t token) { (void)token; return 0; }
SplArray* rt_process_pinned_executable_sha256_value(int64_t token) { (void)token; return NULL; }
/* Group stream owners are not exercised here (link stubs only). */
int rt_process_stream_claim_launch_v2(int64_t a, const char* b, int64_t c, const char* d, int64_t e, int* f, int* g, int* h) {
    (void)a; (void)b; (void)c; (void)d; (void)e; (void)f; (void)g; (void)h; return ENOTSUP; }
int rt_process_stream_launch_not_started_v2(int64_t a, const char* b, int64_t c, const char* d, int64_t e) {
    (void)a; (void)b; (void)c; (void)d; (void)e; return ENOTSUP; }
int rt_process_stream_publish_broker_v2(int64_t a, const char* b, int64_t c, const char* d, int64_t e, int64_t f) {
    (void)a; (void)b; (void)c; (void)d; (void)e; (void)f; return ENOTSUP; }
int simple_local_unix_origin_v1(void) { return 0; }
#define RT_OWNED_EXTERNAL_PIN 1 /* This harness stubs the executable pin. */
#include "../runtime_process_owned.c"

static int failures = 0, checks = 0;
#define CHECK(cond, what) do { checks++; if (!(cond)) { fprintf(stderr, "FAIL: %s\n", what); failures++; } } while (0)

static int pid_runs(pid_t pid) {
    char path[64], line[512]; snprintf(path, sizeof(path), "/proc/%d/stat", (int)pid);
    FILE* f = fopen(path, "r"); if (!f) return 0;
    size_t n = fread(line, 1, sizeof(line) - 1, f); fclose(f); line[n] = 0;
    char* p = strrchr(line, ')'); return p && p[1] == ' ' && p[2] != 'Z' && p[2] != 'X';
}

static void sleep_ms(long ms) {
    struct timespec t = {ms / 1000, (ms % 1000) * 1000000L};
    while (nanosleep(&t, &t) != 0 && errno == EINTR) {}
}

int main(void) {
    SplArray* caps = rt_process_observation_v4_capabilities_value();
    int64_t bits = rt_array_get(caps, 3);
    CHECK((bits & POV4_CAP_PROCESS_GROUP_RETIRE) != 0,
          "Linux advertises POV4_CAP_PROCESS_GROUP_RETIRE when /proc is readable");

    RtOwnedSlot leader_only; memset(&leader_only, 0, sizeof(leader_only));
    CHECK(owned_group_retire_ready(&leader_only) == 1, "a leader-only slot is always ready");

    int report[2]; assert(pipe(report) == 0);
    pid_t leader = fork(); assert(leader >= 0);
    if (leader == 0) {
        (void)setpgid(0, 0);
        pid_t grandchild = fork();
        if (grandchild == 0) { close(report[0]); close(report[1]); for (;;) pause(); }
        ssize_t w = write(report[1], &grandchild, sizeof(grandchild)); (void)w;
        _exit(0);
    }
    (void)setpgid(leader, leader);
    close(report[1]);
    pid_t grandchild = -1;
    assert(read(report[0], &grandchild, sizeof(grandchild)) == (ssize_t)sizeof(grandchild));
    close(report[0]);
    siginfo_t info; memset(&info, 0, sizeof(info));
    assert(waitid(P_PID, (id_t)leader, &info, WEXITED | WNOWAIT) == 0);  /* exited, unreaped */
    CHECK(pid_runs(grandchild), "grandchild is alive before retirement");

    RtOwnedSlot slot; memset(&slot, 0, sizeof(slot));
    slot.pid = leader; slot.pgid = leader; slot.pidfd = -1; slot.group_retire = 1;
    slot.unlimited_cleanup_budget_ns = 5000000000LL;  /* the HIR owner asks 4.75 s */
    CHECK(owned_group_retire_ready(&slot) == 0, "not ready while a group member lives");
    int ready = 0;
    for (int attempt = 0; attempt < 200 && !ready; attempt++) {
        sleep_ms(10);
        ready = owned_group_retire_ready(&slot);
    }
    CHECK(ready == 1, "ready once the surviving member was retired");
    CHECK(!pid_runs(grandchild), "grandchild no longer runs when ready");
    CHECK(slot.group_incomplete == 0, "retired by an empty-group sample, not by the cleanup deadline");
    if (!ready) (void)kill(grandchild, SIGKILL);  /* never leave the fixture running */
    int status = 0;
    CHECK(waitpid(leader, &status, 0) == leader, "leader is reaped after retirement");

    if (failures) { fprintf(stderr, "runtime_process_group_retire_linux_selfcheck: %d failure(s)\n", failures); return 1; }
    printf("runtime_process_group_retire_linux_selfcheck: PASS (%d checks)\n", checks);
    return 0;
}
#endif

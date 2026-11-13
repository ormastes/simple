/* Linux ProcessGroup retirement for Process Observation V4 (2026-11-12).
 * Profile HIR workers request the ProcessGroup descendant policy; until this
 * check the Linux owner neither advertised POV4_CAP_PROCESS_GROUP_RETIRE nor
 * could retire a group (owned_group_retire_ready had no Linux body), so every
 * HIR pool on Linux refused to start a worker.
 * Run from the repository root (clang only, never GCC):
 *   clang -std=c11 -O0 -Wall -Wextra -pthread \
 *     src/runtime/test/runtime_process_group_retire_linux_selfcheck.c \
 *     src/runtime/runtime_process_tree.c -o /tmp/pov4-group-retire && /tmp/pov4-group-retire
 * The fault-injection build adds /proc, kill and clock failures through linker
 * wraps (test-only interposition; production code has no hooks for them):
 *   clang ... -DGR_FAULT_WRAP -Wl,--wrap=opendir,--wrap=readdir,--wrap=open \
 *     -Wl,--wrap=read,--wrap=kill,--wrap=clock_gettime,--wrap=waitid,--wrap=getpgrp ...
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
#include <fcntl.h>
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
/* Pin 77 is this selfcheck binary, so the end-to-end case can start a real
 * child through the V4 owner; every other token is stale. */
#define GR_EXEC_PIN 77
static uint8_t gr_exec_digest[32];
int64_t rt_process_acquire_pinned_executable(int64_t token) {
    if (token != GR_EXEC_PIN) { errno = ESTALE; return -1; }
    return open("/proc/self/exe", O_RDONLY | O_CLOEXEC);
}
int rt_process_close_pinned_executable_owned_value(int64_t token) { (void)token; return 0; }
SplArray* rt_process_pinned_executable_sha256_value(int64_t token) {
    if (token != GR_EXEC_PIN) return NULL;
    SplArray* a = rt_array_new(32);
    for (int i = 0; i < 32; i++) assert(rt_array_push(a, gr_exec_digest[i]));
    return a;
}
/* Group stream owners are not exercised here (link stubs only). */
int rt_process_stream_claim_launch_v2(int64_t a, const char* b, int64_t c, const char* d, int64_t e, int* f, int* g, int* h) {
    (void)a; (void)b; (void)c; (void)d; (void)e; (void)f; (void)g; (void)h; return ENOTSUP; }
int rt_process_stream_launch_not_started_v2(int64_t a, const char* b, int64_t c, const char* d, int64_t e) {
    (void)a; (void)b; (void)c; (void)d; (void)e; return ENOTSUP; }
int rt_process_stream_publish_broker_v2(int64_t a, const char* b, int64_t c, const char* d, int64_t e, int64_t f) {
    (void)a; (void)b; (void)c; (void)d; (void)e; (void)f; return ENOTSUP; }
int simple_local_unix_origin_v1(void) { return 0; }
#define RT_OWNED_EXTERNAL_PIN 1 /* This harness stubs the executable pin. */
#ifdef GR_FAULT_WRAP
#define RT_PROCESS_OBSERVATION_V4_TESTING 1 /* existing reconcile EINTR hook */
#endif
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



/* Exited, unreaped leader of a fresh group; *member is a live group member
 * (self-expiring) or -1 when `with_member` is 0. */
static pid_t gr_spawn_group(int with_member, pid_t* member) {
    int report[2]; assert(pipe(report) == 0);
    pid_t leader = fork(); assert(leader >= 0);
    if (leader == 0) {
        (void)setpgid(0, 0);
        pid_t m = -1;
        if (with_member) {
            m = fork();
            if (m == 0) { close(report[0]); close(report[1]); alarm(30); for (;;) pause(); }
        }
        ssize_t w = write(report[1], &m, sizeof(m)); (void)w;
        _exit(0);
    }
    (void)setpgid(leader, leader);
    close(report[1]);
    assert(read(report[0], member, sizeof(*member)) == (ssize_t)sizeof(*member));
    close(report[0]);
    siginfo_t info; memset(&info, 0, sizeof(info));
    assert(waitid(P_PID, (id_t)leader, &info, WEXITED | WNOWAIT) == 0);
    return leader;
}

/* The cleanup deadline is the only way out while a member survives, and it
 * must never claim an empty tree (pov4_snapshot then reports tree_empty=0). */
static void check_retire_deadline_and_sample_recovery(void) {
    pid_t member = -1;
    pid_t leader = gr_spawn_group(1, &member);
    RtOwnedSlot slot; memset(&slot, 0, sizeof(slot));
    slot.pid = leader; slot.pgid = leader; slot.pidfd = -1; slot.group_retire = 1;
    slot.kill_deadline_ns = 1; slot.cleanup_deadline_ns = 1;  /* already expired */
    CHECK(owned_group_retire_ready(&slot) == 1, "an expired cleanup deadline releases the leader");
    CHECK(slot.group_incomplete == 1, "an expired cleanup deadline marks the group incomplete");
    CHECK(slot.runtime_error == ETIMEDOUT, "an expired cleanup deadline records ETIMEDOUT");
    CHECK(pid_runs(member), "the deadline path does not pretend the member was retired");

    RtOwnedSlot kept; memset(&kept, 0, sizeof(kept));
    kept.pid = leader; kept.pgid = leader; kept.pidfd = -1; kept.group_retire = 1;
    kept.kill_deadline_ns = 1; kept.cleanup_deadline_ns = 1; kept.runtime_error = EIO;
    CHECK(owned_group_retire_ready(&kept) == 1 && kept.runtime_error == EIO,
          "the deadline keeps an earlier non-sampling runtime error");
    (void)kill(member, SIGKILL);
    int status = 0;
    CHECK(waitpid(leader, &status, 0) == leader, "deadline fixture leader is reaped");

    leader = gr_spawn_group(0, &member);
    RtOwnedSlot recovered; memset(&recovered, 0, sizeof(recovered));
    recovered.pid = leader; recovered.pgid = leader; recovered.pidfd = -1; recovered.group_retire = 1;
    recovered.unlimited_cleanup_budget_ns = 5000000000LL;
    recovered.group_sample_error = EIO; recovered.runtime_error = EIO;
    CHECK(owned_group_retire_ready(&recovered) == 1, "an empty group is ready at once");
    CHECK(recovered.runtime_error == 0 && recovered.group_sample_error == 0,
          "a clean sample clears the earlier sampling error");
    CHECK(recovered.group_incomplete == 0, "an empty-sample retirement is complete");
    CHECK(waitpid(leader, &status, 0) == leader, "recovery fixture leader is reaped");
}

/* --- End-to-end: the V4 start path must carry the requested policy --------
 * The checks above hand-build a slot with group_retire = 1, so they never
 * proved that a ProcessGroup REQUEST produces a group-retiring slot. Run-26
 * Stage 2 (2026-11-13): on Linux it did not -- pov4_start_exact never copied
 * the policy (only the Darwin twin did), so the frozen receipt of every
 * cleanly exited HIR worker said tree_control=0 tree_empty=0 and
 * worker_hir_owner_v1 refused it as an invalid retirement receipt. */
static void gr_put_u64(SplArray* a, uint64_t v) {
    for (int i = 0; i < 8; i++) assert(rt_array_push(a, (int64_t)((v >> (8 * i)) & 255)));
}
static void gr_put_bytes(SplArray* a, const uint8_t* b, size_t n) {
    for (size_t i = 0; i < n; i++) assert(rt_array_push(a, b[i]));
}
static void gr_put_text(SplArray* a, const char* t) {
    size_t n = strlen(t); gr_put_u64(a, n); gr_put_bytes(a, (const uint8_t*)t, n);
}
/* Same canonical POV4REQ layout as runtime_process_observation_v4_selfcheck. */
static SplArray* gr_request(const char* cwd, int64_t cwd_pin, const uint8_t cwd_digest[32],
                            const char* child_arg, uint64_t policy) {
    SplArray* a = rt_array_new(1024);
    const uint8_t magic[8] = {'P','O','V','4','R','E','Q',0}; gr_put_bytes(a, magic, 8);
    gr_put_u64(a, 1); gr_put_u64(a, 1); gr_put_u64(a, 20000000000ULL);
    gr_put_u64(a, 100000000ULL); gr_put_u64(a, 4750000000ULL);
    gr_put_u64(a, 1024); gr_put_u64(a, 1024); gr_put_u64(a, 0);
    gr_put_u64(a, 1); gr_put_u64(a, policy); gr_put_u64(a, 1000000); gr_put_u64(a, GR_EXEC_PIN);
    gr_put_bytes(a, gr_exec_digest, 32); gr_put_text(a, cwd); gr_put_text(a, cwd);
    gr_put_u64(a, (uint64_t)cwd_pin); gr_put_bytes(a, cwd_digest, 32);
    gr_put_u64(a, 2); gr_put_text(a, "gr-selfcheck"); gr_put_text(a, child_arg);
    gr_put_u64(a, 0);
    return a;
}
static SplArray* gr_item(SplArray* tuple, int i) { return (SplArray*)(uintptr_t)rt_array_get(tuple, i); }

/* Starts `child_arg` under `policy`, collects the frozen receipt, acks it. */
static SplArray* gr_run(const char* child_arg, uint64_t policy, pid_t* grandchild_out) {
    char cwd[4096]; assert(realpath(".", cwd));
    int64_t cwd_pin = rt_process_observation_v4_pin_cwd_value(cwd, strlen(cwd)); assert(cwd_pin > 0);
    uint8_t cwd_digest[32];
    assert(rt_array_bytes_copy_checked((int64_t)(uintptr_t)
        rt_process_observation_v4_cwd_digest_value(cwd_pin), cwd_digest, 32) == 32);
    SplArray* started = rt_process_observation_v4_start_pinned_value(GR_EXEC_PIN, cwd_pin,
        gr_request(cwd, cwd_pin, cwd_digest, child_arg, policy));
    SplArray* w = gr_item(started, 3);
    CHECK(rt_array_get(w, POV4_STATUS) == POV4_STATUS_RUNNING, "V4 start admits the request");
    if (rt_array_get(w, POV4_STATUS) != POV4_STATUS_RUNNING) return w;
    SplArray* ticket = rt_array_new(5); assert(rt_array_push(ticket, 4));
    for (int i = 4; i <= 7; i++) assert(rt_array_push(ticket, rt_array_get(w, i)));
    SplArray* frozen = NULL;
    for (int i = 0; i < 400; i++) {
        frozen = rt_process_observation_v4_collect_value(ticket, 50000000);
        w = gr_item(frozen, 3);
        if (rt_array_get(w, POV4_PACKET_KIND) == POV4_KIND_FROZEN) break;
    }
    CHECK(rt_array_get(w, POV4_PACKET_KIND) == POV4_KIND_FROZEN, "the owner freezes a terminal receipt");
    SplArray* out = gr_item(frozen, 0);
    long parsed = 0;
    for (int64_t i = 0; i < rt_array_len(out); i++) {
        int64_t c = rt_array_get(out, i);
        if (c >= '0' && c <= '9') parsed = parsed * 10 + (c - '0');
    }
    if (grandchild_out) *grandchild_out = (pid_t)parsed;
    (void)rt_process_observation_v4_ack_collect_value(ticket, gr_item(frozen, 2));
    assert(rt_process_observation_v4_close_cwd_value(cwd_pin) == 1);
    return w;
}

static void check_v4_start_carries_policy(void) {
    for (int i = 0; i < 32; i++) gr_exec_digest[i] = (uint8_t)(i + 1);
    SplArray* w = gr_run("--gr-exit0", POV4_DESCENDANT_PROCESS_GROUP, NULL);
    CHECK(rt_array_get(w, POV4_EXIT_CODE) == 0, "group leader exits 0");
    CHECK(rt_array_get(w, POV4_LEADER_REAPED) == 1, "group leader is reaped");
    CHECK(rt_array_get(w, POV4_TREE_CONTROL_AVAILABLE) == 1,
          "a ProcessGroup request yields a group-retiring slot (tree control)");
    CHECK(rt_array_get(w, POV4_TREE_EMPTY) == 1, "a clean group exit reports tree_empty");
    CHECK(rt_array_get(w, POV4_TREE_EMPTY_NS) >= 0, "tree_empty carries its timestamp");

    pid_t grandchild = 0;
    w = gr_run("--gr-linger", POV4_DESCENDANT_PROCESS_GROUP, &grandchild);
    CHECK(grandchild > 0, "lingering child reported its grandchild");
    CHECK(rt_array_get(w, POV4_TREE_CONTROL_AVAILABLE) == 1, "lingering group: tree control");
    CHECK(rt_array_get(w, POV4_TREE_EMPTY) == 1, "lingering group member is retired before tree_empty");
    CHECK(grandchild <= 0 || !pid_runs(grandchild), "the lingering grandchild no longer runs");
    if (grandchild > 0 && pid_runs(grandchild)) (void)kill(grandchild, SIGKILL);

    /* Unchanged: LeaderOnly never claims tree authority. */
    w = gr_run("--gr-exit0", POV4_DESCENDANT_LEADER, NULL);
    CHECK(rt_array_get(w, POV4_LEADER_REAPED) == 1, "leader-only child is reaped");
    CHECK(rt_array_get(w, POV4_TREE_CONTROL_AVAILABLE) == 0, "leader-only has no tree control");
    CHECK(rt_array_get(w, POV4_TREE_EMPTY) == 0, "leader-only never reports tree_empty");
}

#ifdef GR_FAULT_WRAP
/* --- Test-only fault interposition (no production hooks) -------------------
 * Built only with -DGR_FAULT_WRAP and the linker wraps listed in the header.
 * Every fault is one-shot and targeted; otherwise each wrapper is the libc call. */
#include <dirent.h>
#include <stdarg.h>
DIR* __real_opendir(const char* path);
struct dirent* __real_readdir(DIR* dir);
int __real_open(const char* path, int flags, ...);
ssize_t __real_read(int fd, void* buf, size_t len);
int __real_kill(pid_t pid, int sig);
int __real_clock_gettime(clockid_t clock, struct timespec* ts);
int __real_waitid(idtype_t type, id_t id, siginfo_t* info, int options);
pid_t __real_getpgrp(void);

static int gr_opendir_errno = -1;   /* >= 0: the next opendir("/proc") fails with it */
static const char* gr_fake_entry;   /* emitted once as the first /proc entry */
static int gr_open_errno;           /* the next /proc/<pid>/stat opens fail with it */
static int gr_open_left = 1;        /* ... this many of them */
static char gr_read_text[128];      /* read mode 8: this stat line */
static int gr_waitid_errno;         /* the next waitid fails with it (EINTR: once, then real) */
static int gr_getpgrp_fake;         /* the next getpgrp returns this unused id */
static int gr_read_mode;            /* fault for the next opened /proc/<pid>/stat read */
static int gr_read_fd = -1;
static int gr_kill_errno;           /* the next kill(-pgid, ...) fails with it */
static int gr_clock_fail;           /* the next clock_gettime fails */

static int gr_proc_stat_path(const char* path) {
    return strncmp(path, "/proc/", 6) == 0 && path[6] >= '1' && path[6] <= '9' &&
           strstr(path, "/stat") != NULL;
}
DIR* __wrap_opendir(const char* path) {
    if (gr_opendir_errno >= 0 && strcmp(path, "/proc") == 0) {
        errno = gr_opendir_errno; gr_opendir_errno = -1; return NULL;
    }
    return __real_opendir(path);
}
struct dirent* __wrap_readdir(DIR* dir) {
    static struct dirent fake;
    if (gr_fake_entry) {
        memset(&fake, 0, sizeof(fake));
        snprintf(fake.d_name, sizeof(fake.d_name), "%s", gr_fake_entry);
        gr_fake_entry = NULL;
        return &fake;
    }
    return __real_readdir(dir);
}
int __wrap_open(const char* path, int flags, ...) {
    mode_t mode = 0;
    if (flags & O_CREAT) { va_list ap; va_start(ap, flags); mode = (mode_t)va_arg(ap, int); va_end(ap); }
    if (gr_open_errno && gr_proc_stat_path(path)) {
        errno = gr_open_errno;
        if (--gr_open_left <= 0) { gr_open_errno = 0; gr_open_left = 1; }
        return -1;
    }
    int fd = __real_open(path, flags, mode);
    if (fd >= 0 && gr_read_mode && gr_read_fd < 0 && gr_proc_stat_path(path)) gr_read_fd = fd;
    return fd;
}
ssize_t __wrap_read(int fd, void* buf, size_t len) {
    if (fd >= 0 && fd == gr_read_fd && gr_read_mode) {
        int mode = gr_read_mode; gr_read_mode = 0; gr_read_fd = -1;
        switch (mode) {
        case 1: errno = EIO; return -1;              /* real read error */
        case 2: errno = EINTR; return -1;             /* retried, then real */
        case 3: return 0;                             /* vanished: empty */
        case 4: errno = ESRCH; return -1;             /* exited mid-read */
        case 5: { const char t[] = "1 (no-close-paren"; size_t n = sizeof(t) - 1;
                  if (n > len) n = len; memcpy(buf, t, n); return (ssize_t)n; }
        case 6: { const char t[] = "1 (x) R notanumber"; size_t n = sizeof(t) - 1;
                  if (n > len) n = len; memcpy(buf, t, n); return (ssize_t)n; }
        case 7: errno = ENOENT; return -1;            /* reaped mid-read */
        case 8: { size_t n = strlen(gr_read_text); if (n > len) n = len;
                  memcpy(buf, gr_read_text, n); return (ssize_t)n; }
        default: break;
        }
    }
    return __real_read(fd, buf, len);
}
int __wrap_kill(pid_t pid, int sig) {
    if (gr_kill_errno && pid < 0) { errno = gr_kill_errno; gr_kill_errno = 0; return -1; }
    return __real_kill(pid, sig);
}
int __wrap_clock_gettime(clockid_t clock, struct timespec* ts) {
    if (gr_clock_fail) { gr_clock_fail = 0; errno = EINVAL; return -1; }
    return __real_clock_gettime(clock, ts);
}
int __wrap_waitid(idtype_t type, id_t id, siginfo_t* info, int options) {
    if (gr_waitid_errno) { errno = gr_waitid_errno; gr_waitid_errno = 0; return -1; }
    return __real_waitid(type, id, info, options);
}
pid_t __wrap_getpgrp(void) {
    if (gr_getpgrp_fake) { pid_t fake = gr_getpgrp_fake; gr_getpgrp_fake = 0; return fake; }
    return __real_getpgrp();
}
/* A stat line for pid 1 claiming membership of `group` in `state`. */
static void gr_stat_line(char state, pid_t group) {
    snprintf(gr_read_text, sizeof(gr_read_text), "1 (x) %c 0 %d", state, (int)group);
    gr_read_mode = 8;
}

static void check_group_live_faults(void) {
    size_t live = 0;
    gr_opendir_errno = EACCES;
    CHECK(owned_linux_group_live(getpgrp(), &live) == EACCES, "an unreadable /proc is a sampling failure");
    gr_opendir_errno = 0;
    CHECK(owned_linux_group_live(getpgrp(), &live) == EIO, "an opendir failure without errno is EIO");
    gr_open_errno = EACCES;
    CHECK(owned_linux_group_live(getpgrp(), &live) == EACCES, "an unreadable stat entry is a sampling failure");
    gr_open_errno = ENOENT; live = 0;
    CHECK(owned_linux_group_live(getpgrp(), &live) == 0 && live > 0, "a vanished stat entry is absence");
    gr_open_errno = ESRCH; live = 0;
    CHECK(owned_linux_group_live(getpgrp(), &live) == 0 && live > 0, "an exited stat entry is absence");
    gr_open_errno = EACCES; gr_open_left = 2;
    CHECK(owned_linux_group_live(getpgrp(), &live) == EACCES, "repeated open failures report one error");
    gr_read_mode = 7;
    CHECK(owned_linux_group_live(getpgrp(), &live) == 0, "a reaped process mid-read is absence");
    /* Dead or zombie members of the group are not live. */
    pid_t me = getpgrp();
    size_t base = 0; CHECK(owned_linux_group_live(me, &base) == 0, "baseline group sample");
    gr_stat_line('R', me); live = 0;
    CHECK(owned_linux_group_live(me, &live) == 0, "a forged running member is sampled");
    gr_stat_line('Z', me);
    CHECK(owned_linux_group_live(me, &live) == 0, "a zombie member is sampled");
    gr_stat_line('X', me);
    CHECK(owned_linux_group_live(me, &live) == 0, "a dead (X) member is sampled");
    gr_stat_line('x', me);
    CHECK(owned_linux_group_live(me, &live) == 0, "a dead (x) member is sampled");
    gr_read_mode = 1;
    CHECK(owned_linux_group_live(getpgrp(), &live) == EIO, "a stat read error is a sampling failure");
    gr_read_mode = 2; live = 0;
    CHECK(owned_linux_group_live(getpgrp(), &live) == 0 && live > 0, "an interrupted stat read is retried");
    gr_read_mode = 3;
    CHECK(owned_linux_group_live(getpgrp(), &live) == 0, "an empty stat read is absence");
    gr_read_mode = 4;
    CHECK(owned_linux_group_live(getpgrp(), &live) == 0, "an exited process mid-read is absence");
    gr_read_mode = 5;
    CHECK(owned_linux_group_live(getpgrp(), &live) == EPROTO, "a stat line without ')' is EPROTO");
    gr_read_mode = 6;
    CHECK(owned_linux_group_live(getpgrp(), &live) == EPROTO, "unparsable stat fields are EPROTO");
    /* The first failure wins over a later one. */
    gr_open_errno = EACCES; gr_read_mode = 5;
    CHECK(owned_linux_group_live(getpgrp(), &live) == EACCES, "the first sampling failure is kept (EPROTO later)");
    gr_open_errno = EACCES; gr_read_mode = 6;
    CHECK(owned_linux_group_live(getpgrp(), &live) == EACCES, "the first sampling failure is kept (fields later)");
    gr_open_errno = EACCES; gr_read_mode = 1;
    CHECK(owned_linux_group_live(getpgrp(), &live) == EACCES, "the first sampling failure is kept (read later)");
    /* Names that are not pids, or too long for the path buffer, are skipped. */
    gr_fake_entry = "1.5"; live = 0;
    CHECK(owned_linux_group_live(getpgrp(), &live) == 0 && live > 0, "a dotted entry is skipped");
    gr_fake_entry = "1x"; live = 0;
    CHECK(owned_linux_group_live(getpgrp(), &live) == 0 && live > 0, "a non-numeric entry is skipped");
    gr_fake_entry = "1234567890123456789012345678901234567890123456789012345678"; live = 0;
    CHECK(owned_linux_group_live(getpgrp(), &live) == 0 && live > 0, "an over-long entry is skipped");

    /* Fail closed: an unsampleable /proc neither advertises nor admits ProcessGroup. */
    gr_opendir_errno = EACCES;
    CHECK(owned_linux_group_retire_available() == 0, "unreadable /proc: ProcessGroup not available");
    gr_getpgrp_fake = 0x7ffffff0;
    CHECK(owned_linux_group_retire_available() == 0, "an empty own-group sample: ProcessGroup not available");
    gr_opendir_errno = EACCES;
    SplArray* caps = rt_process_observation_v4_capabilities_value();
    CHECK((rt_array_get(caps, 3) & POV4_CAP_PROCESS_GROUP_RETIRE) == 0,
          "unreadable /proc: ProcessGroup retirement not advertised");
}

static void check_retire_ready_faults(void) {
    pid_t member = -1;
    pid_t leader = gr_spawn_group(1, &member);
    RtOwnedSlot slot; memset(&slot, 0, sizeof(slot));
    slot.pid = leader; slot.pgid = leader; slot.pidfd = -1; slot.group_retire = 1;
    slot.unlimited_cleanup_budget_ns = 5000000000LL;

    gr_clock_fail = 1;
    CHECK(owned_group_retire_ready(&slot) == 0 && slot.clock_failed == 1,
          "a clock failure is never ready and is recorded");
    slot.clock_failed = 0;

    gr_opendir_errno = EACCES;
    CHECK(owned_group_retire_ready(&slot) == 0, "a sampling failure is not ready");
    CHECK(slot.runtime_error == EACCES && slot.group_sample_error == EACCES,
          "a sampling failure is recorded as the runtime error");
    slot.runtime_error = EIO; slot.group_sample_error = 0;
    gr_opendir_errno = EACCES;
    CHECK(owned_group_retire_ready(&slot) == 0 && slot.runtime_error == EIO && slot.group_sample_error == 0,
          "a sampling failure keeps an earlier runtime error");
    slot.runtime_error = 0;

    gr_kill_errno = EINVAL;
    CHECK(owned_group_retire_ready(&slot) == 0 && slot.runtime_error == EINVAL,
          "a failed group kill is recorded");
    CHECK(pid_runs(member), "the member survives a failed group kill");
    slot.runtime_error = 0;
    gr_kill_errno = EPERM;
    CHECK(owned_group_retire_ready(&slot) == 0 && slot.runtime_error == 0,
          "EPERM from the group kill is not a runtime error");
    gr_kill_errno = ESRCH;
    CHECK(owned_group_retire_ready(&slot) == 0 && slot.runtime_error == 0,
          "ESRCH from the group kill is not a runtime error");
    slot.runtime_error = ENOMEM;
    gr_kill_errno = EINVAL;
    CHECK(owned_group_retire_ready(&slot) == 0 && slot.runtime_error == ENOMEM,
          "a failed group kill keeps an earlier runtime error");
    slot.runtime_error = 0;

    /* A clean sample clears only its own sampling error. */
    slot.group_sample_error = EACCES; slot.runtime_error = EIO;
    (void)owned_group_retire_ready(&slot);
    CHECK(slot.runtime_error == EIO && slot.group_sample_error == 0,
          "a clean sample keeps an unrelated runtime error");
    slot.runtime_error = 0;
    /* No armed cleanup deadline (unstarted request): never the deadline exit. */
    RtOwnedSlot unarmed = slot;
    unarmed.request_started_ns = -1; unarmed.kill_deadline_ns = 0; unarmed.cleanup_deadline_ns = 0;
    (void)owned_group_retire_ready(&unarmed);  /* the member may already be gone */
    CHECK(unarmed.cleanup_deadline_ns == 0 && unarmed.group_incomplete == 0 &&
          unarmed.runtime_error != ETIMEDOUT, "an unarmed slot samples instead of timing out");
    /* At the deadline a sampling error is replaced by ETIMEDOUT. */
    RtOwnedSlot expired = slot;
    expired.kill_deadline_ns = 1; expired.cleanup_deadline_ns = 1;
    expired.runtime_error = EACCES; expired.group_sample_error = EACCES;
    CHECK(owned_group_retire_ready(&expired) == 1 && expired.runtime_error == ETIMEDOUT &&
          expired.group_incomplete == 1, "the deadline replaces a sampling error with ETIMEDOUT");

    int ready = 0;
    for (int i = 0; i < 200 && !ready; i++) { sleep_ms(10); ready = owned_group_retire_ready(&slot); }
    CHECK(ready == 1 && !pid_runs(member), "retirement completes after the injected faults");
    if (!ready) (void)kill(member, SIGKILL);
    int status = 0;
    CHECK(waitpid(leader, &status, 0) == leader, "fault fixture leader is reaped");
}

/* pov4_reconcile_gone_child_locked: ESRCH reconciliation of the owned child. */
static void gr_reconcile_slot(RtOwnedSlot* slot, pid_t pid, int group) {
    memset(slot, 0, sizeof(*slot));
    slot->pid = pid; slot->pgid = pid; slot->pidfd = -1; slot->group_retire = group;
    slot->request_started_ns = owned_now_ns();
    slot->unlimited_cleanup_budget_ns = 5000000000LL;
    slot->leader_waited_ns = -1; slot->tree_empty_ns = -1;
}
static void check_reconcile_gone_child(void) {
    RtOwnedSlot slot;
    int64_t far = owned_now_ns() + 5000000000LL;

    /* Group leader still running: never consumed. */
    int hold[2]; assert(pipe(hold) == 0);
    pid_t running = fork(); assert(running >= 0);
    if (running == 0) { close(hold[1]); char c; (void)read(hold[0], &c, 1); _exit(0); }
    (void)setpgid(running, running);
    close(hold[0]);
    gr_reconcile_slot(&slot, running, 1);
    pov4_reconcile_gone_child_locked(&slot, running, far);
    CHECK(slot.reaped == 0, "a running group leader is not reaped");
    gr_waitid_errno = EINTR;
    pov4_reconcile_gone_child_locked(&slot, running, far);
    CHECK(slot.reaped == 0, "an interrupted group probe is retried");
    gr_waitid_errno = ECHILD;
    pov4_reconcile_gone_child_locked(&slot, running, far);
    CHECK(slot.reaped == 0, "a failed group probe never reaps");
    /* Leader-only and still running: the nonblocking wait returns at once. */
    gr_reconcile_slot(&slot, running, 0);
    pov4_reconcile_gone_child_locked(&slot, running, far);
    CHECK(slot.reaped == 0, "a running leader-only child is not reaped");
    close(hold[1]);
    int status = 0; (void)waitpid(running, &status, 0);

    /* Group leader exited while a member lives: not reaped until retired. */
    pid_t member = -1;
    pid_t leader = gr_spawn_group(1, &member);
    gr_reconcile_slot(&slot, leader, 1);
    pov4_reconcile_gone_child_locked(&slot, leader, far);
    CHECK(slot.reaped == 0, "an exited leader with a live member is not reaped");
    for (int i = 0; i < 200 && !slot.reaped; i++) {
        sleep_ms(10);
        pov4_reconcile_gone_child_locked(&slot, leader, far);
    }
    CHECK(slot.reaped == 1 && slot.tree_empty_ns >= 0 && slot.tree_empty_ns == slot.leader_waited_ns,
          "a retired group leader is reaped with tree_empty");
    CHECK(!pid_runs(member), "the member is gone before the leader is reaped");
    if (!slot.reaped) { (void)kill(member, SIGKILL); (void)waitpid(leader, &status, 0); }

    /* Leader-only, exited; EINTR retries are counted, then it is reaped. */
    leader = gr_spawn_group(0, &member);
    gr_reconcile_slot(&slot, leader, 0);
    rt_process_observation_v4_test_force_reconcile_eintr(2);
    pov4_reconcile_gone_child_locked(&slot, leader, far);
    CHECK(slot.reaped == 1 && slot.eintr_retries == 2, "EINTR is retried and counted");
    CHECK(slot.tree_empty_ns == -1, "a leader-only reap never claims tree_empty");
    CHECK(slot.drain_deadline_ms > 0, "the drain deadline follows the cleanup deadline");

    /* EINTR past the deadline stops without reaping. */
    leader = gr_spawn_group(0, &member);
    gr_reconcile_slot(&slot, leader, 0);
    rt_process_observation_v4_test_force_reconcile_eintr(1);
    pov4_reconcile_gone_child_locked(&slot, leader, 1);
    CHECK(slot.reaped == 0 && slot.eintr_retries == 1, "EINTR past the deadline stops");
    rt_process_observation_v4_test_force_reconcile_eintr(0);
    /* An armed execution deadline keeps the caller's drain deadline. */
    slot.execution_deadline_ns = far;
    pov4_reconcile_gone_child_locked(&slot, leader, far);
    CHECK(slot.reaped == 1 && slot.drain_deadline_ms == (far + 999999) / 1000000,
          "an execution deadline keeps the caller's drain deadline");

    /* An unbounded EINTR storm is cut off after 1000 turns. */
    leader = gr_spawn_group(0, &member);
    gr_reconcile_slot(&slot, leader, 0);
    rt_process_observation_v4_test_force_reconcile_eintr(1000);
    pov4_reconcile_gone_child_locked(&slot, leader, far);
    CHECK(slot.reaped == 0 && slot.eintr_retries == 1000, "an EINTR storm is bounded");
    rt_process_observation_v4_test_force_reconcile_eintr(0);
    /* A clock failure inside the EINTR loop stops it. */
    rt_process_observation_v4_test_force_reconcile_eintr(1);
    gr_clock_fail = 1;
    pov4_reconcile_gone_child_locked(&slot, leader, far);
    CHECK(slot.reaped == 0, "a clock failure in the EINTR loop stops it");
    rt_process_observation_v4_test_force_reconcile_eintr(0);
    /* No deadline with an execution deadline armed: no drain deadline. */
    slot.execution_deadline_ns = far;
    pov4_reconcile_gone_child_locked(&slot, leader, -1);
    CHECK(slot.reaped == 1 && slot.drain_deadline_ms == -1, "a negative deadline leaves no drain deadline");
    /* Not our child: the wait fails and nothing is claimed. */
    gr_reconcile_slot(&slot, 1, 0);
    pov4_reconcile_gone_child_locked(&slot, 1, far);
    CHECK(slot.reaped == 0, "a non-child is never reaped");

    /* A clock failure at reap is recorded. */
    leader = gr_spawn_group(0, &member);
    gr_reconcile_slot(&slot, leader, 0);
    gr_clock_fail = 1;
    pov4_reconcile_gone_child_locked(&slot, leader, far);
    CHECK(slot.reaped == 1 && slot.clock_failed == 1 && slot.finished_ms == -1,
          "a clock failure at reap is recorded");
}
#endif

int main(int argc, char** argv) {
    if (argc == 2 && strcmp(argv[1], "--gr-exit0") == 0) return 0;
    if (argc == 2 && strcmp(argv[1], "--gr-linger") == 0) {
        pid_t grandchild = fork();
        if (grandchild == 0) { alarm(30); for (;;) pause(); }  /* self-expiring fixture */
        printf("%d\n", (int)grandchild); fflush(stdout);
        return 0;
    }
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

    check_retire_deadline_and_sample_recovery();
    check_v4_start_carries_policy();
#ifdef GR_FAULT_WRAP
    check_group_live_faults();
    check_retire_ready_faults();
    check_reconcile_gone_child();
#endif

    if (failures) { fprintf(stderr, "runtime_process_group_retire_linux_selfcheck: %d failure(s)\n", failures); return 1; }
    printf("runtime_process_group_retire_linux_selfcheck: PASS (%d checks)\n", checks);
    return 0;
}
#endif

/* Run from the repository root (macOS):
 * cc -std=c11 -O0 -Wall -Wextra -Werror -pthread src/runtime/test/runtime_process_observation_v4_darwin_live_selfcheck.c src/runtime/runtime_process_tree.c -o /tmp/pov4-darwin-live
 * /tmp/pov4-darwin-live
 *
 * Live contract check for the partial Darwin observation V4 owner: a private
 * 0700/0500 snapshot of this binary is launched START_SUSPENDED, proven by its
 * main-image vnode and digest, resumed, observed, reaped and acknowledged.
 * Covers LeaderOnly and ProcessGroup retirement, deadline TERM/KILL, memory-cap
 * refusal, snapshot tamper refusal, startup-cleanup authority, and descriptor
 * hygiene. The executable pin itself is runtime_process.c; this harness
 * substitutes an equivalent snapshot so the owner is tested in isolation. */
#if !defined(__APPLE__)
#include <stdio.h>
int main(void) { puts("runtime_process_observation_v4_darwin_live_selfcheck: SKIP (requires macOS)"); return 77; }
#else
#define _DARWIN_C_SOURCE
#define RT_PROCESS_OBSERVATION_V4_TESTING 1
#define RT_OWNED_EXTERNAL_PIN 1 /* This harness stubs the executable pin. */
#include "../runtime.h"
#include <assert.h>
#include <CommonCrypto/CommonDigest.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <mach-o/dyld.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
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

/* Test snapshot standing in for the runtime_process.c Darwin pin. The digest
 * answer is the value captured at pin time, so a later rewrite exercises the
 * owner's own re-hash rather than this stub. */
#define TEST_PIN 77
static char snapshot_dir[PATH_MAX], snapshot_path[PATH_MAX];
static int snapshot_fd = -1, acquisitions;
static uint8_t snapshot_digest[32];
int64_t rt_process_acquire_pinned_executable(int64_t handle) {
    acquisitions++;
    if (handle != TEST_PIN || snapshot_fd < 0) { errno = ESTALE; return -1; }
    return fcntl(snapshot_fd, F_DUPFD_CLOEXEC, 3);
}
int rt_process_close_pinned_executable_owned_value(int64_t handle) { (void)handle; return 0; }
SplArray* rt_process_pinned_executable_sha256_value(int64_t handle) {
    if (handle != TEST_PIN) return NULL;
    SplArray* a = rt_array_new(32);
    for (int i = 0; i < 32; i++) assert(rt_array_push(a, snapshot_digest[i]));
    return a;
}
#include "../runtime_process_owned.c"

static void hash_fd(int fd, uint8_t digest[32]) {
    CC_SHA256_CTX context; uint8_t buffer[65536]; off_t offset = 0;
    CC_SHA256_Init(&context);
    for (;;) {
        ssize_t n = pread(fd, buffer, sizeof(buffer), offset);
        assert(n >= 0);
        if (n == 0) break;
        CC_SHA256_Update(&context, buffer, (CC_LONG)n); offset += n;
    }
    CC_SHA256_Final(digest, &context);
}
static void make_snapshot(const char* self) {
    char base[PATH_MAX]; assert(realpath("/tmp", base));
    assert(snprintf(snapshot_dir, sizeof(snapshot_dir), "%s/pov4-darwin-live-XXXXXX", base) > 0);
    assert(mkdtemp(snapshot_dir));
    assert(snprintf(snapshot_path, sizeof(snapshot_path), "%s/image", snapshot_dir) > 0);
    int in = open(self, O_RDONLY | O_CLOEXEC); assert(in >= 0);
    int out = open(snapshot_path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0600); assert(out >= 0);
    uint8_t buffer[65536]; ssize_t n;
    while ((n = read(in, buffer, sizeof(buffer))) > 0) assert(write(out, buffer, (size_t)n) == n);
    assert(n == 0 && close(in) == 0 && fsync(out) == 0 && fchmod(out, 0500) == 0 && close(out) == 0);
    snapshot_fd = open(snapshot_path, O_RDONLY | O_CLOEXEC); assert(snapshot_fd >= 0);
    hash_fd(snapshot_fd, snapshot_digest);
}

static void put_u64(SplArray* a, uint64_t value) {
    for (int i = 0; i < 8; i++) assert(rt_array_push(a, (int64_t)((value >> (8 * i)) & 255)));
}
static void set_u64_at(SplArray* a, int64_t offset, uint64_t value) {
    for (int i = 0; i < 8; i++) assert(rt_array_set(a, offset + i, (int64_t)((value >> (8 * i)) & 255)));
}
static void put_bytes(SplArray* a, const uint8_t* bytes, size_t n) {
    for (size_t i = 0; i < n; i++) assert(rt_array_push(a, bytes[i]));
}
static void put_text(SplArray* a, const char* text) {
    size_t n = strlen(text); put_u64(a, n); put_bytes(a, (const uint8_t*)text, n);
}
/* Offsets: 24 wall, 32 grace, 40 cleanup, 64 memory, 72 enforcement, 80 policy. */
static SplArray* request_bytes(const char* cwd, int64_t cwd_pin, const uint8_t cwd_digest[32],
                               const char* child_arg, uint64_t policy) {
    SplArray* a = rt_array_new(2048);
    const uint8_t magic[8] = {'P','O','V','4','R','E','Q',0}; put_bytes(a, magic, 8);
    put_u64(a, 1); put_u64(a, POV4_DARWIN_CAPABILITIES); put_u64(a, 5000000000ULL);
    put_u64(a, 100000000ULL); put_u64(a, 2000000000ULL);
    put_u64(a, 4096); put_u64(a, 4096); put_u64(a, 0);
    put_u64(a, POV4_ENFORCEMENT_NONE); put_u64(a, policy); put_u64(a, 10000000); put_u64(a, TEST_PIN);
    put_bytes(a, snapshot_digest, 32); put_text(a, cwd); put_text(a, cwd);
    put_u64(a, (uint64_t)cwd_pin); put_bytes(a, cwd_digest, 32);
    put_u64(a, 2); put_text(a, "pov4-darwin-live"); put_text(a, child_arg);
    put_u64(a, 1); put_text(a, "POV4_TEST"); put_text(a, "exact");
    return a;
}
static SplArray* tuple_item(SplArray* tuple, int index) {
    return (SplArray*)(uintptr_t)rt_array_get(tuple, index);
}
static int64_t word(SplArray* tuple, int index) { return rt_array_get(tuple_item(tuple, 3), index); }
static SplArray* ticket_from(SplArray* tuple) {
    SplArray* t = rt_array_new(5);
    assert(rt_array_push(t, 4));
    for (int i = 4; i <= 7; i++) assert(rt_array_push(t, word(tuple, i)));
    return t;
}
static SplArray* collect_until(SplArray* ticket, int64_t kind) {
    for (int turn = 0; turn < 400; turn++) {
        SplArray* result = rt_process_observation_v4_collect_value(ticket, 25000000);
        if (word(result, POV4_PACKET_KIND) == kind) return result;
    }
    fprintf(stderr, "collect never reached packet kind %lld\n", (long long)kind);
    abort();
}
static int open_fd_count(void) {
    int count = 0;
    for (int fd = 0; fd < 4096; fd++) if (fcntl(fd, F_GETFD) >= 0) count++;
    return count;
}
static int pid_gone(pid_t pid) {
    for (int turn = 0; turn < 200; turn++) {
        if (kill(pid, 0) != 0 && errno == ESRCH) return 1;
        usleep(10000);
    }
    return 0;
}
static int stdout_equals(SplArray* frozen, const char* text) {
    SplArray* out = tuple_item(frozen, 0);
    if (rt_array_len(out) != (int64_t)strlen(text)) return 0;
    for (size_t i = 0; i < strlen(text); i++)
        if (rt_array_get(out, (int64_t)i) != (uint8_t)text[i]) return 0;
    return 1;
}

static void check_capabilities(void) {
    SplArray* caps = rt_process_observation_v4_capabilities_value();
    assert(rt_array_get(caps, 2) == 1 && rt_array_get(caps, 7) == 0);
    int64_t bits = rt_array_get(caps, 3);
    assert(bits == POV4_DARWIN_CAPABILITIES);
    assert((bits & (POV4_CAP_PINNED_EXEC | POV4_CAP_PTRACE_EXEC | POV4_CAP_RLIMIT_AS)) == 0);
    assert((bits & POV4_CAP_DARWIN_SNAPSHOT_EXEC) && (bits & POV4_CAP_DARWIN_SPAWN_EXEC_PROOF) &&
           (bits & POV4_CAP_PROCESS_GROUP_RETIRE));
}

static void check_leader_only(const char* cwd, int64_t pin, const uint8_t digest[32]) {
    SplArray* started = rt_process_observation_v4_start_pinned_value(TEST_PIN, pin,
        request_bytes(cwd, pin, digest, "--child", POV4_DESCENDANT_LEADER));
    if (word(started, POV4_STATUS) != POV4_STATUS_RUNNING)
        fprintf(stderr, "start: status=%lld errno=%lld phase=%lld reason=%lld\n",
            (long long)word(started, POV4_STATUS), (long long)word(started, POV4_ERRNO),
            (long long)word(started, POV4_FAILURE_PHASE), (long long)word(started, POV4_FAILURE_REASON));
    assert(word(started, POV4_STATUS) == POV4_STATUS_RUNNING);
    assert(word(started, POV4_EXEC_STATE) == POV4_EXEC_CONFIRMED);
    assert(word(started, POV4_VALIDITY) & POV4_VALID_EXEC);
    assert(word(started, POV4_EXEC_CONFIRMED_NS) >= word(started, POV4_PROCESS_STARTED_NS));
    SplArray* ticket = ticket_from(started);
    SplArray* frozen = collect_until(ticket, POV4_KIND_FROZEN);
    assert(word(frozen, POV4_STATUS) == POV4_STATUS_TERMINAL);
    if (word(frozen, POV4_EXIT_CODE) != 7)
        fprintf(stderr, "leader exit=%lld signal=%lld term=%lld kill=%lld reason=%lld errno=%lld\n",
                (long long)word(frozen, POV4_EXIT_CODE), (long long)word(frozen, POV4_SIGNAL),
                (long long)word(frozen, POV4_TERM_ATTEMPTED), (long long)word(frozen, POV4_KILL_ATTEMPTED),
                (long long)word(frozen, POV4_FAILURE_REASON), (long long)word(frozen, POV4_RAW_WAIT));
    assert(word(frozen, POV4_EXIT_CODE) == 7 && word(frozen, POV4_SIGNAL) == 0);
    assert(word(frozen, POV4_LEADER_REAPED) == 1);
    assert(word(frozen, POV4_TREE_EMPTY) == 0 && word(frozen, POV4_TREE_EMPTY_NS) == -1);
    assert(word(frozen, POV4_TREE_CONTROL_AVAILABLE) == 0);
    assert((word(frozen, POV4_VALIDITY) & POV4_VALID_TREE_CONTROL) == 0);
    assert((word(frozen, POV4_VALIDITY) & POV4_VALID_DIRECT_RSS) &&
           word(frozen, POV4_CHILD_DIRECT_RSS_BYTES) > 0);
    assert(word(frozen, POV4_ENFORCEMENT_KIND) == POV4_ENFORCEMENT_NONE &&
           word(frozen, POV4_MEMORY_LIMIT_BYTES) == 0);
    assert(word(frozen, POV4_TERM_ATTEMPTED) == 0 && word(frozen, POV4_FAILURE_PHASE) == 0);
    assert(stdout_equals(frozen, cwd));
    SplArray* err = tuple_item(frozen, 1);
    assert(rt_array_len(err) == 4 && rt_array_get(err, 0) == 'f');
    SplArray* ack = rt_process_observation_v4_ack_collect_value(ticket, tuple_item(frozen, 2));
    assert(word(ack, POV4_PACKET_KIND) == POV4_KIND_ACK);
    SplArray* again = rt_process_observation_v4_ack_collect_value(ticket, tuple_item(frozen, 2));
    assert(word(again, POV4_STATUS) == POV4_STATUS_REJECTED);
}

static void check_process_group(const char* cwd, int64_t pin, const uint8_t digest[32]) {
    SplArray* started = rt_process_observation_v4_start_pinned_value(TEST_PIN, pin,
        request_bytes(cwd, pin, digest, "--group-child", POV4_DESCENDANT_PROCESS_GROUP));
    assert(word(started, POV4_STATUS) == POV4_STATUS_RUNNING);
    assert(word(started, POV4_PROCESS_STARTED_NS) > 0);
    SplArray* ticket = ticket_from(started);
    SplArray* frozen = collect_until(ticket, POV4_KIND_FROZEN);
    assert(word(frozen, POV4_EXIT_CODE) == 0 && word(frozen, POV4_LEADER_REAPED) == 1);
    assert(word(frozen, POV4_TREE_CONTROL_AVAILABLE) == 1);
    assert(word(frozen, POV4_VALIDITY) & POV4_VALID_TREE_CONTROL);
    assert(word(frozen, POV4_TREE_EMPTY) == 1);
    assert(word(frozen, POV4_TREE_EMPTY_NS) >= word(frozen, POV4_LEADER_WAITED_NS));
    assert(word(frozen, POV4_TREE_EMPTY_NS) >= word(frozen, POV4_PROCESS_STARTED_NS));
    /* The grandchild printed its pid and slept holding stdout; retirement
     * killed it before the leader was reaped. */
    SplArray* out = tuple_item(frozen, 0);
    char text[32] = {0};
    for (int64_t i = 0; i < rt_array_len(out) && i < 31; i++) text[i] = (char)rt_array_get(out, i);
    long grandchild = strtol(text, NULL, 10);
    assert(grandchild > 1 && pid_gone((pid_t)grandchild));
    SplArray* ack = rt_process_observation_v4_ack_collect_value(ticket, tuple_item(frozen, 2));
    assert(word(ack, POV4_PACKET_KIND) == POV4_KIND_ACK);
}

static void check_deadline(const char* cwd, int64_t pin, const uint8_t digest[32]) {
    SplArray* request = request_bytes(cwd, pin, digest, "--wait-child", POV4_DESCENDANT_PROCESS_GROUP);
    set_u64_at(request, 24, 250000000ULL);
    SplArray* started = rt_process_observation_v4_start_pinned_value(TEST_PIN, pin, request);
    assert(word(started, POV4_STATUS) == POV4_STATUS_RUNNING);
    SplArray* ticket = ticket_from(started);
    SplArray* frozen = collect_until(ticket, POV4_KIND_FROZEN);
    assert(word(frozen, POV4_TERM_ATTEMPTED) == 1 && word(frozen, POV4_KILL_ATTEMPTED) == 1);
    assert(word(frozen, POV4_KILL_SENT) == 1 && word(frozen, POV4_SIGNAL) == SIGKILL);
    assert(word(frozen, POV4_FAILURE_REASON) == POV4_REASON_EXEC_DEADLINE);
    assert(word(frozen, POV4_TREE_EMPTY) == 1);
    SplArray* ack = rt_process_observation_v4_ack_collect_value(ticket, tuple_item(frozen, 2));
    assert(word(ack, POV4_PACKET_KIND) == POV4_KIND_ACK);
}

static void check_refusals(const char* cwd, int64_t pin, const uint8_t digest[32]) {
    /* Darwin has no memory cap: RLIMIT_AS/cgroup enforcement is refused
     * before the executable is acquired. */
    for (uint64_t enforcement = POV4_ENFORCEMENT_CGROUP; enforcement <= POV4_ENFORCEMENT_RLIMIT_AS; enforcement++) {
        SplArray* request = request_bytes(cwd, pin, digest, "--child", POV4_DESCENDANT_LEADER);
        set_u64_at(request, 64, 64ULL * 1024 * 1024);
        set_u64_at(request, 72, enforcement);
        int before = acquisitions;
        SplArray* rejected = rt_process_observation_v4_start_pinned_value(TEST_PIN, pin, request);
        assert(word(rejected, POV4_STATUS) == POV4_STATUS_REJECTED);
        assert(word(rejected, POV4_ERRNO) == ENOTSUP);
        assert(word(rejected, POV4_FAILURE_REASON) == POV4_REASON_MEMORY);
        assert(word(rejected, POV4_PID) == 0 && acquisitions == before);
    }
    /* Cgroup descendant policy stays unavailable. */
    SplArray* request = request_bytes(cwd, pin, digest, "--child", 3);
    SplArray* rejected = rt_process_observation_v4_start_pinned_value(TEST_PIN, pin, request);
    assert(word(rejected, POV4_STATUS) == POV4_STATUS_REJECTED &&
           word(rejected, POV4_FAILURE_REASON) == POV4_REASON_PROVIDER);
}

static void check_tampered_snapshot(const char* cwd, int64_t pin, const uint8_t digest[32]) {
    /* A same-UID rewrite after pinning must be refused before any child. */
    assert(chmod(snapshot_path, 0700) == 0);
    int writer = open(snapshot_path, O_WRONLY | O_APPEND | O_CLOEXEC); assert(writer >= 0);
    assert(write(writer, "x", 1) == 1 && close(writer) == 0);
    SplArray* rejected = rt_process_observation_v4_start_pinned_value(TEST_PIN, pin,
        request_bytes(cwd, pin, digest, "--child", POV4_DESCENDANT_LEADER));
    assert(word(rejected, POV4_STATUS) == POV4_STATUS_REJECTED);
    assert(word(rejected, POV4_ERRNO) == ESTALE && word(rejected, POV4_PID) == 0);
}

static void check_startup_cleanup(const char* cwd, int64_t pin, const uint8_t digest[32]) {
    /* An injected post-spawn proof failure keeps cleanup authority only. */
    rt_process_observation_v4_test_force_exec_failure(EIO, 1);
    SplArray* started = rt_process_observation_v4_start_pinned_value(TEST_PIN, pin,
        request_bytes(cwd, pin, digest, "--child", POV4_DESCENDANT_PROCESS_GROUP));
    assert(word(started, POV4_STATUS) == POV4_STATUS_CLEANUP_PENDING);
    assert(word(started, POV4_EXEC_STATE) == POV4_EXEC_PENDING);
    assert(word(started, POV4_ERRNO) == EIO);
    pid_t child = (pid_t)word(started, POV4_PID);
    assert(child > 0);
    SplArray* ticket = ticket_from(started);
    SplArray* frozen = collect_until(ticket, POV4_KIND_CLEANUP_FROZEN);
    /* TERM and KILL are both sent to the never-resumed child; either ends it. */
    assert(word(frozen, POV4_LEADER_REAPED) == 1);
    assert(word(frozen, POV4_SIGNAL) == SIGKILL || word(frozen, POV4_SIGNAL) == SIGTERM);
    assert(word(frozen, POV4_TERM_ATTEMPTED) == 1 && word(frozen, POV4_KILL_ATTEMPTED) == 1);
    assert(word(frozen, POV4_TREE_CONTROL_AVAILABLE) == 0 && word(frozen, POV4_TREE_EMPTY) == 0);
    assert(rt_array_len(tuple_item(frozen, 0)) == 0); /* Never resumed: no output. */
    SplArray* ack = rt_process_observation_v4_ack_collect_value(ticket, tuple_item(frozen, 2));
    assert(word(ack, POV4_PACKET_KIND) == POV4_KIND_CLEANUP_ACK);
    assert(pid_gone(child));
}

int main(int argc, char** argv) {
    if (argc == 2 && strcmp(argv[1], "--child") == 0) {
        extern char** environ;
        int count = 0; for (char** e = environ; *e; e++) count++;
        const char* exact = getenv("POV4_TEST"); char cwd[PATH_MAX];
        if (count != 1 || !exact || strcmp(exact, "exact") != 0 || !getcwd(cwd, sizeof(cwd))) return 90;
        if (fcntl(3, F_GETFD) >= 0) return 89; /* Only stdio is inherited. */
        if (write(STDOUT_FILENO, cwd, strlen(cwd)) != (ssize_t)strlen(cwd)) return 91;
        if (write(STDERR_FILENO, "fair", 4) != 4) return 92;
        return 7;
    }
    if (argc == 2 && strcmp(argv[1], "--group-child") == 0) {
        pid_t grandchild = fork();
        if (grandchild < 0) return 93;
        if (grandchild == 0) { signal(SIGTERM, SIG_IGN); sleep(20); _exit(0); }
        char text[32]; int n = snprintf(text, sizeof(text), "%d", (int)grandchild);
        return write(STDOUT_FILENO, text, (size_t)n) == n ? 0 : 94;
    }
    if (argc == 2 && strcmp(argv[1], "--wait-child") == 0) {
        signal(SIGTERM, SIG_IGN);
        sleep(5); /* Leak backstop if an assertion aborts the owner. */
        return 95;
    }
    char self[PATH_MAX]; uint32_t self_size = sizeof(self);
    assert(_NSGetExecutablePath(self, &self_size) == 0);
    make_snapshot(self);
    char cwd[PATH_MAX]; assert(realpath(".", cwd));
    int64_t pin = rt_process_observation_v4_pin_cwd_value(cwd, strlen(cwd));
    assert(pin > 0);
    SplArray* digest_value = rt_process_observation_v4_cwd_digest_value(pin);
    uint8_t digest[32];
    assert(rt_array_bytes_copy_checked((int64_t)(uintptr_t)digest_value, digest, 32) == 32);
    int baseline = open_fd_count();

    check_capabilities();
    check_leader_only(cwd, pin, digest);
    check_process_group(cwd, pin, digest);
    check_deadline(cwd, pin, digest);
    check_refusals(cwd, pin, digest);
    check_startup_cleanup(cwd, pin, digest);
    /* Every lease above was acknowledged: no slot keeps a descriptor. */
    assert(open_fd_count() == baseline);
    for (int round = 0; round < POV4_SLOTS + 2; round++) check_leader_only(cwd, pin, digest);
    assert(open_fd_count() == baseline);
    /* Last: a write invalidates the snapshot vnode's code-signing state, so
     * the rewritten image is never executed again by this check. */
    check_tampered_snapshot(cwd, pin, digest);

    assert(rt_process_observation_v4_close_cwd_value(pin) == 1);
    assert(close(snapshot_fd) == 0 && unlink(snapshot_path) == 0 && rmdir(snapshot_dir) == 0);
    puts("runtime_process_observation_v4_darwin_live_selfcheck: PASS");
    return 0;
}
#endif

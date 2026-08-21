/* Runtime-owned synchronous process capsule used by the registered language
 * ABI. Focused C selfchecks cover provider and receipt failure paths; deployed
 * qualification still requires source-matched Stage2/native facade evidence. */
#include "runtime.h"

/* Every value this file releases via rt_free_deep is an rt_string_new result
 * (stdout/stderr capture strings on the error-cleanup paths), so a plain
 * rt_string_free is semantically exact. The general rt_free_deep lives in
 * runtime_native.c, which the Rust seed runtime crate deliberately does NOT
 * compile (duplicate rt_host_gpu_* symbols — see compiler_rust/runtime/build.rs).
 * The seed build defines SIMPLE_RUNTIME_PROCESS_OWNED_STRING_FREE to swap in
 * rt_string_free (implemented in Rust there); the native product build keeps
 * the real rt_free_deep. Mirrors the SIMPLE_RUNTIME_AUDIO_STUB_SPLARRAY
 * precedent in that build.rs. */
#ifdef SIMPLE_RUNTIME_PROCESS_OWNED_STRING_FREE
#define RT_OWNED_FREE_VALUE(v) rt_string_free(v)
#else
#define RT_OWNED_FREE_VALUE(v) rt_free_deep(v)
#endif

#if !defined(_WIN32) && defined(__unix__)

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#ifdef __linux__
#include <sys/syscall.h>
#endif

#define RT_OWNED_PROCESS_SLOTS 16
#define RT_OWNED_TERM_GRACE_MS 100
#define RT_OWNED_POST_REAP_DRAIN_MS 100
#define RT_OWNED_DRAIN_QUANTUM (64U * 1024U)
#define RT_OWNED_ABI_MAX_TIMEOUT_MS 3600000
#define RT_OWNED_ABI_MAX_OUTPUT_BYTES (16U * 1024U * 1024U)

/* Output is owned by the lease, never by a transient poll caller.  A single
 * bounded record array preserves the interleaving source while separate read
 * cursors let stdout/stderr consumers drain their own stream exactly once. */
typedef struct RtOwnedCapturedByte {
    unsigned char byte;
    unsigned char stream; /* 0 stdout, 1 stderr */
} RtOwnedCapturedByte;

#ifndef RT_OWNED_HOST_MALLOC
#define RT_OWNED_HOST_MALLOC malloc
#define RT_OWNED_HOST_CALLOC calloc
#define RT_OWNED_HOST_FREE free
#endif
#ifndef RT_OWNED_TOKEN_FILL
#define RT_OWNED_TOKEN_FILL(dst, len) syscall(SYS_getrandom, (dst), (len), 0)
#endif
#ifndef RT_OWNED_SIGNAL_GROUP
#define RT_OWNED_SIGNAL_GROUP(pid, pgid, pidfd, sig) owned_signal_group((pid), (pgid), (pidfd), (sig))
#endif

typedef struct RtOwnedSlot {
    pid_t pid;
    pid_t pgid;
    int pidfd;
    uint64_t start_identity;
    uint64_t generation;
    int cancel_requested;
    uint64_t token_high;
    uint64_t token_low;
    int state; /* 0 free, 1 live, 2 terminal */
    int out_fd;
    int err_fd;
    int out_open;
    int err_open;
    int64_t started_ms;
    int64_t timeout_ms;
    int64_t term_grace_ms;
    int64_t term_at_ms;
    int64_t drain_deadline_ms;
    int status;
    uint64_t output_limit;
    uint64_t stdout_seen;
    uint64_t stderr_seen;
    uint64_t stdout_kept;
    uint64_t stderr_kept;
    uint64_t stdout_delivered;
    uint64_t stderr_delivered;
    uint64_t stdout_scan;
    uint64_t stderr_scan;
    uint64_t retained_count;
    RtOwnedCapturedByte* retained;
    int stdout_truncated;
    int stderr_truncated;
    int timed_out;
    int term_sent;
    int kill_sent;
    int identity_revalidated;
    int reaped;
    int runtime_error;
    int retired;
    int op_refs;
    int collecting;
    pthread_mutex_t* state_lock;
} RtOwnedSlot;

typedef struct RtOwnedCleanup {
    uint32_t slot;
    uint64_t generation;
    pid_t pid;
    pid_t pgid;
    int pidfd;
    int out_fd;
    int err_fd;
    int reserved;
    int reaped;
} RtOwnedCleanup;

static RtOwnedSlot rt_owned_slots[RT_OWNED_PROCESS_SLOTS];
static pthread_mutex_t rt_owned_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t rt_owned_state_locks[RT_OWNED_PROCESS_SLOTS];
static pthread_once_t rt_owned_state_once = PTHREAD_ONCE_INIT;
#if defined(RT_PROCESS_OWNED_TESTING) || defined(RT_PROCESS_OWNED_CORE_ONLY)
static int rt_owned_test_collision_count;
static RtOwnedProcessTokenV2 rt_owned_test_collision_token;
static int rt_owned_test_signal_fail_count;
static int rt_owned_test_read_fail_count;
void rt_process_owned_test_force_collision(RtOwnedProcessTokenV2 token, int count) {
    rt_owned_test_collision_token = token; rt_owned_test_collision_count = count;
}
void rt_process_owned_test_force_signal_failure(int count) { rt_owned_test_signal_fail_count = count; }
void rt_process_owned_test_force_read_failure(int count) { rt_owned_test_read_fail_count = count; }
#endif

static void owned_state_locks_init(void) {
    for (uint32_t i = 0; i < RT_OWNED_PROCESS_SLOTS; i++)
        (void)pthread_mutex_init(&rt_owned_state_locks[i], NULL);
}

static int64_t owned_now_ms(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return -1;
    if (ts.tv_sec > INT64_MAX / 1000) return INT64_MAX;
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static uint64_t owned_add_sat(uint64_t a, uint64_t b) {
    return UINT64_MAX - a < b ? UINT64_MAX : a + b;
}

static uint64_t owned_start_identity(pid_t pid) {
#ifdef __linux__
    char path[64], line[2048];
    snprintf(path, sizeof(path), "/proc/%ld/stat", (long)pid);
    FILE* file = fopen(path, "r");
    if (!file) return 0;
    if (!fgets(line, sizeof(line), file)) { fclose(file); return 0; }
    fclose(file);
    char* cursor = strrchr(line, ')');
    if (!cursor || cursor[1] != ' ') return 0;
    cursor += 2;
    for (int field = 3; field < 22; field++) {
        cursor = strchr(cursor, ' ');
        if (!cursor) return 0;
        cursor++;
    }
    errno = 0;
    char* end = NULL;
    unsigned long long value = strtoull(cursor, &end, 10);
    return errno == 0 && end != cursor ? (uint64_t)value : 0;
#else
    (void)pid;
    return 0;
#endif
}

static int owned_pidfd_open(pid_t pid) {
#if defined(__linux__) && defined(SYS_pidfd_open)
    return (int)syscall(SYS_pidfd_open, pid, 0);
#else
    (void)pid;
    errno = ENOTSUP;
    return -1;
#endif
}

static int owned_pidfd_live(int pidfd) {
    struct pollfd pfd = {pidfd, POLLIN, 0};
    int rc;
    do rc = poll(&pfd, 1, 0); while (rc < 0 && errno == EINTR);
    return rc == 0;
}

static int owned_pidfd_valid(int pidfd) {
    int rc;
    do rc = fcntl(pidfd, F_GETFD); while (rc < 0 && errno == EINTR);
    return rc >= 0;
}

static int owned_reserve(uint32_t* index, uint64_t* generation) {
    (void)pthread_once(&rt_owned_state_once, owned_state_locks_init);
    if (pthread_mutex_lock(&rt_owned_lock) != 0) return 0;
    for (uint32_t i = 0; i < RT_OWNED_PROCESS_SLOTS; i++) {
        if (rt_owned_slots[i].pid == 0 && !rt_owned_slots[i].retired) {
            uint64_t next = rt_owned_slots[i].generation + 1;
            if (next == 0) { rt_owned_slots[i].retired = 1; continue; }
            rt_owned_slots[i].pid = -1;
            rt_owned_slots[i].pidfd = -1;
            rt_owned_slots[i].generation = next;
            rt_owned_slots[i].state_lock = &rt_owned_state_locks[i];
            *index = i;
            *generation = rt_owned_slots[i].generation;
            pthread_mutex_unlock(&rt_owned_lock);
            return 1;
        }
    }
    pthread_mutex_unlock(&rt_owned_lock);
    return 0;
}

static void owned_release(uint32_t index, uint64_t generation) {
    if (pthread_mutex_lock(&rt_owned_lock) != 0) return;
    if (index < RT_OWNED_PROCESS_SLOTS && rt_owned_slots[index].generation == generation) {
        uint64_t keep_generation = rt_owned_slots[index].generation;
        int keep_retired = rt_owned_slots[index].retired;
        pthread_mutex_t* keep_lock = rt_owned_slots[index].state_lock;
        memset(&rt_owned_slots[index], 0, sizeof(rt_owned_slots[index]));
        rt_owned_slots[index].generation = keep_generation;
        rt_owned_slots[index].retired = keep_retired;
        rt_owned_slots[index].state_lock = keep_lock;
    }
    pthread_mutex_unlock(&rt_owned_lock);
}

/* A live pidfd pins the leader PID, so the process-group id cannot be reused
 * between this validation and kill(-pgid).  Platforms without pidfds fail
 * closed rather than relying on a racy /proc identity check. */
static int owned_signal_group(pid_t pid, pid_t pgid, int pidfd, int sig) {
    if (pid <= 0 || pgid != pid || pidfd < 0 || !owned_pidfd_live(pidfd)) {
        errno = ESTALE;
        return 0;
    }
    if (getpgid(pid) != pgid) { errno = ESTALE; return 0; }
    if (kill(-pgid, sig) == 0 || errno == ESRCH) return 1;
    return 0;
}

/* Internal callers retain an unreaped direct child.  That zombie pins both its
 * PID and the process-group id even after the pidfd becomes readable, so group
 * cleanup remains safe until waitpid consumes the leader. */
static int owned_signal_group_pinned(pid_t pid, pid_t pgid, int pidfd, int sig) {
    if (pid <= 0 || pgid != pid || pidfd < 0 || !owned_pidfd_valid(pidfd)) {
        errno = ESTALE;
        return 0;
    }
    if (kill(-pgid, sig) == 0 || errno == ESRCH) return 1;
    return 0;
}

bool rt_process_owned_cancel(uint64_t requested_slot, uint64_t requested_generation,
                             int64_t requested_pid, uint64_t identity,
                             RtOwnedProcessCancelReceipt* receipt) {
    if (!receipt) return false;
    memset(receipt, 0, sizeof(*receipt));
    receipt->version = RT_OWNED_PROCESS_CANCEL_RECEIPT_VERSION;
    receipt->slot = requested_slot;
    receipt->generation = requested_generation;
    receipt->pid = requested_pid;
    receipt->start_identity = identity;
    receipt->runtime_error = ESTALE;
    if (requested_pid <= 0 || identity == 0 || requested_slot >= RT_OWNED_PROCESS_SLOTS ||
        requested_generation == 0) return false;
    int pidfd = -1;
    if (pthread_mutex_lock(&rt_owned_lock) != 0) return false;
    RtOwnedSlot* slot = &rt_owned_slots[requested_slot];
    int matched = slot->state == 0 && slot->pid == (pid_t)requested_pid &&
                  slot->generation == requested_generation &&
                  slot->start_identity == identity;
    if (matched) {
        pidfd = slot->pidfd;
    }
    int ok = matched && pidfd >= 0;
    if (ok) {
        slot->cancel_requested = 1;
        receipt->accepted = 1;
        receipt->runtime_error = 0;
    }
    pthread_mutex_unlock(&rt_owned_lock);
    return ok != 0;
}

bool rt_process_owned_terminate(int64_t requested_pid, uint64_t identity) {
    /* A raw PID/identity pair is never sufficient authorization. */
    (void)requested_pid;
    (void)identity;
    return false;
}

bool rt_process_owned_cancel_value(uint64_t slot, uint64_t generation,
                                   int64_t pid, uint64_t identity) {
    RtOwnedProcessCancelReceipt receipt;
    return rt_process_owned_cancel(slot, generation, pid, identity, &receipt);
}

static int owned_set_nonblocking(int fd) {
    int flags;
    do flags = fcntl(fd, F_GETFL); while (flags < 0 && errno == EINTR);
    if (flags < 0) return 0;
    int rc;
    do rc = fcntl(fd, F_SETFL, flags | O_NONBLOCK); while (rc < 0 && errno == EINTR);
    return rc == 0;
}

static void owned_capture(int fd, char* dst, uint64_t capacity, uint64_t limit,
                          uint64_t* seen, uint64_t* kept, int32_t* truncated,
                          int* open_flag) {
    char chunk[4096];
    uint64_t quantum = 0;
    while (quantum < RT_OWNED_DRAIN_QUANTUM) {
        ssize_t n = read(fd, chunk, sizeof(chunk));
        if (n > 0) {
            uint64_t count = (uint64_t)n;
            *seen = owned_add_sat(*seen, count);
            quantum = owned_add_sat(quantum, count);
            uint64_t room = *kept < limit ? limit - *kept : 0;
            uint64_t buffer_room = capacity > 0 && *kept < capacity - 1
                                       ? capacity - 1 - *kept : 0;
            if (room > buffer_room) room = buffer_room;
            uint64_t take = count < room ? count : room;
            if (take) memcpy(dst + *kept, chunk, (size_t)take);
            *kept = owned_add_sat(*kept, take);
            if (take < count) *truncated = 1;
            continue;
        }
        if (n == 0 || (errno != EAGAIN && errno != EWOULDBLOCK && errno != EINTR)) {
            close(fd); *open_flag = 0;
        }
        return;
    }
}

static void owned_cleanup(void* opaque) {
    RtOwnedCleanup* c = (RtOwnedCleanup*)opaque;
    if (c->pid > 0 && !c->reaped) {
        (void)owned_signal_group_pinned(c->pid, c->pgid, c->pidfd, SIGKILL);
        int status;
        pid_t rc;
        do rc = waitpid(c->pid, &status, 0); while (rc < 0 && errno == EINTR);
        if (rc == c->pid) c->reaped = 1;
    }
    if (c->out_fd >= 0) close(c->out_fd);
    if (c->err_fd >= 0) close(c->err_fd);
    /* Unpublish while the pidfd still identifies this slot.  Closing first
     * permits another thread to reuse the fd number while terminate() can
     * still discover the stale published entry. */
    if (c->reserved) {
        owned_release(c->slot, c->generation);
        c->reserved = 0;
    }
    if (c->pidfd >= 0) { close(c->pidfd); c->pidfd = -1; }
}

static int owned_token_random(RtOwnedProcessTokenV2* token) {
#if defined(RT_PROCESS_OWNED_TESTING) || defined(RT_PROCESS_OWNED_CORE_ONLY)
    if (rt_owned_test_collision_count > 0) {
        rt_owned_test_collision_count--;
        *token = rt_owned_test_collision_token;
        return 1;
    }
#endif
#if defined(__linux__) && defined(SYS_getrandom)
    uint8_t* dst = (uint8_t*)token;
    size_t done = 0;
    while (done < sizeof(*token)) {
        ssize_t n = RT_OWNED_TOKEN_FILL(dst + done, sizeof(*token) - done);
        if (n > 0) { done += (size_t)n; continue; }
        if (n < 0 && errno == EINTR) continue;
        return 0;
    }
    return token->high != 0 || token->low != 0;
#else
    (void)token;
    errno = ENOTSUP;
    return 0;
#endif
}

static int owned_token_equal(const RtOwnedSlot* slot, RtOwnedProcessTokenV2 token) {
    uint64_t diff = (slot->token_high ^ token.high) | (slot->token_low ^ token.low);
    return diff == 0 && (token.high != 0 || token.low != 0);
}

static RtOwnedSlot* owned_find_token_locked(RtOwnedProcessTokenV2 token,
                                             uint32_t* index) {
    RtOwnedSlot* match = NULL;
    uint32_t found = 0;
    for (uint32_t i = 0; i < RT_OWNED_PROCESS_SLOTS; i++) {
        int equal = rt_owned_slots[i].pid != 0 && owned_token_equal(&rt_owned_slots[i], token);
        if (equal) { match = &rt_owned_slots[i]; found = i; }
    }
    if (match && index) *index = found;
    return match;
}

static RtOwnedSlot* owned_token_acquire(RtOwnedProcessTokenV2 token,
                                        uint32_t* index) {
    if (pthread_mutex_lock(&rt_owned_lock) != 0) return NULL;
    RtOwnedSlot* slot = owned_find_token_locked(token, index);
    if (slot && !slot->collecting) slot->op_refs++;
    else slot = NULL;
    pthread_mutex_unlock(&rt_owned_lock);
    return slot;
}

static void owned_token_release(RtOwnedSlot* slot) {
    if (pthread_mutex_lock(&rt_owned_lock) != 0) return;
    if (slot->op_refs > 0) slot->op_refs--;
    pthread_mutex_unlock(&rt_owned_lock);
}

static int owned_token_mint_install_reserved(uint32_t index, uint64_t generation,
                                             RtOwnedProcessTokenV2* token) {
    for (int attempt = 0; attempt < 16; attempt++) {
        RtOwnedProcessTokenV2 candidate = {0, 0};
        if (!owned_token_random(&candidate)) return 0;
        if (pthread_mutex_lock(&rt_owned_lock) != 0) return 0;
        int collision = owned_find_token_locked(candidate, NULL) != NULL;
        int reserved = index < RT_OWNED_PROCESS_SLOTS &&
            rt_owned_slots[index].generation == generation && rt_owned_slots[index].pid == -1;
        if (!collision && reserved) {
            rt_owned_slots[index].token_high = candidate.high;
            rt_owned_slots[index].token_low = candidate.low;
        }
        pthread_mutex_unlock(&rt_owned_lock);
        if (!reserved) { errno = ESTALE; return 0; }
        if (!collision) { *token = candidate; return 1; }
    }
    errno = EEXIST;
    return 0;
}

static void owned_async_close_pipes(RtOwnedSlot* slot) {
    if (slot->out_open) { close(slot->out_fd); slot->out_open = 0; slot->out_fd = -1; }
    if (slot->err_open) { close(slot->err_fd); slot->err_open = 0; slot->err_fd = -1; }
}

/* A post-reap deadline exists only for descendants that retained an inherited
 * pipe forever.  Closing such a pipe is a deliberate bounded-loss policy, so
 * the receipt must say so; a terminal non-truncated receipt always drained
 * both pipes to EOF. */
static void owned_async_close_pipes_truncated(RtOwnedSlot* slot) {
    if (slot->out_open) slot->stdout_truncated = 1;
    if (slot->err_open) slot->stderr_truncated = 1;
    owned_async_close_pipes(slot);
}

static void owned_async_capture_one(RtOwnedSlot* slot, int fd, int stream,
                                    int* open_flag, uint64_t* budget) {
    char chunk[4096];
    uint64_t* seen = stream ? &slot->stderr_seen : &slot->stdout_seen;
    uint64_t* kept = stream ? &slot->stderr_kept : &slot->stdout_kept;
    int* truncated = stream ? &slot->stderr_truncated : &slot->stdout_truncated;
    uint64_t quantum = 0;
    while (*open_flag && quantum < RT_OWNED_DRAIN_QUANTUM && *budget > 0) {
        size_t request = sizeof(chunk);
        if ((uint64_t)request > *budget) request = (size_t)*budget;
        ssize_t n;
#if defined(RT_PROCESS_OWNED_TESTING) || defined(RT_PROCESS_OWNED_CORE_ONLY)
        if (rt_owned_test_read_fail_count > 0) {
            rt_owned_test_read_fail_count--; errno = EIO; n = -1;
        } else
#endif
        n = read(fd, chunk, request);
        if (n > 0) {
            uint64_t count = (uint64_t)n;
            *seen = owned_add_sat(*seen, count);
            quantum = owned_add_sat(quantum, count);
            *budget -= count;
            uint64_t room = slot->retained_count < slot->output_limit
                ? slot->output_limit - slot->retained_count : 0;
            uint64_t take = count < room ? count : room;
            for (uint64_t i = 0; i < take; i++) {
                slot->retained[slot->retained_count + i].byte = (unsigned char)chunk[i];
                slot->retained[slot->retained_count + i].stream = (unsigned char)stream;
            }
            slot->retained_count = owned_add_sat(slot->retained_count, take);
            *kept = owned_add_sat(*kept, take);
            if (take < count) *truncated = 1;
            continue;
        }
        if (n == 0) {
            close(fd); *open_flag = 0;
        } else if (errno != EAGAIN && errno != EWOULDBLOCK && errno != EINTR) {
            *truncated = 1;
            if (slot->runtime_error == 0) slot->runtime_error = errno ? errno : EIO;
            close(fd); *open_flag = 0;
        }
        break;
    }
}

/* A zero-size caller buffer is an observation-only poll: it must not consume
 * any retained bytes.  The scan cursor therefore advances only while a byte
 * is copied into an actual caller buffer. */
static void owned_async_deliver(RtOwnedSlot* slot, int stream, char* dst,
                                uint64_t cap) {
    if (cap) dst[0] = '\0';
    if (!dst || cap <= 1) return;
    uint64_t* scan = stream ? &slot->stderr_scan : &slot->stdout_scan;
    uint64_t* delivered = stream ? &slot->stderr_delivered : &slot->stdout_delivered;
    uint64_t copied = 0;
    while (*scan < slot->retained_count && copied < cap - 1) {
        RtOwnedCapturedByte* item = &slot->retained[*scan];
        (*scan)++;
        if (item->stream != (unsigned char)stream) continue;
        dst[copied++] = (char)item->byte;
        *delivered = owned_add_sat(*delivered, 1);
    }
    dst[copied] = '\0';
}

static void owned_async_fill_poll(const RtOwnedSlot* slot,
                                  RtOwnedProcessPollReceiptV2* receipt) {
    memset(receipt, 0, sizeof(*receipt));
    receipt->version = RT_OWNED_PROCESS_ASYNC_VERSION;
    receipt->live = slot->state == 1;
    receipt->terminal = slot->state == 2;
    receipt->cancel_requested = slot->cancel_requested;
    receipt->timed_out = slot->timed_out;
    receipt->term_sent = slot->term_sent;
    receipt->kill_sent = slot->kill_sent;
    receipt->reaped = slot->reaped;
    receipt->stdout_truncated = slot->stdout_truncated;
    receipt->stderr_truncated = slot->stderr_truncated;
    receipt->stdout_bytes_seen = slot->stdout_seen;
    receipt->stderr_bytes_seen = slot->stderr_seen;
    receipt->stdout_bytes_kept = slot->stdout_kept;
    receipt->stderr_bytes_kept = slot->stderr_kept;
    receipt->runtime_error = slot->runtime_error;
}

static void owned_async_fill_result(const RtOwnedSlot* slot,
                                    RtOwnedProcessResultV2* result) {
    memset(result, 0, sizeof(*result));
    result->version = RT_OWNED_PROCESS_ASYNC_VERSION;
    result->pid = slot->pid;
    result->process_group_id = slot->pgid;
    result->start_identity = slot->start_identity;
    if (slot->reaped) {
        if (WIFEXITED(slot->status)) result->exit_code = WEXITSTATUS(slot->status);
        else if (WIFSIGNALED(slot->status)) result->exit_code = 128 + WTERMSIG(slot->status);
        else result->exit_code = -1;
    } else result->exit_code = -1;
    result->timed_out = slot->timed_out;
    result->cancel_requested = slot->cancel_requested;
    result->term_sent = slot->term_sent;
    result->kill_sent = slot->kill_sent;
    result->identity_revalidated = slot->identity_revalidated;
    result->reaped = slot->reaped;
    result->stdout_truncated = slot->stdout_truncated;
    result->stderr_truncated = slot->stderr_truncated;
    result->stdout_bytes_seen = slot->stdout_seen;
    result->stderr_bytes_seen = slot->stderr_seen;
    result->stdout_bytes_kept = slot->stdout_kept;
    result->stderr_bytes_kept = slot->stderr_kept;
    result->runtime_error = slot->runtime_error;
}

/* Reconcile a failed signal with an immediate non-reaping exit observation.
 * A concurrent natural exit is success and is reaped here; ESTALE is reserved
 * for a still-live process whose identity/group no longer matches. */
enum OwnedSignalOutcome { OWNED_SIGNAL_ERROR = 0, OWNED_SIGNAL_SENT = 1, OWNED_SIGNAL_REAPED = 2 };
static enum OwnedSignalOutcome owned_async_signal_or_reap(RtOwnedSlot* slot, int sig, int64_t now) {
    int signalled;
#if defined(RT_PROCESS_OWNED_TESTING) || defined(RT_PROCESS_OWNED_CORE_ONLY)
    if (rt_owned_test_signal_fail_count > 0) { rt_owned_test_signal_fail_count--; signalled = 0; errno = ESRCH; }
    else signalled = RT_OWNED_SIGNAL_GROUP(slot->pid, slot->pgid, slot->pidfd, sig);
#else
    signalled = RT_OWNED_SIGNAL_GROUP(slot->pid, slot->pgid, slot->pidfd, sig);
#endif
    if (signalled) return OWNED_SIGNAL_SENT;
    siginfo_t info; memset(&info, 0, sizeof(info));
    int rc; do rc = waitid(P_PID, (id_t)slot->pid, &info, WEXITED|WNOHANG|WNOWAIT);
    while (rc < 0 && errno == EINTR);
    if (rc == 0 && info.si_pid == slot->pid) {
        (void)owned_signal_group_pinned(slot->pid, slot->pgid, slot->pidfd, SIGKILL);
        pid_t waited; do waited = waitpid(slot->pid, &slot->status, 0);
        while (waited < 0 && errno == EINTR);
        if (waited == slot->pid) {
            slot->reaped = 1;
            slot->drain_deadline_ms = now + RT_OWNED_POST_REAP_DRAIN_MS;
            return OWNED_SIGNAL_REAPED;
        }
        slot->runtime_error = errno ? errno : ECHILD;
        return OWNED_SIGNAL_ERROR;
    }
    slot->runtime_error = ESTALE;
    return OWNED_SIGNAL_ERROR;
}

bool rt_process_owned_start_v2(const char* cmd, const char* const* argv,
                               int64_t timeout_ms, int64_t term_grace_ms,
                               uint64_t max_output_bytes,
                               RtOwnedProcessTokenV2* token,
                               RtOwnedProcessStartReceiptV2* receipt) {
    if (!token || !receipt) return false;
    memset(token, 0, sizeof(*token)); memset(receipt, 0, sizeof(*receipt));
    receipt->version = RT_OWNED_PROCESS_ASYNC_VERSION;
#ifndef __linux__
    (void)cmd; (void)argv; (void)timeout_ms; (void)term_grace_ms; (void)max_output_bytes;
    receipt->runtime_error = ENOTSUP; return false;
#else
    if (!cmd || !argv || !argv[0] || timeout_ms <= 0 ||
        timeout_ms > RT_OWNED_ABI_MAX_TIMEOUT_MS || term_grace_ms < 0 ||
        term_grace_ms > 30000 || max_output_bytes > RT_OWNED_ABI_MAX_OUTPUT_BYTES) {
        receipt->runtime_error = EINVAL; return false;
    }
    uint32_t index = 0; uint64_t generation = 0;
    if (!owned_reserve(&index, &generation)) {
        receipt->runtime_error = errno == EOVERFLOW ? EOVERFLOW : EAGAIN; return false;
    }
    RtOwnedProcessTokenV2 minted = {0, 0};
    if (!owned_token_mint_install_reserved(index, generation, &minted)) {
        receipt->runtime_error = errno; owned_release(index, generation); return false;
    }
    int out_pipe[2] = {-1, -1}, err_pipe[2] = {-1, -1};
    if (pipe(out_pipe) != 0 || pipe(err_pipe) != 0) {
        int saved = errno;
        if (out_pipe[0] >= 0) { close(out_pipe[0]); close(out_pipe[1]); }
        if (err_pipe[0] >= 0) { close(err_pipe[0]); close(err_pipe[1]); }
        receipt->runtime_error = saved; owned_release(index, generation); return false;
    }
    pid_t pid = fork();
    if (pid == 0) {
        (void)setpgid(0, 0); close(out_pipe[0]); close(err_pipe[0]);
        if (dup2(out_pipe[1], STDOUT_FILENO) < 0 || dup2(err_pipe[1], STDERR_FILENO) < 0) _exit(126);
        close(out_pipe[1]); close(err_pipe[1]); execvp(cmd, (char* const*)argv); _exit(127);
    }
    close(out_pipe[1]); close(err_pipe[1]);
    if (pid < 0) {
        int saved = errno; close(out_pipe[0]); close(err_pipe[0]);
        receipt->runtime_error = saved; owned_release(index, generation); return false;
    }
    int pidfd = -1; uint64_t identity = 0; int error = 0;
    RtOwnedCapturedByte* retained = NULL;
    if (max_output_bytes) {
        if (max_output_bytes > SIZE_MAX / sizeof(*retained)) error = EOVERFLOW;
        else if (!(retained = (RtOwnedCapturedByte*)RT_OWNED_HOST_MALLOC(
                         (size_t)max_output_bytes * sizeof(*retained)))) error = ENOMEM;
    }
    if (setpgid(pid, pid) != 0 && errno != EACCES && errno != EEXIST) error = errno;
    if (!error && getpgid(pid) != pid) error = EPERM;
    if (!error && (pidfd = owned_pidfd_open(pid)) < 0) error = errno ? errno : ENOTSUP;
    if (!error && (identity = owned_start_identity(pid)) == 0) error = ESRCH;
    if (!error && (!owned_set_nonblocking(out_pipe[0]) || !owned_set_nonblocking(err_pipe[0]))) error = errno ? errno : EIO;
    int64_t started = !error ? owned_now_ms() : -1;
    if (!error && started < 0) error = errno ? errno : EIO;
    if (error) {
        if (pidfd >= 0) (void)owned_signal_group_pinned(pid, pid, pidfd, SIGKILL);
        else (void)kill(-pid, SIGKILL);
        int status; pid_t reaped; do reaped = waitpid(pid, &status, 0); while (reaped < 0 && errno == EINTR);
        (void)reaped;
        close(out_pipe[0]); close(err_pipe[0]); if (pidfd >= 0) close(pidfd);
        RT_OWNED_HOST_FREE(retained);
        receipt->runtime_error = error; owned_release(index, generation); return false;
    }
    pthread_mutex_lock(&rt_owned_lock);
    RtOwnedSlot* slot = &rt_owned_slots[index];
    if (slot->generation != generation || slot->pid != -1) {
        pthread_mutex_unlock(&rt_owned_lock);
        (void)owned_signal_group_pinned(pid, pid, pidfd, SIGKILL);
        int status; while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {}
        close(out_pipe[0]); close(err_pipe[0]); close(pidfd);
        RT_OWNED_HOST_FREE(retained);
        receipt->runtime_error = ESTALE; owned_release(index, generation); return false;
    }
    slot->pid = pid; slot->pgid = pid; slot->pidfd = pidfd; slot->start_identity = identity;
    slot->token_high = minted.high; slot->token_low = minted.low; slot->state = 1;
    slot->out_fd = out_pipe[0]; slot->err_fd = err_pipe[0]; slot->out_open = 1; slot->err_open = 1;
    slot->started_ms = started; slot->timeout_ms = timeout_ms; slot->term_grace_ms = term_grace_ms;
    slot->term_at_ms = -1; slot->drain_deadline_ms = -1; slot->output_limit = max_output_bytes;
    slot->retained = retained;
    pthread_mutex_unlock(&rt_owned_lock);
    *token = minted; receipt->accepted = 1; return true;
#endif
}

bool rt_process_owned_poll_v2(RtOwnedProcessTokenV2 token, int64_t wait_ms,
                              char* out, uint64_t out_cap, char* err,
                              uint64_t err_cap,
                              RtOwnedProcessPollReceiptV2* receipt) {
    if (!receipt || (out_cap && !out) || (err_cap && !err) || wait_ms < 0 || wait_ms > 1000) return false;
    memset(receipt, 0, sizeof(*receipt)); receipt->version = RT_OWNED_PROCESS_ASYNC_VERSION;
#ifndef __linux__
    (void)token; (void)wait_ms; (void)out; (void)out_cap; (void)err; (void)err_cap;
    receipt->runtime_error = ENOTSUP; return false;
#else
    RtOwnedSlot* slot = owned_token_acquire(token, NULL);
    if (!slot) { receipt->runtime_error = ESTALE; return false; }
    pthread_mutex_lock(slot->state_lock);
    if (slot->state == 2) {
        owned_async_deliver(slot, 0, out, out_cap);
        owned_async_deliver(slot, 1, err, err_cap);
        owned_async_fill_poll(slot, receipt);
        pthread_mutex_unlock(slot->state_lock);
        owned_token_release(slot);
        return true;
    }
    int64_t before_poll = owned_now_ms();
    int64_t earliest = before_poll + 25;
    int64_t timeout_at = slot->started_ms + slot->timeout_ms;
    if (timeout_at < earliest) earliest = timeout_at;
    /* Once KILL was sent there is no remaining grace deadline.  Retaining the
     * expired TERM deadline would clamp every later caller poll to zero and
     * prevent bounded progress to the reaping observation. */
    if (slot->term_sent && !slot->kill_sent && slot->term_at_ms + slot->term_grace_ms < earliest)
        earliest = slot->term_at_ms + slot->term_grace_ms;
    if (slot->reaped && slot->drain_deadline_ms >= 0 && slot->drain_deadline_ms < earliest)
        earliest = slot->drain_deadline_ms;
    int64_t deadline_wait = earliest > before_poll ? earliest - before_poll : 0;
    if (wait_ms > deadline_wait) wait_ms = deadline_wait;
    struct pollfd pfds[2]; nfds_t count = 0; int oi = -1, ei = -1;
    if (slot->out_open) { oi = (int)count; pfds[count++] = (struct pollfd){slot->out_fd, POLLIN|POLLHUP|POLLERR, 0}; }
    if (slot->err_open) { ei = (int)count; pfds[count++] = (struct pollfd){slot->err_fd, POLLIN|POLLHUP|POLLERR, 0}; }
    int rc; do rc = poll(pfds, count, (int)wait_ms); while (rc < 0 && errno == EINTR);
    if (rc < 0) slot->runtime_error = errno;
    uint64_t drain_budget = RT_OWNED_DRAIN_QUANTUM;
    if (oi >= 0 && (pfds[oi].revents & (POLLIN|POLLHUP|POLLERR)))
        owned_async_capture_one(slot, slot->out_fd, 0, &slot->out_open, &drain_budget);
    if (ei >= 0 && (pfds[ei].revents & (POLLIN|POLLHUP|POLLERR)))
        owned_async_capture_one(slot, slot->err_fd, 1, &slot->err_open, &drain_budget);
    if (!slot->out_open) slot->out_fd = -1;
    if (!slot->err_open) slot->err_fd = -1;
    siginfo_t info; memset(&info, 0, sizeof(info));
    int wr; do wr = waitid(P_PID, (id_t)slot->pid, &info, WEXITED|WNOHANG|WNOWAIT); while (wr < 0 && errno == EINTR);
    int64_t now = owned_now_ms();
    if (wr == 0 && info.si_pid == slot->pid && !slot->reaped) {
        (void)owned_signal_group_pinned(slot->pid, slot->pgid, slot->pidfd, SIGKILL);
        pid_t waited; do waited = waitpid(slot->pid, &slot->status, 0); while (waited < 0 && errno == EINTR);
        if (waited == slot->pid) {
            slot->reaped = 1;
            slot->drain_deadline_ms = now + RT_OWNED_POST_REAP_DRAIN_MS;
            if (slot->runtime_error == ESTALE) slot->runtime_error = 0;
        }
        else slot->runtime_error = errno ? errno : ECHILD;
    } else if (wr < 0) slot->runtime_error = errno;
    if (!slot->reaped && (slot->cancel_requested || now - slot->started_ms >= slot->timeout_ms) && !slot->term_sent) {
        slot->timed_out = !slot->cancel_requested;
        enum OwnedSignalOutcome outcome = owned_async_signal_or_reap(slot, SIGTERM, now);
        if (outcome == OWNED_SIGNAL_SENT) {
            slot->identity_revalidated = 1; slot->term_sent = 1; slot->term_at_ms = now;
        } else if (outcome == OWNED_SIGNAL_REAPED) {
            slot->identity_revalidated = 1; slot->runtime_error = 0;
        }
    }
    if (!slot->reaped && slot->term_sent && !slot->kill_sent && now - slot->term_at_ms >= slot->term_grace_ms) {
        enum OwnedSignalOutcome outcome = owned_async_signal_or_reap(slot, SIGKILL, now);
        if (outcome == OWNED_SIGNAL_SENT) slot->kill_sent = 1;
        else if (outcome == OWNED_SIGNAL_REAPED) slot->runtime_error = 0;
    }
    if (slot->reaped && slot->drain_deadline_ms >= 0 && now >= slot->drain_deadline_ms)
        owned_async_close_pipes_truncated(slot);
    if (slot->reaped && !slot->out_open && !slot->err_open) slot->state = 2;
    owned_async_deliver(slot, 0, out, out_cap);
    owned_async_deliver(slot, 1, err, err_cap);
    owned_async_fill_poll(slot, receipt);
    pthread_mutex_unlock(slot->state_lock);
    owned_token_release(slot);
    return receipt->runtime_error == 0;
#endif
}

bool rt_process_owned_cancel_v2(RtOwnedProcessTokenV2 token,
                                RtOwnedProcessCancelReceipt* receipt) {
    if (!receipt) return false;
    memset(receipt, 0, sizeof(*receipt));
    receipt->version = RT_OWNED_PROCESS_ASYNC_VERSION;
#ifndef __linux__
    (void)token; receipt->runtime_error = ENOTSUP; return false;
#else
    RtOwnedSlot* slot = owned_token_acquire(token, NULL);
    if (!slot) { receipt->runtime_error = ESTALE; return false; }
    pthread_mutex_lock(slot->state_lock);
    receipt->pid = slot->pid; receipt->start_identity = slot->start_identity;
    if (slot->state == 1) slot->cancel_requested = 1;
    receipt->accepted = 1;
    int64_t grace_ms = slot->term_grace_ms;
    pthread_mutex_unlock(slot->state_lock);
    /* The registry remains published while synchronous cancellation drives the
     * complete TERM/grace/KILL/reap path.  NULL buffers drain into retained
     * lease-owned storage, so this does not steal caller-visible output. */
    RtOwnedProcessPollReceiptV2 poll;
    int64_t attempts = (grace_ms + RT_OWNED_POST_REAP_DRAIN_MS + 1000 + 9) / 10;
    for (int64_t i = 0; i < attempts; i++) {
        (void)rt_process_owned_poll_v2(token, 10, NULL, 0, NULL, 0, &poll);
        /* Capture/provider errors are result data, not authority to abandon a
         * live child.  Poll retains the first error, but cancellation still
         * owns TERM, grace, KILL, exact reap, and terminalization. */
        if (poll.terminal) break;
    }
    pthread_mutex_lock(slot->state_lock);
    receipt->term_sent = slot->term_sent;
    receipt->runtime_error = slot->runtime_error;
    int terminal = slot->state == 2;
    pthread_mutex_unlock(slot->state_lock);
    owned_token_release(slot);
    return terminal && receipt->runtime_error == 0;
#endif
}

#if defined(RT_PROCESS_OWNED_TESTING) || defined(RT_PROCESS_OWNED_CORE_ONLY)
bool rt_process_owned_test_legacy_cancel_v2(RtOwnedProcessTokenV2 token) {
    RtOwnedSlot* slot = owned_token_acquire(token, NULL);
    if (!slot) return false;
    pthread_mutex_lock(slot->state_lock);
    uint64_t generation = slot->generation, identity = slot->start_identity;
    int64_t pid = slot->pid;
    uint32_t index = (uint32_t)(slot - rt_owned_slots);
    pthread_mutex_unlock(slot->state_lock);
    owned_token_release(slot);
    RtOwnedProcessCancelReceipt receipt;
    return rt_process_owned_cancel(index, generation, pid, identity, &receipt);
}
#endif

bool rt_process_owned_result_v2(RtOwnedProcessTokenV2 token,
                                RtOwnedProcessResultV2* result) {
    if (!result) return false;
    memset(result, 0, sizeof(*result));
    result->version = RT_OWNED_PROCESS_ASYNC_VERSION;
#ifndef __linux__
    (void)token; result->runtime_error = ENOTSUP; return false;
#else
    RtOwnedSlot* slot = owned_token_acquire(token, NULL);
    if (!slot) { result->runtime_error = ESTALE; return false; }
    pthread_mutex_lock(slot->state_lock);
    if (slot->state != 2) {
        pthread_mutex_unlock(slot->state_lock); owned_token_release(slot);
        result->runtime_error = EAGAIN; return false;
    }
    owned_async_fill_result(slot, result);
    pthread_mutex_unlock(slot->state_lock); owned_token_release(slot);
    return result->runtime_error == 0;
#endif
}

bool rt_process_owned_collect_v2(RtOwnedProcessTokenV2 token,
                                 RtOwnedProcessResultV2* result) {
    if (!result) return false;
    memset(result, 0, sizeof(*result));
    result->version = RT_OWNED_PROCESS_ASYNC_VERSION;
#ifndef __linux__
    (void)token; result->runtime_error = ENOTSUP; return false;
#else
    pthread_mutex_lock(&rt_owned_lock);
    uint32_t index = 0; RtOwnedSlot* slot = owned_find_token_locked(token, &index);
    if (!slot || slot->collecting || slot->op_refs != 0) {
        pthread_mutex_unlock(&rt_owned_lock);
        result->runtime_error = slot ? EBUSY : ESTALE; return false;
    }
    slot->collecting = 1;
    pthread_mutex_unlock(&rt_owned_lock);
    pthread_mutex_lock(slot->state_lock);
    /* A terminal runtime error is result data, not a reason to strand the
     * lease.  Once the owner has consumed all retained output, collect must
     * release the capture, pidfd, and registry slot exactly as it does for a
     * clean exit; its false return and copied result preserve that error for
     * the caller. */
    if (slot->state != 2 ||
        slot->stdout_delivered != slot->stdout_kept ||
        slot->stderr_delivered != slot->stderr_kept) {
        result->runtime_error = slot->state != 2 ? EAGAIN :
            EBUSY;
        pthread_mutex_unlock(slot->state_lock);
        pthread_mutex_lock(&rt_owned_lock); slot->collecting = 0; pthread_mutex_unlock(&rt_owned_lock);
        return false;
    }
    owned_async_fill_result(slot, result);
    RT_OWNED_HOST_FREE(slot->retained); slot->retained = NULL;
    int pidfd = slot->pidfd;
    if (pidfd >= 0) { close(pidfd); slot->pidfd = -1; }
    /* `collecting` was set under the registry before this slot lock.  Drop the
     * slot lock before returning to the registry so every dual-lock path is
     * registry -> slot, never the inverse.  Collecting excludes new tokens
     * and the earlier op-ref check excludes already-running operations. */
    pthread_mutex_t* keep_lock = slot->state_lock;
    pthread_mutex_unlock(keep_lock);
    pthread_mutex_lock(&rt_owned_lock);
    uint64_t keep_generation = slot->generation; int keep_retired = slot->retired;
    memset(slot, 0, sizeof(*slot)); slot->generation = keep_generation;
    slot->retired = keep_retired; slot->state_lock = keep_lock;
    pthread_mutex_unlock(&rt_owned_lock);
    (void)pidfd;
    (void)index;
    return result->runtime_error == 0;
#endif
}

bool rt_process_run_owned_bounded(const char* cmd, const char* const* argv,
                                  int64_t timeout_ms, uint64_t max_output_bytes,
                                  char* out, uint64_t out_cap,
                                  char* err, uint64_t err_cap,
                                  RtOwnedProcessReceipt* receipt) {
    if (!receipt) return false;
    memset(receipt, 0, sizeof(*receipt));
    receipt->version = RT_OWNED_PROCESS_RECEIPT_VERSION;
    receipt->exit_code = -1;
    if (!cmd || !argv || timeout_ms <= 0 ||
        (out_cap && !out) || (err_cap && !err)) {
        receipt->runtime_error = EINVAL;
        return false;
    }
    if (out_cap) out[0] = '\0';
    if (err_cap) err[0] = '\0';
#ifndef __linux__
    receipt->runtime_error = ENOTSUP;
    return false;
#else
    RtOwnedCleanup cleanup = {0, 0, 0, 0, -1, -1, -1, 0, 0};
    int old_cancel_state = 0;
    (void)pthread_setcancelstate(PTHREAD_CANCEL_DISABLE, &old_cancel_state);
    if (!owned_reserve(&cleanup.slot, &cleanup.generation)) {
        receipt->runtime_error = EAGAIN;
        (void)pthread_setcancelstate(old_cancel_state, NULL);
        return false;
    }
    cleanup.reserved = 1;
    receipt->slot = cleanup.slot; receipt->generation = cleanup.generation;
    pthread_cleanup_push(owned_cleanup, &cleanup);

    int out_pipe[2] = {-1, -1}, err_pipe[2] = {-1, -1};
    if (pipe(out_pipe) != 0 || pipe(err_pipe) != 0) {
        receipt->runtime_error = errno;
        if (out_pipe[0] >= 0) { close(out_pipe[0]); close(out_pipe[1]); }
        if (err_pipe[0] >= 0) { close(err_pipe[0]); close(err_pipe[1]); }
        goto done;
    }
    pid_t pid = fork();
    if (pid == 0) {
        (void)setpgid(0, 0);
        close(out_pipe[0]); close(err_pipe[0]);
        if (dup2(out_pipe[1], STDOUT_FILENO) < 0 || dup2(err_pipe[1], STDERR_FILENO) < 0) _exit(126);
        close(out_pipe[1]); close(err_pipe[1]);
        execvp(cmd, (char* const*)argv);
        _exit(127);
    }
    close(out_pipe[1]); close(err_pipe[1]);
    cleanup.out_fd = out_pipe[0]; cleanup.err_fd = err_pipe[0];
    if (pid < 0) { receipt->runtime_error = errno; goto done; }
    cleanup.pid = pid; cleanup.pgid = pid;

    if (setpgid(pid, pid) != 0 && errno != EACCES && errno != EEXIST) {
        receipt->runtime_error = errno; goto done;
    }
    pid_t actual_pgid = getpgid(pid);
    if (actual_pgid != pid) { receipt->runtime_error = actual_pgid < 0 ? errno : EPERM; goto done; }
    cleanup.pidfd = owned_pidfd_open(pid);
    if (cleanup.pidfd < 0) { receipt->runtime_error = errno ? errno : ENOTSUP; goto done; }
    uint64_t identity = owned_start_identity(pid);
    if (identity == 0) { receipt->runtime_error = ESRCH; goto done; }
    if (!owned_set_nonblocking(cleanup.out_fd) || !owned_set_nonblocking(cleanup.err_fd)) {
        receipt->runtime_error = errno ? errno : EIO; goto done;
    }

    pthread_mutex_lock(&rt_owned_lock);
    rt_owned_slots[cleanup.slot].pid = pid;
    rt_owned_slots[cleanup.slot].pgid = pid;
    rt_owned_slots[cleanup.slot].pidfd = cleanup.pidfd;
    rt_owned_slots[cleanup.slot].start_identity = identity;
    pthread_mutex_unlock(&rt_owned_lock);
    receipt->pid = pid; receipt->process_group_id = pid; receipt->start_identity = identity;

    /* From publication onward every cancellation point is protected by the
     * cleanup handler, which kills/reaps the group and releases the slot. */
    (void)pthread_setcancelstate(old_cancel_state, NULL);

    int out_open = 1, err_open = 1, child_done = 0, status = 0;
    int64_t started = owned_now_ms(), term_at = -1, drain_deadline = -1;
    if (started < 0) { receipt->runtime_error = errno ? errno : EIO; goto done; }
    while (!child_done || out_open || err_open) {
        int64_t now = owned_now_ms();
        if (now < 0) { receipt->runtime_error = errno ? errno : EIO; break; }
        if (child_done && drain_deadline >= 0 && now >= drain_deadline) {
            if (out_open) { close(cleanup.out_fd); cleanup.out_fd = -1; out_open = 0; }
            if (err_open) { close(cleanup.err_fd); cleanup.err_fd = -1; err_open = 0; }
            break;
        }
        struct pollfd pfds[2]; nfds_t count = 0;
        int out_index = -1, err_index = -1;
        if (out_open) { out_index = (int)count; pfds[count++] = (struct pollfd){cleanup.out_fd, POLLIN | POLLHUP | POLLERR, 0}; }
        if (err_open) { err_index = (int)count; pfds[count++] = (struct pollfd){cleanup.err_fd, POLLIN | POLLHUP | POLLERR, 0}; }
        int poll_ms = 10;
        if (child_done && drain_deadline - now < poll_ms) poll_ms = (int)(drain_deadline - now);
        int poll_rc;
        do poll_rc = poll(pfds, count, poll_ms); while (poll_rc < 0 && errno == EINTR);
        if (poll_rc < 0) { receipt->runtime_error = errno; break; }
        if (out_index >= 0 && (pfds[out_index].revents & (POLLIN | POLLHUP | POLLERR)))
            owned_capture(cleanup.out_fd, out, out_cap, max_output_bytes,
                          &receipt->stdout_bytes_seen, &receipt->stdout_bytes_kept,
                          &receipt->stdout_truncated, &out_open);
        if (!out_open) cleanup.out_fd = -1;
        if (err_index >= 0 && (pfds[err_index].revents & (POLLIN | POLLHUP | POLLERR)))
            owned_capture(cleanup.err_fd, err, err_cap, max_output_bytes,
                          &receipt->stderr_bytes_seen, &receipt->stderr_bytes_kept,
                          &receipt->stderr_truncated, &err_open);
        if (!err_open) cleanup.err_fd = -1;

        if (!child_done) {
            siginfo_t info;
            memset(&info, 0, sizeof(info));
            int wait_rc;
            do wait_rc = waitid(P_PID, (id_t)pid, &info, WEXITED | WNOHANG | WNOWAIT);
            while (wait_rc < 0 && errno == EINTR);
            if (wait_rc == 0 && info.si_pid == pid) {
                /* Keep the leader unreaped while terminating descendants: the
                 * retained child pins pgid against reuse. */
                if (!owned_signal_group_pinned(pid, pid, cleanup.pidfd, SIGKILL)) {
                    receipt->runtime_error = ESTALE;
                    break;
                }
                pid_t waited;
                do waited = waitpid(pid, &status, 0); while (waited < 0 && errno == EINTR);
                if (waited != pid) { receipt->runtime_error = errno ? errno : ECHILD; break; }
                child_done = 1; cleanup.reaped = 1; receipt->reaped = 1;
                drain_deadline = owned_add_sat((uint64_t)owned_now_ms(), RT_OWNED_POST_REAP_DRAIN_MS);
            } else if (wait_rc < 0) {
                receipt->runtime_error = errno; break;
            }
        }
        now = owned_now_ms();
        int cancel_requested = 0;
        pthread_mutex_lock(&rt_owned_lock);
        if (cleanup.slot < RT_OWNED_PROCESS_SLOTS &&
            rt_owned_slots[cleanup.slot].generation == cleanup.generation)
            cancel_requested = rt_owned_slots[cleanup.slot].cancel_requested;
        pthread_mutex_unlock(&rt_owned_lock);
        if (!child_done && (cancel_requested || (timeout_ms > 0 && now - started >= timeout_ms)) && !receipt->term_sent) {
            receipt->timed_out = cancel_requested ? 0 : 1;
            receipt->identity_revalidated = owned_pidfd_live(cleanup.pidfd) && getpgid(pid) == pid;
            if (!receipt->identity_revalidated || !owned_signal_group(pid, pid, cleanup.pidfd, SIGTERM)) {
                receipt->runtime_error = ESTALE; break;
            }
            receipt->term_sent = 1; term_at = now;
        }
        if (!child_done && receipt->term_sent && now - term_at >= RT_OWNED_TERM_GRACE_MS && !receipt->kill_sent) {
            if (!owned_signal_group(pid, pid, cleanup.pidfd, SIGKILL)) { receipt->runtime_error = ESTALE; break; }
            receipt->kill_sent = 1;
        }
    }

    if (!cleanup.reaped) {
        (void)owned_signal_group(pid, pid, cleanup.pidfd, SIGKILL);
        pid_t waited;
        do waited = waitpid(pid, &status, 0); while (waited < 0 && errno == EINTR);
        if (waited == pid) { cleanup.reaped = 1; receipt->reaped = 1; }
        else if (receipt->runtime_error == 0) receipt->runtime_error = errno ? errno : ECHILD;
    }
    if (receipt->reaped) {
        if (WIFEXITED(status)) receipt->exit_code = WEXITSTATUS(status);
        else if (WIFSIGNALED(status)) receipt->exit_code = 128 + WTERMSIG(status);
    }

done:
    /* Prevent cancellation between manual cleanup and popping its handler. */
    (void)pthread_setcancelstate(PTHREAD_CANCEL_DISABLE, NULL);
    if (out_cap) out[receipt->stdout_bytes_kept < out_cap ? receipt->stdout_bytes_kept : out_cap - 1] = '\0';
    if (err_cap) err[receipt->stderr_bytes_kept < err_cap ? receipt->stderr_bytes_kept : err_cap - 1] = '\0';
    owned_cleanup(&cleanup);
    pthread_cleanup_pop(0);
    (void)pthread_setcancelstate(old_cancel_state, NULL);
    if (old_cancel_state == PTHREAD_CANCEL_ENABLE) pthread_testcancel();
    return receipt->runtime_error == 0;
#endif
}

/* Stable language ABI. Keep the policy receipt numeric and versioned so the
 * Simple facade can reject layouts it does not understand. */
#ifndef RT_PROCESS_OWNED_CORE_ONLY
int64_t* rt_process_run_owned_bounded_value(const char* cmd_data, uint64_t cmd_len, SplArray* args,
                                            int64_t timeout_ms,
                                            int64_t max_output_bytes) {
    if (!cmd_data || cmd_len > SIZE_MAX - 1 || timeout_ms < 0 || max_output_bytes < 0) return NULL;
    if (!args || memchr(cmd_data, '\0', (size_t)cmd_len) != NULL) return NULL;
    if (timeout_ms > RT_OWNED_ABI_MAX_TIMEOUT_MS) timeout_ms = RT_OWNED_ABI_MAX_TIMEOUT_MS;
    if (max_output_bytes > RT_OWNED_ABI_MAX_OUTPUT_BYTES) max_output_bytes = RT_OWNED_ABI_MAX_OUTPUT_BYTES;
    char* cmd = (char*)RT_OWNED_HOST_MALLOC((size_t)cmd_len + 1);
    if (!cmd) return NULL;
    memcpy(cmd, cmd_data, (size_t)cmd_len); cmd[cmd_len] = '\0';
    int64_t argc = rt_array_len(args);
    if (argc < 0 || (uint64_t)argc > SIZE_MAX / sizeof(char*) - 2) { RT_OWNED_HOST_FREE(cmd); return NULL; }
    char** argv = (char**)RT_OWNED_HOST_CALLOC((size_t)argc + 2, sizeof(char*));
    char* out = NULL;
    char* err = NULL;
    SplArray* fields = NULL;
    int64_t* tuple = NULL;
    int64_t stdout_value = 0;
    int64_t stderr_value = 0;
    if (!argv) goto fail;
    argv[0] = cmd;
    for (int64_t i = 0; i < argc; i++) {
        int64_t value = rt_array_get(args, i);
        int64_t arg_len = rt_string_len(value);
        const uint8_t* arg_data = rt_string_data(value);
        if (arg_len < 0 || !arg_data || (uint64_t)arg_len > SIZE_MAX - 1 ||
            memchr(arg_data, '\0', (size_t)arg_len) != NULL) {
            goto fail;
        }
        argv[i + 1] = (char*)RT_OWNED_HOST_MALLOC((size_t)arg_len + 1);
        if (!argv[i + 1]) goto fail;
        memcpy(argv[i + 1], arg_data, (size_t)arg_len);
        argv[i + 1][arg_len] = '\0';
    }

    uint64_t limit = (uint64_t)max_output_bytes;
    if (limit == UINT64_MAX || limit > SIZE_MAX - 1) goto fail;
    size_t capacity = (size_t)limit + 1;
    out = (char*)RT_OWNED_HOST_MALLOC(capacity);
    err = (char*)RT_OWNED_HOST_MALLOC(capacity);
    if (!out || !err) goto fail;

    RtOwnedProcessReceipt receipt;
    bool ok = rt_process_run_owned_bounded(cmd, (const char* const*)argv, timeout_ms, limit,
                                            out, capacity, err, capacity, &receipt);
    fields = rt_array_new(19);
    if (!fields) goto fail;
#define OWNED_PUSH(value) do { if (!rt_array_push(fields, rt_value_int((int64_t)(value)))) goto fail; } while (0)
    OWNED_PUSH(receipt.version); OWNED_PUSH(receipt.slot); OWNED_PUSH(receipt.generation);
    OWNED_PUSH(receipt.pid); OWNED_PUSH(receipt.process_group_id); OWNED_PUSH(receipt.start_identity);
    OWNED_PUSH(receipt.stdout_bytes_seen); OWNED_PUSH(receipt.stderr_bytes_seen);
    OWNED_PUSH(receipt.stdout_bytes_kept); OWNED_PUSH(receipt.stderr_bytes_kept);
    OWNED_PUSH(receipt.exit_code); OWNED_PUSH(receipt.timed_out); OWNED_PUSH(receipt.term_sent);
    OWNED_PUSH(receipt.kill_sent); OWNED_PUSH(receipt.identity_revalidated); OWNED_PUSH(receipt.reaped);
    OWNED_PUSH(receipt.stdout_truncated); OWNED_PUSH(receipt.stderr_truncated);
    OWNED_PUSH(receipt.runtime_error);
#undef OWNED_PUSH
    (void)ok; /* runtime_error carries provider failure without hiding output. */

    stdout_value = rt_string_new((const uint8_t*)out, receipt.stdout_bytes_kept);
    stderr_value = rt_string_new((const uint8_t*)err, receipt.stderr_bytes_kept);
    if (!stdout_value || !stderr_value) goto fail;
    tuple = (int64_t*)rt_alloc(3 * (int64_t)sizeof(int64_t));
    if (!tuple) goto fail;
    tuple[0] = stdout_value;
    tuple[1] = stderr_value;
    tuple[2] = (int64_t)(uintptr_t)fields;
    for (int64_t i = 1; i <= argc; i++) RT_OWNED_HOST_FREE(argv[i]);
    RT_OWNED_HOST_FREE(argv); RT_OWNED_HOST_FREE(cmd);
    RT_OWNED_HOST_FREE(out); RT_OWNED_HOST_FREE(err);
    return tuple;

fail:
    if (argv) {
        for (int64_t i = 1; i <= argc; i++) RT_OWNED_HOST_FREE(argv[i]);
    }
    RT_OWNED_HOST_FREE(argv); RT_OWNED_HOST_FREE(cmd);
    RT_OWNED_HOST_FREE(out); RT_OWNED_HOST_FREE(err);
    if (stdout_value) (void)RT_OWNED_FREE_VALUE(stdout_value);
    if (stderr_value) (void)RT_OWNED_FREE_VALUE(stderr_value);
    if (fields) rt_array_free(fields);
    if (tuple) rt_free(tuple);
    return NULL;
}
#endif

#else

#include <errno.h>
#include <string.h>

bool rt_process_owned_start_v2(const char* cmd, const char* const* argv,
                               int64_t timeout_ms, int64_t term_grace_ms,
                               uint64_t max_output_bytes,
                               RtOwnedProcessTokenV2* token,
                               RtOwnedProcessStartReceiptV2* receipt) {
    (void)cmd; (void)argv; (void)timeout_ms; (void)term_grace_ms; (void)max_output_bytes;
    if (!token || !receipt) return false;
    memset(token, 0, sizeof(*token)); memset(receipt, 0, sizeof(*receipt));
    receipt->version = RT_OWNED_PROCESS_ASYNC_VERSION; receipt->runtime_error = ENOTSUP;
    return false;
}

bool rt_process_owned_poll_v2(RtOwnedProcessTokenV2 token, int64_t wait_ms,
                              char* out, uint64_t out_cap, char* err,
                              uint64_t err_cap,
                              RtOwnedProcessPollReceiptV2* receipt) {
    (void)token; (void)wait_ms; (void)out; (void)out_cap; (void)err; (void)err_cap;
    if (!receipt) return false;
    memset(receipt, 0, sizeof(*receipt));
    receipt->version = RT_OWNED_PROCESS_ASYNC_VERSION; receipt->runtime_error = ENOTSUP;
    return false;
}

bool rt_process_owned_cancel_v2(RtOwnedProcessTokenV2 token,
                                RtOwnedProcessCancelReceipt* receipt) {
    (void)token;
    if (!receipt) return false;
    memset(receipt, 0, sizeof(*receipt));
    receipt->version = RT_OWNED_PROCESS_ASYNC_VERSION; receipt->runtime_error = ENOTSUP;
    return false;
}

bool rt_process_owned_result_v2(RtOwnedProcessTokenV2 token,
                                RtOwnedProcessResultV2* result) {
    (void)token;
    if (!result) return false;
    memset(result, 0, sizeof(*result));
    result->version = RT_OWNED_PROCESS_ASYNC_VERSION; result->exit_code = -1; result->runtime_error = ENOTSUP;
    return false;
}

bool rt_process_owned_collect_v2(RtOwnedProcessTokenV2 token,
                                 RtOwnedProcessResultV2* result) {
    return rt_process_owned_result_v2(token, result);
}

bool rt_process_run_owned_bounded(const char* cmd, const char* const* argv,
                                  int64_t timeout_ms, uint64_t max_output_bytes,
                                  char* out, uint64_t out_cap, char* err,
                                  uint64_t err_cap, RtOwnedProcessReceipt* receipt) {
    (void)cmd; (void)argv; (void)timeout_ms; (void)max_output_bytes;
    (void)out; (void)out_cap; (void)err; (void)err_cap;
    if (!receipt) return false;
    memset(receipt, 0, sizeof(*receipt));
    receipt->version = RT_OWNED_PROCESS_RECEIPT_VERSION;
    receipt->exit_code = -1;
    receipt->runtime_error = ENOTSUP;
    return false;
}

bool rt_process_owned_terminate(int64_t pid, uint64_t identity) {
    (void)pid; (void)identity;
    return false;
}

bool rt_process_owned_cancel(uint64_t slot, uint64_t generation, int64_t pid,
                             uint64_t identity, RtOwnedProcessCancelReceipt* receipt) {
    (void)slot; (void)generation; (void)pid; (void)identity;
    if (!receipt) return false;
    memset(receipt, 0, sizeof(*receipt));
    receipt->version = RT_OWNED_PROCESS_CANCEL_RECEIPT_VERSION;
    receipt->pid = pid;
    receipt->start_identity = identity;
    receipt->runtime_error = ENOTSUP;
    return false;
}

bool rt_process_owned_cancel_value(uint64_t slot, uint64_t generation,
                                   int64_t pid, uint64_t identity) {
    (void)slot; (void)generation; (void)pid; (void)identity;
    return false;
}


#ifndef RT_PROCESS_OWNED_CORE_ONLY
int64_t* rt_process_run_owned_bounded_value(const char* cmd, uint64_t cmd_len, SplArray* args,
                                            int64_t timeout_ms,
                                            int64_t max_output_bytes) {
    (void)cmd; (void)cmd_len; (void)args; (void)timeout_ms; (void)max_output_bytes;
    SplArray* fields = rt_array_new(19);
    if (!fields) return NULL;
    const int64_t values[19] = {
        RT_OWNED_PROCESS_RECEIPT_VERSION, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        -1, 0, 0, 0, 0, 0, 0, 0, ENOTSUP,
    };
    for (int i = 0; i < 19; i++) {
        if (!rt_array_push(fields, rt_value_int(values[i]))) {
            rt_array_free(fields);
            return NULL;
        }
    }
    int64_t* tuple = (int64_t*)rt_alloc(3 * (int64_t)sizeof(int64_t));
    if (!tuple) { rt_array_free(fields); return NULL; }
    tuple[0] = rt_string_new((const uint8_t*)"", 0);
    tuple[1] = rt_string_new((const uint8_t*)"", 0);
    if (!tuple[0] || !tuple[1]) {
        if (tuple[0]) (void)RT_OWNED_FREE_VALUE(tuple[0]);
        if (tuple[1]) (void)RT_OWNED_FREE_VALUE(tuple[1]);
        rt_array_free(fields); rt_free(tuple);
        return NULL;
    }
    tuple[2] = (int64_t)(uintptr_t)fields;
    return tuple;
}
#endif

#endif

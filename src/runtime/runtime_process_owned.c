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
#include <sys/resource.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#ifdef __linux__
#include <dirent.h>
#include <ctype.h>
#include <sys/syscall.h>
#endif

#define RT_OWNED_PROCESS_SLOTS 16
#define RT_OWNED_TERM_GRACE_MS 100
#define RT_OWNED_POST_REAP_DRAIN_MS 100
#define RT_OWNED_DRAIN_QUANTUM (64U * 1024U)
#define RT_OWNED_ABI_MAX_TIMEOUT_MS 3600000
#define RT_OWNED_ABI_MAX_OUTPUT_BYTES (16U * 1024U * 1024U)

#ifdef __linux__
typedef struct RtOwnedTreeSample {
    int64_t charge_bytes;
    int64_t io_read_bytes;
    int64_t io_write_bytes;
    int64_t pids;
} RtOwnedTreeSample;

static int64_t owned_proc_counter(pid_t member, const char* file, const char* key,
                                  uint64_t multiplier) {
    char path[96];
    int path_len = snprintf(path, sizeof(path), "/proc/%ld/%s", (long)member, file);
    if (path_len <= 0 || (size_t)path_len >= sizeof(path)) return 0;
    FILE* stream = fopen(path, "r");
    if (!stream) return 0;
    char line[256];
    int64_t value = 0;
    size_t key_len = strlen(key);
    while (fgets(line, sizeof(line), stream)) {
        if (strncmp(line, key, key_len) == 0) {
            unsigned long long parsed = 0;
            if (sscanf(line + key_len, "%llu", &parsed) == 1 &&
                multiplier > 0 && parsed <= (unsigned long long)INT64_MAX / multiplier)
                value = (int64_t)(parsed * multiplier);
            break;
        }
    }
    fclose(stream);
    return value;
}

static RtOwnedTreeSample owned_sample_process_group(pid_t pgid) {
    RtOwnedTreeSample sample = {0, 0, 0, 0};
    DIR* proc = opendir("/proc");
    if (!proc) return sample;
    struct dirent* entry;
    while ((entry = readdir(proc)) != NULL) {
        if (!isdigit((unsigned char)entry->d_name[0])) continue;
        char* end = NULL;
        long raw_pid = strtol(entry->d_name, &end, 10);
        if (!end || *end != '\0' || raw_pid <= 0 || raw_pid > INT_MAX) continue;
        pid_t member = (pid_t)raw_pid;
        if (getpgid(member) != pgid) continue;
        sample.pids++;
        sample.charge_bytes += owned_proc_counter(member, "status", "VmRSS:", 1024);
        sample.io_read_bytes += owned_proc_counter(member, "io", "read_bytes:", 1);
        sample.io_write_bytes += owned_proc_counter(member, "io", "write_bytes:", 1);
    }
    closedir(proc);
    return sample;
}
#endif

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
    int in_fd;
    int in_open;
    uint8_t* input;
    uint64_t input_len;
    uint64_t input_written;
    uint8_t input_sha256[32];
    int input_contract_v3;
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
    struct rusage child_usage;
    int child_usage_available;
    int retired;
    int op_refs;
    int collecting;
    pthread_mutex_t* state_lock;
} RtOwnedSlot;

static uint32_t owned_sha256_rotr(uint32_t v, unsigned s) { return (v >> s) | (v << (32 - s)); }
static void owned_sha256_block(uint32_t st[8], const uint8_t b[64]) {
    static const uint32_t k[64] = {
        0x428a2f98u,0x71374491u,0xb5c0fbcfu,0xe9b5dba5u,0x3956c25bu,0x59f111f1u,0x923f82a4u,0xab1c5ed5u,
        0xd807aa98u,0x12835b01u,0x243185beu,0x550c7dc3u,0x72be5d74u,0x80deb1feu,0x9bdc06a7u,0xc19bf174u,
        0xe49b69c1u,0xefbe4786u,0x0fc19dc6u,0x240ca1ccu,0x2de92c6fu,0x4a7484aau,0x5cb0a9dcu,0x76f988dau,
        0x983e5152u,0xa831c66du,0xb00327c8u,0xbf597fc7u,0xc6e00bf3u,0xd5a79147u,0x06ca6351u,0x14292967u,
        0x27b70a85u,0x2e1b2138u,0x4d2c6dfcu,0x53380d13u,0x650a7354u,0x766a0abbu,0x81c2c92eu,0x92722c85u,
        0xa2bfe8a1u,0xa81a664bu,0xc24b8b70u,0xc76c51a3u,0xd192e819u,0xd6990624u,0xf40e3585u,0x106aa070u,
        0x19a4c116u,0x1e376c08u,0x2748774cu,0x34b0bcb5u,0x391c0cb3u,0x4ed8aa4au,0x5b9cca4fu,0x682e6ff3u,
        0x748f82eeu,0x78a5636fu,0x84c87814u,0x8cc70208u,0x90befffau,0xa4506cebu,0xbef9a3f7u,0xc67178f2u };
    uint32_t w[64];
    for (int i=0;i<16;i++) w[i]=((uint32_t)b[i*4]<<24)|((uint32_t)b[i*4+1]<<16)|((uint32_t)b[i*4+2]<<8)|b[i*4+3];
    for (int i=16;i<64;i++) { uint32_t a=owned_sha256_rotr(w[i-15],7)^owned_sha256_rotr(w[i-15],18)^(w[i-15]>>3); uint32_t z=owned_sha256_rotr(w[i-2],17)^owned_sha256_rotr(w[i-2],19)^(w[i-2]>>10); w[i]=w[i-16]+a+w[i-7]+z; }
    uint32_t a=st[0],bb=st[1],c=st[2],d=st[3],e=st[4],f=st[5],g=st[6],h=st[7];
    for (int i=0;i<64;i++) { uint32_t s1=owned_sha256_rotr(e,6)^owned_sha256_rotr(e,11)^owned_sha256_rotr(e,25); uint32_t t1=h+s1+((e&f)^((~e)&g))+k[i]+w[i]; uint32_t s0=owned_sha256_rotr(a,2)^owned_sha256_rotr(a,13)^owned_sha256_rotr(a,22); uint32_t t2=s0+((a&bb)^(a&c)^(bb&c)); h=g;g=f;f=e;e=d+t1;d=c;c=bb;bb=a;a=t1+t2; }
    st[0]+=a;st[1]+=bb;st[2]+=c;st[3]+=d;st[4]+=e;st[5]+=f;st[6]+=g;st[7]+=h;
}
static void owned_sha256(const uint8_t* msg, size_t len, uint8_t out[32]) {
    uint32_t st[8]={0x6a09e667u,0xbb67ae85u,0x3c6ef372u,0xa54ff53au,0x510e527fu,0x9b05688cu,0x1f83d9abu,0x5be0cd19u}; size_t i=0;
    for (;i+64<=len;i+=64) owned_sha256_block(st,msg+i);
    uint8_t tail[128]={0}; size_t rem=len-i; if(rem) memcpy(tail,msg+i,rem); tail[rem]=0x80; size_t total=rem+9<=64?64:128; uint64_t bits=(uint64_t)len*8u;
    for(int j=0;j<8;j++) tail[total-1-j]=(uint8_t)(bits>>(8*j));
    owned_sha256_block(st,tail);
    if(total==128) owned_sha256_block(st,tail+64);
    for(int j=0;j<8;j++){out[j*4]=(uint8_t)(st[j]>>24);out[j*4+1]=(uint8_t)(st[j]>>16);out[j*4+2]=(uint8_t)(st[j]>>8);out[j*4+3]=(uint8_t)st[j];}
}

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

static int64_t owned_timeval_ms(struct timeval value) {
    if (value.tv_sec > INT64_MAX / 1000) return INT64_MAX;
    return (int64_t)value.tv_sec * 1000 + value.tv_usec / 1000;
}

static int64_t owned_direct_child_rss_bytes(const struct rusage* usage) {
#if defined(__APPLE__)
    return usage->ru_maxrss < 0 ? 0 : (int64_t)usage->ru_maxrss;
#else
    if (usage->ru_maxrss <= 0) return 0;
    if ((uint64_t)usage->ru_maxrss > (uint64_t)INT64_MAX / 1024U) return INT64_MAX;
    return (int64_t)usage->ru_maxrss * 1024;
#endif
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

static int owned_pipe_cloexec(int fds[2]) {
#if defined(__linux__) && defined(SYS_pipe2)
    if (syscall(SYS_pipe2, fds, O_CLOEXEC) != 0) return -1;
#else
    if (pipe(fds) != 0) return -1;
    if (fcntl(fds[0], F_SETFD, FD_CLOEXEC) != 0 ||
        fcntl(fds[1], F_SETFD, FD_CLOEXEC) != 0) {
        int saved = errno;
        close(fds[0]); close(fds[1]);
        fds[0] = -1; fds[1] = -1;
        errno = saved;
        return -1;
    }
#endif
    for (int i = 0; i < 2; i++) {
        if (fds[i] <= STDERR_FILENO) {
            int moved = fcntl(fds[i], F_DUPFD_CLOEXEC, STDERR_FILENO + 1);
            if (moved < 0) {
                int saved = errno;
                close(fds[0]); close(fds[1]);
                fds[0] = -1; fds[1] = -1; errno = saved; return -1;
            }
            close(fds[i]); fds[i] = moved;
        }
    }
    return 0;
}

static int owned_child_close_inherited_except(int keep_fd) {
#if defined(__linux__) && defined(SYS_close_range)
    if (keep_fd > STDERR_FILENO + 1 &&
        syscall(SYS_close_range, (unsigned int)(STDERR_FILENO + 1),
                (unsigned int)keep_fd - 1U, 0U) != 0) return 0;
    if (syscall(SYS_close_range, (unsigned int)keep_fd + 1U, ~0U, 0U) != 0)
        return 0;
    return 1;
#else
    (void)keep_fd;
    return 0;
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

static void owned_async_close_input(RtOwnedSlot* slot) {
    if (slot->in_open) { close(slot->in_fd); slot->in_open = 0; slot->in_fd = -1; }
    RT_OWNED_HOST_FREE(slot->input); slot->input = NULL;
}

static ssize_t owned_write_no_sigpipe(int fd, const uint8_t* data, size_t len) {
    sigset_t block, prior;
    sigemptyset(&block); sigaddset(&block, SIGPIPE);
    if (pthread_sigmask(SIG_BLOCK, &block, &prior) != 0) { errno = EIO; return -1; }
    ssize_t result = write(fd, data, len);
    int saved = errno;
    if (result < 0 && saved == EPIPE && !sigismember(&prior, SIGPIPE)) {
        struct timespec zero = {0, 0};
        while (sigtimedwait(&block, NULL, &zero) < 0 && errno == EINTR) {}
    }
    (void)pthread_sigmask(SIG_SETMASK, &prior, NULL);
    errno = saved;
    return result;
}

static void owned_async_write_input(RtOwnedSlot* slot) {
    if (!slot->in_open) return;
    uint64_t budget = RT_OWNED_DRAIN_QUANTUM;
    while (slot->input_written < slot->input_len && budget > 0) {
        size_t remaining = (size_t)(slot->input_len - slot->input_written);
        if (remaining > budget) remaining = (size_t)budget;
        ssize_t n = owned_write_no_sigpipe(
            slot->in_fd, slot->input + slot->input_written, remaining);
        if (n > 0) {
            slot->input_written += (uint64_t)n;
            budget -= (uint64_t)n;
            continue;
        }
        if (n < 0 && errno == EINTR) continue;
        if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) return;
        if (slot->runtime_error == 0) slot->runtime_error = errno ? errno : EIO;
        owned_async_close_input(slot); return;
    }
    if (slot->input_written == slot->input_len) owned_async_close_input(slot);
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
static uint64_t owned_async_deliver(RtOwnedSlot* slot, int stream, char* dst,
                                    uint64_t cap) {
    if (cap) dst[0] = '\0';
    if (!dst || cap <= 1) return 0;
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
    return copied;
}

static void owned_async_fill_poll(const RtOwnedSlot* slot,
                                  RtOwnedProcessPollReceiptV2* receipt,
                                  uint64_t stdout_delivered,
                                  uint64_t stderr_delivered) {
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
    receipt->stdout_bytes_delivered = stdout_delivered;
    receipt->stderr_bytes_delivered = stderr_delivered;
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
        memset(&slot->child_usage, 0, sizeof(slot->child_usage));
        pid_t waited; do waited = wait4(slot->pid, &slot->status, 0, &slot->child_usage);
        while (waited < 0 && errno == EINTR);
        if (waited == slot->pid) {
            slot->child_usage_available = 1;
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

static bool owned_process_start(const char* cmd, const char* const* argv,
                               const uint8_t* input, uint64_t input_len, int pipe_stdin,
                               int pinned_executable_fd,
                               int64_t timeout_ms, int64_t term_grace_ms,
                               uint64_t max_output_bytes,
                               RtOwnedProcessTokenV2* token,
                               RtOwnedProcessStartReceiptV2* receipt) {
    if (!token || !receipt) { if (pinned_executable_fd >= 0) close(pinned_executable_fd); return false; }
    memset(token, 0, sizeof(*token)); memset(receipt, 0, sizeof(*receipt));
    receipt->version = RT_OWNED_PROCESS_ASYNC_VERSION;
#ifndef __linux__
    (void)cmd; (void)argv; (void)timeout_ms; (void)term_grace_ms; (void)max_output_bytes;
    if (pinned_executable_fd >= 0) close(pinned_executable_fd);
    receipt->runtime_error = ENOTSUP; return false;
#else
    if (!cmd || !argv || !argv[0] || timeout_ms <= 0 ||
        timeout_ms > RT_OWNED_ABI_MAX_TIMEOUT_MS || term_grace_ms < 0 ||
        term_grace_ms > 30000 || max_output_bytes > RT_OWNED_ABI_MAX_OUTPUT_BYTES) {
        receipt->runtime_error = EINVAL; if (pinned_executable_fd >= 0) close(pinned_executable_fd); return false;
    }
    uint8_t* input_copy = NULL; uint8_t input_sha256[32] = {0};
    if (pipe_stdin && input_len) {
        if (input_len > RT_OWNED_PROCESS_MAX_INPUT_BYTES || !input) { receipt->runtime_error = EINVAL; if (pinned_executable_fd >= 0) close(pinned_executable_fd); return false; }
        input_copy = (uint8_t*)RT_OWNED_HOST_MALLOC((size_t)input_len);
        if (!input_copy) { receipt->runtime_error = ENOMEM; if (pinned_executable_fd >= 0) close(pinned_executable_fd); return false; }
        memcpy(input_copy, input, (size_t)input_len);
    }
    if (pipe_stdin) owned_sha256(input_copy, (size_t)input_len, input_sha256);
    uint32_t index = 0; uint64_t generation = 0;
    if (!owned_reserve(&index, &generation)) {
        receipt->runtime_error = errno == EOVERFLOW ? EOVERFLOW : EAGAIN; RT_OWNED_HOST_FREE(input_copy); if (pinned_executable_fd >= 0) close(pinned_executable_fd); return false;
    }
    RtOwnedProcessTokenV2 minted = {0, 0};
    if (!owned_token_mint_install_reserved(index, generation, &minted)) {
        receipt->runtime_error = errno; owned_release(index, generation); RT_OWNED_HOST_FREE(input_copy); if (pinned_executable_fd >= 0) close(pinned_executable_fd); return false;
    }
    int out_pipe[2] = {-1, -1}, err_pipe[2] = {-1, -1}, in_pipe[2] = {-1, -1};
    if (owned_pipe_cloexec(out_pipe) != 0 || owned_pipe_cloexec(err_pipe) != 0 ||
        (pipe_stdin && owned_pipe_cloexec(in_pipe) != 0)) {
        int saved = errno;
        if (out_pipe[0] >= 0) { close(out_pipe[0]); close(out_pipe[1]); }
        if (err_pipe[0] >= 0) { close(err_pipe[0]); close(err_pipe[1]); }
        if (in_pipe[0] >= 0) { close(in_pipe[0]); close(in_pipe[1]); }
        receipt->runtime_error = saved; owned_release(index, generation); RT_OWNED_HOST_FREE(input_copy); if (pinned_executable_fd >= 0) close(pinned_executable_fd); return false;
    }
    pid_t pid = fork();
    if (pid == 0) {
        (void)setpgid(0, 0); close(out_pipe[0]); close(err_pipe[0]);
        if (pipe_stdin) close(in_pipe[1]);
        if (dup2(out_pipe[1], STDOUT_FILENO) < 0 || dup2(err_pipe[1], STDERR_FILENO) < 0 ||
            (pipe_stdin && dup2(in_pipe[0], STDIN_FILENO) < 0)) _exit(126);
        if (pipe_stdin && in_pipe[0] > STDERR_FILENO) close(in_pipe[0]);
        if (out_pipe[1] > STDERR_FILENO) close(out_pipe[1]);
        if (err_pipe[1] > STDERR_FILENO) close(err_pipe[1]);
        if (pinned_executable_fd >= 0) {
            char* pinned_environment[] = {(char*)"LANG=C", (char*)"LC_ALL=C", (char*)"TZ=UTC", (char*)"PATH=/nonexistent", NULL};
            if (chdir("/") != 0) _exit(127);
            if (!owned_child_close_inherited_except(pinned_executable_fd)) _exit(127);
            fexecve(pinned_executable_fd, (char* const*)argv, pinned_environment);
        } else execvp(cmd, (char* const*)argv);
        _exit(127);
    }
    close(out_pipe[1]); close(err_pipe[1]);
    if (pipe_stdin) close(in_pipe[0]);
    if (pinned_executable_fd >= 0) { close(pinned_executable_fd); pinned_executable_fd = -1; }
    if (pid < 0) {
        int saved = errno; close(out_pipe[0]); close(err_pipe[0]); if (pipe_stdin) close(in_pipe[1]);
        receipt->runtime_error = saved; owned_release(index, generation); RT_OWNED_HOST_FREE(input_copy); return false;
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
    if (!error && (!owned_set_nonblocking(out_pipe[0]) || !owned_set_nonblocking(err_pipe[0]) ||
                   (pipe_stdin && !owned_set_nonblocking(in_pipe[1])))) error = errno ? errno : EIO;
    int64_t started = !error ? owned_now_ms() : -1;
    if (!error && started < 0) error = errno ? errno : EIO;
    if (error) {
        if (pidfd >= 0) (void)owned_signal_group_pinned(pid, pid, pidfd, SIGKILL);
        else (void)kill(-pid, SIGKILL);
        int status; pid_t reaped; do reaped = waitpid(pid, &status, 0); while (reaped < 0 && errno == EINTR);
        (void)reaped;
        close(out_pipe[0]); close(err_pipe[0]); if (pipe_stdin) close(in_pipe[1]); if (pidfd >= 0) close(pidfd);
        RT_OWNED_HOST_FREE(retained); RT_OWNED_HOST_FREE(input_copy);
        receipt->runtime_error = error; owned_release(index, generation); return false;
    }
    pthread_mutex_lock(&rt_owned_lock);
    RtOwnedSlot* slot = &rt_owned_slots[index];
    if (slot->generation != generation || slot->pid != -1) {
        pthread_mutex_unlock(&rt_owned_lock);
        (void)owned_signal_group_pinned(pid, pid, pidfd, SIGKILL);
        int status; while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {}
        close(out_pipe[0]); close(err_pipe[0]); if (pipe_stdin) close(in_pipe[1]); close(pidfd);
        RT_OWNED_HOST_FREE(retained); RT_OWNED_HOST_FREE(input_copy);
        receipt->runtime_error = ESTALE; owned_release(index, generation); return false;
    }
    slot->pid = pid; slot->pgid = pid; slot->pidfd = pidfd; slot->start_identity = identity;
    slot->token_high = minted.high; slot->token_low = minted.low; slot->state = 1;
    slot->out_fd = out_pipe[0]; slot->err_fd = err_pipe[0]; slot->out_open = 1; slot->err_open = 1;
    slot->in_fd = pipe_stdin ? in_pipe[1] : -1; slot->in_open = pipe_stdin;
    slot->input = input_copy; slot->input_len = input_len; slot->input_written = 0;
    memcpy(slot->input_sha256, input_sha256, sizeof(slot->input_sha256));
    slot->input_contract_v3 = pipe_stdin;
    if (pipe_stdin && input_len == 0) { close(slot->in_fd); slot->in_fd = -1; slot->in_open = 0; }
    slot->started_ms = started; slot->timeout_ms = timeout_ms; slot->term_grace_ms = term_grace_ms;
    slot->term_at_ms = -1; slot->drain_deadline_ms = -1; slot->output_limit = max_output_bytes;
    slot->retained = retained;
    pthread_mutex_unlock(&rt_owned_lock);
    *token = minted; receipt->accepted = 1; return true;
#endif
}

bool rt_process_owned_start_v2(const char* cmd, const char* const* argv,
                               int64_t timeout_ms, int64_t term_grace_ms,
                               uint64_t max_output_bytes, RtOwnedProcessTokenV2* token,
                               RtOwnedProcessStartReceiptV2* receipt) {
    return owned_process_start(cmd, argv, NULL, 0, 0, -1, timeout_ms, term_grace_ms,
                               max_output_bytes, token, receipt);
}

bool rt_process_owned_start_v3(const char* cmd, const char* const* argv,
                               const uint8_t* input, uint64_t input_len,
                               int64_t timeout_ms, int64_t term_grace_ms,
                               uint64_t max_output_bytes, RtOwnedProcessTokenV2* token,
                               RtOwnedProcessStartReceiptV2* receipt) {
    if (input_len > RT_OWNED_PROCESS_MAX_INPUT_BYTES || (input_len && !input)) {
        if (token) memset(token, 0, sizeof(*token));
        if (receipt) { memset(receipt, 0, sizeof(*receipt)); receipt->version = RT_OWNED_PROCESS_INPUT_VERSION; receipt->runtime_error = EINVAL; }
        return false;
    }
    bool ok = owned_process_start(cmd, argv, input, input_len, 1, -1, timeout_ms,
                                  term_grace_ms, max_output_bytes, token, receipt);
    if (receipt) receipt->version = RT_OWNED_PROCESS_INPUT_VERSION;
    return ok;
}

bool rt_process_owned_start_pinned_v3(int64_t executable_handle,
                                      const char* const* argv,
                                      const uint8_t* input, uint64_t input_len,
                                      int64_t timeout_ms, int64_t term_grace_ms,
                                      uint64_t max_output_bytes,
                                      RtOwnedProcessTokenV2* token,
                                      RtOwnedProcessStartReceiptV2* receipt) {
    int private_fd = (int)rt_process_acquire_pinned_executable(executable_handle);
    if (private_fd < 0) {
        if (token) memset(token, 0, sizeof(*token));
        if (receipt) { memset(receipt, 0, sizeof(*receipt)); receipt->version = RT_OWNED_PROCESS_INPUT_VERSION; receipt->runtime_error = ESTALE; }
        return false;
    }
    bool ok = owned_process_start("simple-pinned-executable", argv, input, input_len, 1,
                                  private_fd, timeout_ms, term_grace_ms, max_output_bytes,
                                  token, receipt);
    if (receipt) receipt->version = RT_OWNED_PROCESS_INPUT_VERSION;
    return ok;
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
        uint64_t out_delivered = owned_async_deliver(slot, 0, out, out_cap);
        uint64_t err_delivered = owned_async_deliver(slot, 1, err, err_cap);
        owned_async_fill_poll(slot, receipt, out_delivered, err_delivered);
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
    struct pollfd pfds[3]; nfds_t count = 0; int oi = -1, ei = -1, ii = -1;
    if (slot->out_open) { oi = (int)count; pfds[count++] = (struct pollfd){slot->out_fd, POLLIN|POLLHUP|POLLERR, 0}; }
    if (slot->err_open) { ei = (int)count; pfds[count++] = (struct pollfd){slot->err_fd, POLLIN|POLLHUP|POLLERR, 0}; }
    if (slot->in_open) { ii = (int)count; pfds[count++] = (struct pollfd){slot->in_fd, POLLOUT|POLLHUP|POLLERR, 0}; }
    int rc; do rc = poll(pfds, count, (int)wait_ms); while (rc < 0 && errno == EINTR);
    if (rc < 0) slot->runtime_error = errno;
    uint64_t drain_budget = RT_OWNED_DRAIN_QUANTUM;
    if (oi >= 0 && (pfds[oi].revents & (POLLIN|POLLHUP|POLLERR)))
        owned_async_capture_one(slot, slot->out_fd, 0, &slot->out_open, &drain_budget);
    if (ei >= 0 && (pfds[ei].revents & (POLLIN|POLLHUP|POLLERR)))
        owned_async_capture_one(slot, slot->err_fd, 1, &slot->err_open, &drain_budget);
    if (ii >= 0 && (pfds[ii].revents & (POLLOUT|POLLHUP|POLLERR))) owned_async_write_input(slot);
    if (!slot->out_open) slot->out_fd = -1;
    if (!slot->err_open) slot->err_fd = -1;
    siginfo_t info; memset(&info, 0, sizeof(info));
    int wr = 0;
    if (!slot->reaped) {
        do wr = waitid(P_PID, (id_t)slot->pid, &info,
            WEXITED|WNOHANG|WNOWAIT); while (wr < 0 && errno == EINTR);
    }
    int64_t now = owned_now_ms();
    if (wr == 0 && info.si_pid == slot->pid && !slot->reaped) {
        /* waitid observed the same pidfd-pinned leader before exact reap. */
        slot->identity_revalidated = 1;
        (void)owned_signal_group_pinned(slot->pid, slot->pgid, slot->pidfd, SIGKILL);
        memset(&slot->child_usage, 0, sizeof(slot->child_usage));
        pid_t waited; do waited = wait4(slot->pid, &slot->status, 0, &slot->child_usage); while (waited < 0 && errno == EINTR);
        if (waited == slot->pid) {
            slot->child_usage_available = 1;
            slot->reaped = 1;
            slot->drain_deadline_ms = now + RT_OWNED_POST_REAP_DRAIN_MS;
            if (slot->runtime_error == ESTALE) slot->runtime_error = 0;
        }
        else slot->runtime_error = errno ? errno : ECHILD;
    } else if (!slot->reaped && wr < 0) slot->runtime_error = errno;
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
    if (slot->reaped && slot->in_open) {
        if (slot->input_written != slot->input_len && slot->runtime_error == 0)
            slot->runtime_error = EPIPE;
        owned_async_close_input(slot);
    }
    if (slot->reaped && !slot->out_open && !slot->err_open) slot->state = 2;
    uint64_t out_delivered = owned_async_deliver(slot, 0, out, out_cap);
    uint64_t err_delivered = owned_async_deliver(slot, 1, err, err_cap);
    owned_async_fill_poll(slot, receipt, out_delivered, err_delivered);
    pthread_mutex_unlock(slot->state_lock);
    owned_token_release(slot);
    return receipt->runtime_error == 0;
#endif
}

bool rt_process_owned_input_receipt_v3(RtOwnedProcessTokenV2 token,
                                       RtOwnedProcessInputReceiptV3* receipt) {
    if (!receipt) return false;
    memset(receipt, 0, sizeof(*receipt)); receipt->version = RT_OWNED_PROCESS_INPUT_VERSION;
    RtOwnedSlot* slot = owned_token_acquire(token, NULL);
    if (!slot) { receipt->runtime_error = ESTALE; return false; }
    pthread_mutex_lock(slot->state_lock);
    if (!slot->input_contract_v3) {
        pthread_mutex_unlock(slot->state_lock); owned_token_release(slot);
        receipt->runtime_error = EPROTO; return false;
    }
    receipt->input_bytes_accepted = slot->input_len;
    receipt->input_bytes_written = slot->input_written;
    memcpy(receipt->input_sha256, slot->input_sha256, sizeof(receipt->input_sha256));
    receipt->stdin_closed = !slot->in_open;
    receipt->terminal = slot->state == 2;
    receipt->reaped = slot->reaped;
    receipt->runtime_error = slot->runtime_error;
    pthread_mutex_unlock(slot->state_lock); owned_token_release(slot);
    return receipt->runtime_error == 0;
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

bool rt_process_owned_observation_v1(RtOwnedProcessTokenV2 token,
                                     RtOwnedProcessObservationV1* observation) {
    if (!observation) return false;
    memset(observation, 0, sizeof(*observation));
    observation->version = RT_OWNED_PROCESS_OBSERVATION_VERSION;
#ifndef __linux__
    (void)token; observation->runtime_error = ENOTSUP; return false;
#else
    RtOwnedSlot* slot = owned_token_acquire(token, NULL);
    if (!slot) { observation->runtime_error = ESTALE; return false; }
    pthread_mutex_lock(slot->state_lock);
    if (slot->state != 2) {
        pthread_mutex_unlock(slot->state_lock); owned_token_release(slot);
        observation->runtime_error = EAGAIN; return false;
    }
    if (slot->child_usage_available) {
        observation->evidence_flags |= RT_PROCESS_EVIDENCE_DIRECT_CHILD_RUSAGE;
        observation->user_cpu_ms = owned_timeval_ms(slot->child_usage.ru_utime);
        observation->system_cpu_ms = owned_timeval_ms(slot->child_usage.ru_stime);
        observation->peak_direct_child_rss_bytes = owned_direct_child_rss_bytes(&slot->child_usage);
        /* ru_inblock/ru_oublock count operations, not bytes. Keep byte fields
         * unavailable instead of relabeling unlike evidence. */
    }
    if (slot->reaped && WIFSIGNALED(slot->status)) {
        observation->termination_signal = WTERMSIG(slot->status);
    }
    pthread_mutex_unlock(slot->state_lock); owned_token_release(slot);
    return true;
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

/* The language ABI never receives the V2 token.  This small registry maps a
 * separately minted random positive handle to that token and serializes the
 * one operation that can consume a core lease.  `closing` prevents a release
 * from racing a newly admitted projection, while `refs` lets in-flight polls
 * finish against their stable token snapshot. */
#define RT_OWNED_ADAPTER_SLOTS RT_OWNED_PROCESS_SLOTS
#define RT_OWNED_ADAPTER_MAX_ARGS 4096
#define RT_OWNED_ADAPTER_MAX_ARG_BYTES (1024U * 1024U)
#define RT_OWNED_ADAPTER_MAX_POLL_BYTES (64U * 1024U)
typedef struct RtOwnedAdapterSlot {
    RtOwnedProcessTokenV2 token;
    uint64_t handle;
    uint32_t refs;
    int active;
    int closing;
} RtOwnedAdapterSlot;

static RtOwnedAdapterSlot rt_owned_adapter_slots[RT_OWNED_ADAPTER_SLOTS];
static pthread_mutex_t rt_owned_adapter_lock = PTHREAD_MUTEX_INITIALIZER;

static SplArray* owned_adapter_values(const int64_t* values, int64_t count) {
    SplArray* result = rt_array_new(count);
    if (!result) return NULL;
    for (int64_t i = 0; i < count; i++) {
        if (!rt_array_push(result, rt_value_int(values[i]))) {
            rt_array_free(result);
            return NULL;
        }
    }
    return result;
}

static int owned_adapter_fill_reserved_values(SplArray* result,
                                              const int64_t* values,
                                              int64_t count) {
    if (!result || rt_array_len(result) != 0) return 0;
    for (int64_t i = 0; i < count; i++)
        if (!rt_array_push(result, rt_value_int(values[i]))) return 0;
    return 1;
}

static SplArray* owned_adapter_bytes(const char* bytes, uint64_t count) {
    if (count > INT64_MAX) return NULL;
    SplArray* result = rt_array_new((int64_t)count);
    if (!result) return NULL;
    for (uint64_t i = 0; i < count; i++) {
        if (!rt_array_push(result, rt_value_int((unsigned char)bytes[i]))) {
            rt_array_free(result);
            return NULL;
        }
    }
    return result;
}

static SplArray* owned_adapter_poll_error(int error) {
    const int64_t fields[] = { RT_OWNED_PROCESS_OPAQUE_V3_VERSION, 0, 0, 0, 0, 0, 0, 0,
        0, 0, 0, 0, 0, 0, 0, 0, error };
    SplArray* out = owned_adapter_bytes("", 0);
    SplArray* err = owned_adapter_bytes("", 0);
    SplArray* receipt = owned_adapter_values(fields, 17);
    SplArray* tuple = NULL;
    if (out && err && receipt && (tuple = rt_array_new(3)) &&
        rt_array_push(tuple, (int64_t)(uintptr_t)out) &&
        rt_array_push(tuple, (int64_t)(uintptr_t)err) &&
        rt_array_push(tuple, (int64_t)(uintptr_t)receipt)) return tuple;
    if (tuple) rt_array_free(tuple);
    if (out) rt_array_free(out);
    if (err) rt_array_free(err);
    if (receipt) rt_array_free(receipt);
    return NULL;
}

static int owned_adapter_handle_live_locked(uint64_t handle) {
    for (uint32_t i = 0; i < RT_OWNED_ADAPTER_SLOTS; i++)
        if (rt_owned_adapter_slots[i].active && rt_owned_adapter_slots[i].handle == handle)
            return 1;
    return 0;
}

static int owned_adapter_reserve(uint32_t* index, uint64_t* handle) {
    if (pthread_mutex_lock(&rt_owned_adapter_lock) != 0) return 0;
    uint32_t free_index = RT_OWNED_ADAPTER_SLOTS;
    for (uint32_t i = 0; i < RT_OWNED_ADAPTER_SLOTS; i++) {
        if (!rt_owned_adapter_slots[i].active) { free_index = i; break; }
    }
    if (free_index == RT_OWNED_ADAPTER_SLOTS) {
        pthread_mutex_unlock(&rt_owned_adapter_lock); errno = EAGAIN; return 0;
    }
    for (int attempt = 0; attempt < 16; attempt++) {
        RtOwnedProcessTokenV2 entropy = {0, 0};
        if (!owned_token_random(&entropy)) break;
        /* Keep handles in Simple's immediate positive integer range, avoiding
         * heap-box allocation or truncating OOM fallback during publication. */
        uint64_t candidate = entropy.low & UINT64_C(0x0fffffffffffffff);
        if (candidate && !owned_adapter_handle_live_locked(candidate)) {
            RtOwnedAdapterSlot* slot = &rt_owned_adapter_slots[free_index];
            memset(slot, 0, sizeof(*slot));
            slot->handle = candidate;
            slot->active = 1; /* reserved, not yet externally visible */
            *index = free_index; *handle = candidate;
            pthread_mutex_unlock(&rt_owned_adapter_lock);
            return 1;
        }
    }
    pthread_mutex_unlock(&rt_owned_adapter_lock);
    if (!errno) errno = EAGAIN;
    return 0;
}

static void owned_adapter_drop(uint32_t index) {
    if (pthread_mutex_lock(&rt_owned_adapter_lock) != 0) return;
    if (index < RT_OWNED_ADAPTER_SLOTS) memset(&rt_owned_adapter_slots[index], 0,
                                                sizeof(rt_owned_adapter_slots[index]));
    pthread_mutex_unlock(&rt_owned_adapter_lock);
}

static int owned_adapter_publish(uint32_t index, RtOwnedProcessTokenV2 token) {
    if (pthread_mutex_lock(&rt_owned_adapter_lock) != 0) return 0;
    int ok = index < RT_OWNED_ADAPTER_SLOTS && rt_owned_adapter_slots[index].active &&
             !rt_owned_adapter_slots[index].closing;
    if (ok) rt_owned_adapter_slots[index].token = token;
    pthread_mutex_unlock(&rt_owned_adapter_lock);
    return ok;
}

static int owned_adapter_acquire(int64_t raw_handle, RtOwnedProcessTokenV2* token,
                                 uint32_t* index) {
    uint64_t handle = (uint64_t)raw_handle;
    if (raw_handle <= 0 || pthread_mutex_lock(&rt_owned_adapter_lock) != 0) return 0;
    for (uint32_t i = 0; i < RT_OWNED_ADAPTER_SLOTS; i++) {
        RtOwnedAdapterSlot* slot = &rt_owned_adapter_slots[i];
        if (slot->active && !slot->closing && slot->handle == handle &&
            (slot->token.high || slot->token.low)) {
            slot->refs++; *token = slot->token; *index = i;
            pthread_mutex_unlock(&rt_owned_adapter_lock);
            return 1;
        }
    }
    pthread_mutex_unlock(&rt_owned_adapter_lock);
    return 0;
}

static void owned_adapter_release_ref(uint32_t index) {
    if (pthread_mutex_lock(&rt_owned_adapter_lock) != 0) return;
    if (index < RT_OWNED_ADAPTER_SLOTS && rt_owned_adapter_slots[index].refs)
        rt_owned_adapter_slots[index].refs--;
    pthread_mutex_unlock(&rt_owned_adapter_lock);
}

static int owned_adapter_begin_consume(int64_t raw_handle, RtOwnedProcessTokenV2* token,
                                       uint32_t* index) {
    uint64_t handle = (uint64_t)raw_handle;
    if (raw_handle <= 0 || pthread_mutex_lock(&rt_owned_adapter_lock) != 0) return 0;
    for (uint32_t i = 0; i < RT_OWNED_ADAPTER_SLOTS; i++) {
        RtOwnedAdapterSlot* slot = &rt_owned_adapter_slots[i];
        if (slot->active && !slot->closing && slot->refs == 0 && slot->handle == handle &&
            (slot->token.high || slot->token.low)) {
            slot->closing = 1; *token = slot->token; *index = i;
            pthread_mutex_unlock(&rt_owned_adapter_lock);
            return 1;
        }
    }
    pthread_mutex_unlock(&rt_owned_adapter_lock);
    return 0;
}

static void owned_adapter_end_consume(uint32_t index, int consumed) {
    if (pthread_mutex_lock(&rt_owned_adapter_lock) != 0) return;
    if (index < RT_OWNED_ADAPTER_SLOTS) {
        if (consumed) memset(&rt_owned_adapter_slots[index], 0,
                             sizeof(rt_owned_adapter_slots[index]));
        else rt_owned_adapter_slots[index].closing = 0;
    }
    pthread_mutex_unlock(&rt_owned_adapter_lock);
}

static void owned_adapter_free_argv(char** argv, int64_t argc) {
    if (!argv) return;
    for (int64_t i = 0; i <= argc; i++) RT_OWNED_HOST_FREE(argv[i]);
    RT_OWNED_HOST_FREE(argv);
}

static char** owned_adapter_copy_argv(const char* command_data, uint64_t command_len,
                                      SplArray* args, int64_t* argc_out, int* error_out) {
    *argc_out = -1; *error_out = EINVAL;
    if (!command_data || !args || command_len == 0 || command_len > RT_OWNED_ADAPTER_MAX_ARG_BYTES ||
        command_len > SIZE_MAX - 1 || memchr(command_data, '\0', (size_t)command_len)) return NULL;
    int64_t argc = rt_array_len(args);
    if (argc < 0 || argc > RT_OWNED_ADAPTER_MAX_ARGS || (uint64_t)argc > SIZE_MAX / sizeof(char*) - 2) return NULL;
    char** argv = (char**)RT_OWNED_HOST_CALLOC((size_t)argc + 2, sizeof(char*));
    if (!argv) { *error_out = ENOMEM; return NULL; }
    argv[0] = (char*)RT_OWNED_HOST_MALLOC((size_t)command_len + 1);
    if (!argv[0]) { owned_adapter_free_argv(argv, argc); *error_out = ENOMEM; return NULL; }
    memcpy(argv[0], command_data, (size_t)command_len); argv[0][command_len] = '\0';
    for (int64_t i = 0; i < argc; i++) {
        int64_t value = rt_array_get(args, i);
        int64_t length = rt_string_len(value);
        const uint8_t* data = rt_string_data(value);
        if (length < 0 || !data || (uint64_t)length > RT_OWNED_ADAPTER_MAX_ARG_BYTES ||
            (uint64_t)length > SIZE_MAX - 1 || memchr(data, '\0', (size_t)length)) {
            owned_adapter_free_argv(argv, argc); return NULL;
        }
        argv[i + 1] = (char*)RT_OWNED_HOST_MALLOC((size_t)length + 1);
        if (!argv[i + 1]) { owned_adapter_free_argv(argv, argc); *error_out = ENOMEM; return NULL; }
        memcpy(argv[i + 1], data, (size_t)length); argv[i + 1][length] = '\0';
    }
    *argc_out = argc; *error_out = 0;
    return argv;
}

static SplArray* owned_adapter_result_values(const RtOwnedProcessResultV2* result) {
    const int64_t values[] = { RT_OWNED_PROCESS_OPAQUE_V3_VERSION, result->exit_code,
        result->timed_out, result->cancel_requested, result->term_sent, result->kill_sent,
        result->identity_revalidated, result->reaped, result->stdout_truncated,
        result->stderr_truncated, (int64_t)result->stdout_bytes_seen,
        (int64_t)result->stderr_bytes_seen, (int64_t)result->stdout_bytes_kept,
        (int64_t)result->stderr_bytes_kept, result->runtime_error };
    return owned_adapter_values(values, (int64_t)(sizeof(values) / sizeof(values[0])));
}

/* Start publishes no authority until the adapter token map is installed.  A
 * mutex-provider failure at that exact point must still consume the private
 * core lease rather than orphaning a child or its captured output. */
static void owned_adapter_discard_unpublished(RtOwnedProcessTokenV2 token) {
    RtOwnedProcessCancelReceipt cancel;
    (void)rt_process_owned_cancel_v2(token, &cancel);
    char out[8192], err[8192];
    RtOwnedProcessPollReceiptV2 poll;
    for (int i = 0; i < 4096; i++) {
        (void)rt_process_owned_poll_v2(token, 0, out, sizeof(out), err, sizeof(err), &poll);
        if (poll.terminal && poll.stdout_bytes_delivered == 0 && poll.stderr_bytes_delivered == 0) break;
    }
    RtOwnedProcessResultV2 result;
    (void)rt_process_owned_collect_v2(token, &result);
}

SplArray* rt_process_owned_v3_start_value(const char* command_data, uint64_t command_len,
                                          SplArray* args, SplArray* input,
                                          int64_t timeout_ms, int64_t term_grace_ms,
                                          int64_t max_output_bytes) {
    int64_t values[4] = {0, RT_OWNED_PROCESS_OPAQUE_V3_VERSION, 0, EINVAL};
    SplArray* projected = rt_array_new(4);
    if (!projected) return NULL;
    int64_t argc = -1, input_len = -1; int copy_error = EINVAL;
    char** argv = owned_adapter_copy_argv(command_data, command_len, args, &argc, &copy_error);
    uint8_t* input_copy = NULL;
    uint32_t adapter_index = 0; uint64_t handle = 0;
    RtOwnedProcessTokenV2 token = {0, 0}; RtOwnedProcessStartReceiptV2 receipt;
    if (!argv) {
        values[3] = copy_error;
        (void)owned_adapter_fill_reserved_values(projected, values, 4);
        return projected;
    }
    input_len = input ? rt_array_len(input) : -1;
    if (input_len < 0 || (uint64_t)input_len > RT_OWNED_PROCESS_MAX_INPUT_BYTES ||
        max_output_bytes < 0 || (uint64_t)max_output_bytes > RT_OWNED_ABI_MAX_OUTPUT_BYTES) goto done;
    if (rt_array_bytes_validate((int64_t)(uintptr_t)input) != input_len) goto done;
    if (input_len) {
        input_copy = (uint8_t*)RT_OWNED_HOST_MALLOC((size_t)input_len);
        if (!input_copy) { values[3] = ENOMEM; goto done; }
        if (rt_array_bytes_copy_checked((int64_t)(uintptr_t)input, input_copy, input_len) != input_len) {
            values[3] = EINVAL; goto done;
        }
    }
    if (!owned_adapter_reserve(&adapter_index, &handle)) { values[3] = errno ? errno : EAGAIN; goto done; }
    if (!rt_process_owned_start_v3(argv[0], (const char* const*)argv, input_copy,
                                   (uint64_t)input_len, timeout_ms, term_grace_ms,
                                   (uint64_t)max_output_bytes, &token, &receipt)) {
        values[3] = receipt.runtime_error ? receipt.runtime_error : EIO;
        owned_adapter_drop(adapter_index); goto done;
    }
    if (!owned_adapter_publish(adapter_index, token)) {
        owned_adapter_discard_unpublished(token);
        owned_adapter_drop(adapter_index); values[3] = ESTALE; goto done;
    }
    values[0] = (int64_t)handle; values[2] = 1; values[3] = 0;
done:
    RT_OWNED_HOST_FREE(input_copy);
    owned_adapter_free_argv(argv, argc);
    if (!owned_adapter_fill_reserved_values(projected, values, 4)) {
        /* The fixed-size projection was fully allocated before any authority
         * existed, so replacement cannot require allocation. */
        rt_array_free(projected);
        return NULL;
    }
    return projected;
}

SplArray* rt_process_owned_v3_start_pinned_value(int64_t executable_handle,
                                                  SplArray* args, SplArray* input,
                                                  int64_t timeout_ms,
                                                  int64_t term_grace_ms,
                                                  int64_t max_output_bytes) {
    static const char argv0[] = "simple-pinned-executable";
    int64_t values[4] = {0, RT_OWNED_PROCESS_OPAQUE_V3_VERSION, 0, EINVAL};
    SplArray* projected = rt_array_new(4);
    int64_t argc = -1, input_len = -1; int copy_error = EINVAL;
    uint8_t* input_copy = NULL; char** argv = NULL;
    uint32_t adapter_index = 0; uint64_t handle = 0;
    RtOwnedProcessTokenV2 token = {0, 0}; RtOwnedProcessStartReceiptV2 receipt;
    if (!projected) return NULL;
    argv = owned_adapter_copy_argv(argv0, sizeof(argv0) - 1, args, &argc, &copy_error);
    if (!argv) { values[3] = copy_error; goto done; }
    input_len = input ? rt_array_len(input) : -1;
    if (input_len < 0 || (uint64_t)input_len > RT_OWNED_PROCESS_MAX_INPUT_BYTES ||
        max_output_bytes < 0 || (uint64_t)max_output_bytes > RT_OWNED_ABI_MAX_OUTPUT_BYTES ||
        rt_array_bytes_validate((int64_t)(uintptr_t)input) != input_len) goto done;
    if (input_len) {
        input_copy = (uint8_t*)RT_OWNED_HOST_MALLOC((size_t)input_len);
        if (!input_copy) { values[3] = ENOMEM; goto done; }
        if (rt_array_bytes_copy_checked((int64_t)(uintptr_t)input, input_copy, input_len) != input_len) goto done;
    }
    if (!owned_adapter_reserve(&adapter_index, &handle)) { values[3] = errno ? errno : EAGAIN; goto done; }
    if (!rt_process_owned_start_pinned_v3(executable_handle, (const char* const*)argv,
                                          input_copy, (uint64_t)input_len, timeout_ms,
                                          term_grace_ms, (uint64_t)max_output_bytes, &token, &receipt)) {
        values[3] = receipt.runtime_error ? receipt.runtime_error : EIO;
        owned_adapter_drop(adapter_index); goto done;
    }
    if (!owned_adapter_publish(adapter_index, token)) {
        owned_adapter_discard_unpublished(token); owned_adapter_drop(adapter_index);
        values[3] = ESTALE; goto done;
    }
    values[0] = (int64_t)handle; values[2] = 1; values[3] = 0;
done:
    RT_OWNED_HOST_FREE(input_copy); owned_adapter_free_argv(argv, argc);
    if (!owned_adapter_fill_reserved_values(projected, values, 4)) { rt_array_free(projected); return NULL; }
    return projected;
}

SplArray* rt_process_owned_v3_poll_value(int64_t handle, int64_t wait_ms,
                                         int64_t stdout_capacity, int64_t stderr_capacity) {
    RtOwnedProcessTokenV2 token; uint32_t index;
    if (wait_ms < 0 || wait_ms > 1000) return owned_adapter_poll_error(EINVAL);
    if (!owned_adapter_acquire(handle, &token, &index)) return owned_adapter_poll_error(ESTALE);
    if (stdout_capacity < 0 || stderr_capacity < 0 || stdout_capacity > RT_OWNED_ADAPTER_MAX_POLL_BYTES ||
        stderr_capacity > RT_OWNED_ADAPTER_MAX_POLL_BYTES) {
        owned_adapter_release_ref(index); return owned_adapter_poll_error(EINVAL);
    }
    char* out = NULL; char* err = NULL;
    if (stdout_capacity) { out = (char*)RT_OWNED_HOST_MALLOC((size_t)stdout_capacity + 1); if (!out) goto oom; }
    if (stderr_capacity) { err = (char*)RT_OWNED_HOST_MALLOC((size_t)stderr_capacity + 1); if (!err) goto oom; }
    SplArray* out_value = rt_array_new(stdout_capacity);
    SplArray* err_value = rt_array_new(stderr_capacity);
    SplArray* field_value = rt_array_new(17);
    SplArray* tuple = rt_array_new(3);
    if (!out_value || !err_value || !field_value || !tuple ||
        !rt_array_push(tuple, (int64_t)(uintptr_t)out_value) ||
        !rt_array_push(tuple, (int64_t)(uintptr_t)err_value) ||
        !rt_array_push(tuple, (int64_t)(uintptr_t)field_value)) {
        rt_array_free(tuple); rt_array_free(out_value); rt_array_free(err_value);
        rt_array_free(field_value); goto oom;
    }
    RtOwnedProcessPollReceiptV2 receipt;
    memset(&receipt, 0, sizeof(receipt));
    receipt.version = RT_OWNED_PROCESS_ASYNC_VERSION;
    if (!rt_process_owned_poll_v2(token, wait_ms, out,
            (uint64_t)stdout_capacity + (stdout_capacity ? 1 : 0), err,
            (uint64_t)stderr_capacity + (stderr_capacity ? 1 : 0), &receipt) &&
        receipt.runtime_error == 0)
        receipt.runtime_error = EIO;
    uint64_t out_count = receipt.stdout_bytes_delivered;
    uint64_t err_count = receipt.stderr_bytes_delivered;
    int64_t fields[] = { RT_OWNED_PROCESS_OPAQUE_V3_VERSION, receipt.live, receipt.terminal,
        receipt.cancel_requested, receipt.timed_out, receipt.term_sent, receipt.kill_sent, receipt.reaped,
        receipt.stdout_truncated, receipt.stderr_truncated, (int64_t)receipt.stdout_bytes_seen,
        (int64_t)receipt.stderr_bytes_seen, (int64_t)receipt.stdout_bytes_kept,
        (int64_t)receipt.stderr_bytes_kept, (int64_t)receipt.stdout_bytes_delivered,
        (int64_t)receipt.stderr_bytes_delivered, receipt.runtime_error };
    int projection_ok = 1;
    for (uint64_t i = 0; i < out_count; i++)
        projection_ok = projection_ok && rt_array_push(out_value,
            rt_value_int((unsigned char)out[i]));
    for (uint64_t i = 0; i < err_count; i++)
        projection_ok = projection_ok && rt_array_push(err_value,
            rt_value_int((unsigned char)err[i]));
    for (int i = 0; i < 17; i++)
        projection_ok = projection_ok && rt_array_push(field_value, rt_value_int(fields[i]));
    if (projection_ok) {
        RT_OWNED_HOST_FREE(out); RT_OWNED_HOST_FREE(err); owned_adapter_release_ref(index); return tuple;
    }
    rt_array_free(tuple); rt_array_free(out_value); rt_array_free(err_value); rt_array_free(field_value);
    RT_OWNED_HOST_FREE(out); RT_OWNED_HOST_FREE(err); owned_adapter_release_ref(index); return NULL;
oom:
    RT_OWNED_HOST_FREE(out); RT_OWNED_HOST_FREE(err); owned_adapter_release_ref(index);
    return owned_adapter_poll_error(ENOMEM);
}

SplArray* rt_process_owned_v3_input_value(int64_t handle) {
    RtOwnedProcessInputReceiptV3 receipt; RtOwnedProcessTokenV2 token; uint32_t index;
    if (!owned_adapter_acquire(handle, &token, &index)) {
        int64_t values[39] = { RT_OWNED_PROCESS_OPAQUE_V3_VERSION, 0, 0, 0, 0, 0, ESTALE };
        return owned_adapter_values(values, 39);
    }
    (void)rt_process_owned_input_receipt_v3(token, &receipt); owned_adapter_release_ref(index);
    int64_t values[39] = { RT_OWNED_PROCESS_OPAQUE_V3_VERSION, (int64_t)receipt.input_bytes_accepted,
        (int64_t)receipt.input_bytes_written, receipt.stdin_closed, receipt.terminal, receipt.reaped,
        receipt.runtime_error };
    for (int i = 0; i < 32; i++) values[7 + i] = receipt.input_sha256[i];
    return owned_adapter_values(values, 39);
}

SplArray* rt_process_owned_v3_cancel_value(int64_t handle) {
    RtOwnedProcessCancelReceipt receipt; RtOwnedProcessTokenV2 token; uint32_t index;
    if (!owned_adapter_acquire(handle, &token, &index)) {
        const int64_t values[] = { RT_OWNED_PROCESS_OPAQUE_V3_VERSION, 0, 0, ESTALE };
        return owned_adapter_values(values, 4);
    }
    (void)rt_process_owned_cancel_v2(token, &receipt); owned_adapter_release_ref(index);
    const int64_t values[] = { RT_OWNED_PROCESS_OPAQUE_V3_VERSION, receipt.accepted,
        receipt.term_sent, receipt.runtime_error };
    return owned_adapter_values(values, 4);
}

SplArray* rt_process_owned_v3_result_value(int64_t handle) {
    RtOwnedProcessResultV2 result; RtOwnedProcessTokenV2 token; uint32_t index;
    if (!owned_adapter_acquire(handle, &token, &index)) {
        memset(&result, 0, sizeof(result)); result.exit_code = -1; result.runtime_error = ESTALE;
        return owned_adapter_result_values(&result);
    }
    (void)rt_process_owned_result_v2(token, &result); owned_adapter_release_ref(index);
    return owned_adapter_result_values(&result);
}

SplArray* rt_process_owned_v3_collect_value(int64_t handle) {
    RtOwnedProcessResultV2 result; RtOwnedProcessTokenV2 token; uint32_t index;
    if (!owned_adapter_begin_consume(handle, &token, &index)) {
        memset(&result, 0, sizeof(result)); result.exit_code = -1; result.runtime_error = ESTALE;
        return owned_adapter_result_values(&result);
    }
    int consumed = rt_process_owned_collect_v2(token, &result) ? 1 : 0;
    /* A terminal provider error still consumes the core lease: its copied
     * result carries the error but a retry must never resurrect authority. */
    if (!consumed && result.reaped && result.runtime_error != EAGAIN && result.runtime_error != EBUSY)
        consumed = 1;
    owned_adapter_end_consume(index, consumed);
    return owned_adapter_result_values(&result);
}

int rt_process_owned_v3_release_value(int64_t handle) {
    RtOwnedProcessTokenV2 token; uint32_t index; RtOwnedProcessResultV2 result;
    if (!owned_adapter_begin_consume(handle, &token, &index)) return 0;
    int consumed = rt_process_owned_collect_v2(token, &result) ? 1 : 0;
    if (!consumed && result.reaped && result.runtime_error != EAGAIN && result.runtime_error != EBUSY)
        consumed = 1;
    owned_adapter_end_consume(index, consumed);
    return consumed;
}

static bool owned_run_bounded_impl(const char* cmd, const char* const* argv,
                                   int64_t timeout_ms, uint64_t max_output_bytes,
                                   char* out, uint64_t out_cap,
                                   char* err, uint64_t err_cap,
                                   RtOwnedProcessReceipt* receipt,
                                   RtOwnedProcessObservationV1* observation) {
    if (!receipt) return false;
    memset(receipt, 0, sizeof(*receipt));
    if (observation) {
        memset(observation, 0, sizeof(*observation));
        observation->version = RT_OWNED_PROCESS_OBSERVATION_VERSION;
    }
    receipt->version = RT_OWNED_PROCESS_RECEIPT_VERSION;
    receipt->exit_code = -1;
    if (!cmd || !argv || timeout_ms <= 0 ||
        (out_cap && !out) || (err_cap && !err)) {
        receipt->runtime_error = EINVAL;
        if (observation) observation->runtime_error = EINVAL;
        return false;
    }
    if (out_cap) out[0] = '\0';
    if (err_cap) err[0] = '\0';
#ifndef __linux__
    receipt->runtime_error = ENOTSUP;
    if (observation) observation->runtime_error = ENOTSUP;
    return false;
#else
    RtOwnedCleanup cleanup = {0, 0, 0, 0, -1, -1, -1, 0, 0};
    struct rusage child_usage;
    memset(&child_usage, 0, sizeof(child_usage));
    volatile int child_usage_available = 0;
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
    int64_t next_tree_sample_ms = started;
    if (started < 0) { receipt->runtime_error = errno ? errno : EIO; goto done; }
    while (!child_done || out_open || err_open) {
        int64_t now = owned_now_ms();
        if (now < 0) { receipt->runtime_error = errno ? errno : EIO; break; }
        if (observation && !child_done && now >= next_tree_sample_ms) {
            RtOwnedTreeSample sample = owned_sample_process_group(pid);
            if (sample.pids > 0) {
                observation->evidence_flags |= RT_PROCESS_EVIDENCE_SAMPLED_TREE;
                if (sample.charge_bytes > observation->peak_tree_charge_bytes)
                    observation->peak_tree_charge_bytes = sample.charge_bytes;
                if (sample.io_read_bytes > observation->io_read_bytes)
                    observation->io_read_bytes = sample.io_read_bytes;
                if (sample.io_write_bytes > observation->io_write_bytes)
                    observation->io_write_bytes = sample.io_write_bytes;
                if (sample.pids > observation->pids_peak)
                    observation->pids_peak = sample.pids;
            }
            next_tree_sample_ms = now + 50;
        }
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
                do waited = wait4(pid, &status, 0, &child_usage); while (waited < 0 && errno == EINTR);
                if (waited != pid) { receipt->runtime_error = errno ? errno : ECHILD; break; }
                child_usage_available = 1;
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
        do waited = wait4(pid, &status, 0, &child_usage); while (waited < 0 && errno == EINTR);
        if (waited == pid) { cleanup.reaped = 1; receipt->reaped = 1; child_usage_available = 1; }
        else if (receipt->runtime_error == 0) receipt->runtime_error = errno ? errno : ECHILD;
    }
    if (receipt->reaped) {
        if (WIFEXITED(status)) receipt->exit_code = WEXITSTATUS(status);
        else if (WIFSIGNALED(status)) receipt->exit_code = 128 + WTERMSIG(status);
    }
    if (observation && child_usage_available) {
        observation->evidence_flags |= RT_PROCESS_EVIDENCE_DIRECT_CHILD_RUSAGE;
        observation->user_cpu_ms = owned_timeval_ms(child_usage.ru_utime);
        observation->system_cpu_ms = owned_timeval_ms(child_usage.ru_stime);
        observation->peak_direct_child_rss_bytes = owned_direct_child_rss_bytes(&child_usage);
    }
    if (observation && receipt->reaped && WIFSIGNALED(status)) {
        observation->termination_signal = WTERMSIG(status);
    }

done:
    /* Prevent cancellation between manual cleanup and popping its handler. */
    (void)pthread_setcancelstate(PTHREAD_CANCEL_DISABLE, NULL);
    if (out_cap) out[receipt->stdout_bytes_kept < out_cap ? receipt->stdout_bytes_kept : out_cap - 1] = '\0';
    if (err_cap) err[receipt->stderr_bytes_kept < err_cap ? receipt->stderr_bytes_kept : err_cap - 1] = '\0';
    owned_cleanup(&cleanup);
    if (observation) observation->runtime_error = receipt->runtime_error;
    pthread_cleanup_pop(0);
    (void)pthread_setcancelstate(old_cancel_state, NULL);
    if (old_cancel_state == PTHREAD_CANCEL_ENABLE) pthread_testcancel();
    return receipt->runtime_error == 0;
#endif
}

bool rt_process_run_owned_bounded(const char* cmd, const char* const* argv,
                                  int64_t timeout_ms, uint64_t max_output_bytes,
                                  char* out, uint64_t out_cap,
                                  char* err, uint64_t err_cap,
                                  RtOwnedProcessReceipt* receipt) {
    return owned_run_bounded_impl(cmd, argv, timeout_ms, max_output_bytes,
                                  out, out_cap, err, err_cap, receipt, NULL);
}

bool rt_process_run_owned_observed_bounded(const char* cmd, const char* const* argv,
                                           int64_t timeout_ms, uint64_t max_output_bytes,
                                           char* out, uint64_t out_cap,
                                           char* err, uint64_t err_cap,
                                           RtOwnedProcessReceipt* receipt,
                                           RtOwnedProcessObservationV1* observation) {
    if (!observation) return false;
    return owned_run_bounded_impl(cmd, argv, timeout_ms, max_output_bytes,
                                  out, out_cap, err, err_cap, receipt, observation);
}

/* Stable language ABI. Keep the policy receipt numeric and versioned so the
 * Simple facade can reject layouts it does not understand. */
#ifndef RT_PROCESS_OWNED_CORE_ONLY
static int64_t* owned_run_bounded_value_impl(const char* cmd_data, uint64_t cmd_len, SplArray* args,
                                             int64_t timeout_ms,
                                             int64_t max_output_bytes,
                                             int include_observation) {
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
    RtOwnedProcessObservationV1 observation;
    bool ok = include_observation
        ? rt_process_run_owned_observed_bounded(cmd, (const char* const*)argv, timeout_ms, limit,
                                                out, capacity, err, capacity, &receipt, &observation)
        : rt_process_run_owned_bounded(cmd, (const char* const*)argv, timeout_ms, limit,
                                       out, capacity, err, capacity, &receipt);
    fields = rt_array_new(include_observation ? 30 : 19);
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
    if (include_observation) {
        OWNED_PUSH(observation.version); OWNED_PUSH(observation.evidence_flags);
        OWNED_PUSH(observation.user_cpu_ms); OWNED_PUSH(observation.system_cpu_ms);
        OWNED_PUSH(observation.peak_direct_child_rss_bytes);
        OWNED_PUSH(observation.peak_tree_charge_bytes); OWNED_PUSH(observation.io_read_bytes);
        OWNED_PUSH(observation.io_write_bytes); OWNED_PUSH(observation.pids_peak);
        OWNED_PUSH(observation.termination_signal);
        OWNED_PUSH(observation.runtime_error);
    }
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

int64_t* rt_process_run_owned_bounded_value(const char* cmd_data, uint64_t cmd_len, SplArray* args,
                                            int64_t timeout_ms, int64_t max_output_bytes) {
    return owned_run_bounded_value_impl(cmd_data, cmd_len, args, timeout_ms, max_output_bytes, 0);
}

int64_t* rt_process_run_owned_observed_bounded_value(const char* cmd_data, uint64_t cmd_len,
                                                     SplArray* args, int64_t timeout_ms,
                                                     int64_t max_output_bytes) {
    return owned_run_bounded_value_impl(cmd_data, cmd_len, args, timeout_ms, max_output_bytes, 1);
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

bool rt_process_owned_start_v3(const char* cmd, const char* const* argv,
                               const uint8_t* input, uint64_t input_len,
                               int64_t timeout_ms, int64_t term_grace_ms,
                               uint64_t max_output_bytes,
                               RtOwnedProcessTokenV2* token,
                               RtOwnedProcessStartReceiptV2* receipt) {
    (void)cmd; (void)argv; (void)input; (void)input_len; (void)timeout_ms;
    (void)term_grace_ms; (void)max_output_bytes;
    if (!token || !receipt) return false;
    memset(token, 0, sizeof(*token)); memset(receipt, 0, sizeof(*receipt));
    receipt->version = RT_OWNED_PROCESS_INPUT_VERSION; receipt->runtime_error = ENOTSUP;
    return false;
}

bool rt_process_owned_start_pinned_v3(int64_t executable_handle,
                                      const char* const* argv,
                                      const uint8_t* input, uint64_t input_len,
                                      int64_t timeout_ms, int64_t term_grace_ms,
                                      uint64_t max_output_bytes,
                                      RtOwnedProcessTokenV2* token,
                                      RtOwnedProcessStartReceiptV2* receipt) {
    (void)executable_handle; (void)argv; (void)input; (void)input_len;
    (void)timeout_ms; (void)term_grace_ms; (void)max_output_bytes;
    if (!token || !receipt) return false;
    memset(token, 0, sizeof(*token)); memset(receipt, 0, sizeof(*receipt));
    receipt->version = RT_OWNED_PROCESS_INPUT_VERSION; receipt->runtime_error = ENOTSUP;
    return false;
}

bool rt_process_owned_input_receipt_v3(RtOwnedProcessTokenV2 token,
                                       RtOwnedProcessInputReceiptV3* receipt) {
    (void)token;
    if (!receipt) return false;
    memset(receipt, 0, sizeof(*receipt)); receipt->version = RT_OWNED_PROCESS_INPUT_VERSION;
    receipt->runtime_error = ENOTSUP;
    return false;
}

bool rt_process_run_owned_observed_bounded(const char* cmd, const char* const* argv,
                                           int64_t timeout_ms, uint64_t max_output_bytes,
                                           char* out, uint64_t out_cap, char* err,
                                           uint64_t err_cap, RtOwnedProcessReceipt* receipt,
                                           RtOwnedProcessObservationV1* observation) {
    if (!observation) return false;
    memset(observation, 0, sizeof(*observation));
    observation->version = RT_OWNED_PROCESS_OBSERVATION_VERSION;
    observation->runtime_error = ENOTSUP;
    return rt_process_run_owned_bounded(cmd, argv, timeout_ms, max_output_bytes,
                                        out, out_cap, err, err_cap, receipt);
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

bool rt_process_owned_observation_v1(RtOwnedProcessTokenV2 token,
                                     RtOwnedProcessObservationV1* observation) {
    if (!observation) return false;
    memset(observation, 0, sizeof(*observation));
    observation->version = RT_OWNED_PROCESS_OBSERVATION_VERSION;
    observation->runtime_error = ENOTSUP;
    (void)token;
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

int64_t* rt_process_run_owned_observed_bounded_value(const char* cmd, uint64_t cmd_len,
                                                     SplArray* args, int64_t timeout_ms,
                                                     int64_t max_output_bytes) {
    (void)cmd; (void)cmd_len; (void)args; (void)timeout_ms; (void)max_output_bytes;
    SplArray* fields = rt_array_new(30);
    if (!fields) return NULL;
    const int64_t values[30] = {
        RT_OWNED_PROCESS_RECEIPT_VERSION, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        -1, 0, 0, 0, 0, 0, 0, 0, ENOTSUP,
        RT_OWNED_PROCESS_OBSERVATION_VERSION, 0, 0, 0, 0, 0, 0, 0, 0, 0, ENOTSUP,
    };
    for (int i = 0; i < 30; i++) {
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

static SplArray* owned_v3_unsupported_words(int64_t count, int64_t error_index) {
    SplArray* values = rt_array_new(count);
    if (!values) return NULL;
    for (int64_t i = 0; i < count; i++) {
        int64_t value = i == 0 ? RT_OWNED_PROCESS_OPAQUE_V3_VERSION : 0;
        if (i == error_index) value = ENOTSUP;
        if (!rt_array_push(values, rt_value_int(value))) {
            rt_array_free(values); return NULL;
        }
    }
    return values;
}

SplArray* rt_process_owned_v3_start_value(const char* command_data,
        uint64_t command_len, SplArray* args, SplArray* input,
        int64_t timeout_ms, int64_t term_grace_ms, int64_t max_output_bytes) {
    (void)command_data; (void)command_len; (void)args; (void)input;
    (void)timeout_ms; (void)term_grace_ms; (void)max_output_bytes;
    SplArray* values = owned_v3_unsupported_words(4, 3);
    if (values) {
        (void)rt_array_set(values, 0, rt_value_int(0));
        (void)rt_array_set(values, 1,
            rt_value_int(RT_OWNED_PROCESS_OPAQUE_V3_VERSION));
    }
    return values;
}

SplArray* rt_process_owned_v3_start_pinned_value(int64_t executable_handle,
        SplArray* args, SplArray* input, int64_t timeout_ms,
        int64_t term_grace_ms, int64_t max_output_bytes) {
    (void)executable_handle; (void)args; (void)input; (void)timeout_ms;
    (void)term_grace_ms; (void)max_output_bytes;
    SplArray* values = rt_array_new(4);
    if (!values) return NULL;
    const int64_t fields[] = {0, RT_OWNED_PROCESS_OPAQUE_V3_VERSION, 0, ENOTSUP};
    for (int i = 0; i < 4; i++) if (!rt_array_push(values, rt_value_int(fields[i]))) { rt_array_free(values); return NULL; }
    return values;
}

SplArray* rt_process_owned_v3_poll_value(int64_t handle, int64_t wait_ms,
        int64_t stdout_capacity, int64_t stderr_capacity) {
    (void)handle; (void)wait_ms; (void)stdout_capacity; (void)stderr_capacity;
    SplArray* out = rt_array_new(0); SplArray* err = rt_array_new(0);
    SplArray* receipt = owned_v3_unsupported_words(17, 16);
    SplArray* tuple = rt_array_new(3);
    if (out && err && receipt && tuple &&
        rt_array_push(tuple, (int64_t)(uintptr_t)out) &&
        rt_array_push(tuple, (int64_t)(uintptr_t)err) &&
        rt_array_push(tuple, (int64_t)(uintptr_t)receipt)) return tuple;
    rt_array_free(tuple); rt_array_free(out); rt_array_free(err);
    rt_array_free(receipt); return NULL;
}

SplArray* rt_process_owned_v3_input_value(int64_t handle) {
    (void)handle; return owned_v3_unsupported_words(39, 6);
}
SplArray* rt_process_owned_v3_cancel_value(int64_t handle) {
    (void)handle; return owned_v3_unsupported_words(4, 3);
}
SplArray* rt_process_owned_v3_result_value(int64_t handle) {
    (void)handle; return owned_v3_unsupported_words(15, 14);
}
SplArray* rt_process_owned_v3_collect_value(int64_t handle) {
    (void)handle; return owned_v3_unsupported_words(15, 14);
}
int rt_process_owned_v3_release_value(int64_t handle) {
    (void)handle; return 0;
}
#endif

#endif

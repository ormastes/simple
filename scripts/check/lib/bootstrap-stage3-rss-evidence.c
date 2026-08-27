#define _GNU_SOURCE

#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <limits.h>
#include <linux/memfd.h>
#include <poll.h>
#include <signal.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#ifndef EVIDENCE_BUILD_ROLE
#define EVIDENCE_BUILD_ROLE 0
#endif

#if EVIDENCE_BUILD_ROLE < 0 || EVIDENCE_BUILD_ROLE > 2
#error "EVIDENCE_BUILD_ROLE must be 0 (development), 1 (sampler), or 2 (analyzer)"
#endif

/*
 * Linux/x86 Stage-3 RSS evidence owner.
 *
 * Safety invariants:
 *   - the command and optional script are descriptor/hash bound before fork;
 *   - every owned process is keyed by (pid, /proc starttime) and signalled by
 *     pidfd only after the starttime is rechecked;
 *   - PR_SET_CHILD_SUBREAPER plus persistent membership catches setsid and
 *     double-fork descendants after the measured root exits;
 *   - every post-fork path runs bounded TERM -> KILL -> reap/scan-to-zero;
 *   - a complete terminal is appended and synced only after zero survivors;
 *   - interruption, command failure, resource limits, and sampler failures
 *     produce an analyzer-rejected failure record, never a terminal.
 */

#define RAW_SCHEMA "simple-stage3-process-rss-v1"
#define RECEIPT_SCHEMA "simple-stage3-memory-evidence-v1"
#define RECEIPT_SCHEMA_V2 "simple-stage3-memory-evidence-v2"
#define MAX_TRACKED 4096u
#define MAX_PROCS 65536u
#define MAX_BASELINE_CHILDREN 256u
#define MAX_CMDLINE_BYTES 4096u
#define MAX_ARGV_BYTES 16384u
#define MAX_RECORD_BYTES 32768u
#define DEFAULT_INTERVAL_MS 5u
#define DEFAULT_MAX_GAP_MS 50u
#define DEFAULT_MAX_RSS_KB 8388608u
#define DEFAULT_TERM_GRACE_MS 5000u
#define DEFAULT_KILL_GRACE_MS 10000u
#define DEFAULT_MAX_RUNTIME_MS 3600000u
#define DEFAULT_MAX_BATCHES 1000000u
#define DEFAULT_MAX_RECORDS 16000000u
#define DEFAULT_MAX_RAW_BYTES 1073741824u
#define CLOSURE_RESERVE_BYTES 65536u
#define CLOSURE_RESERVE_RECORDS 256u
#define SYNC_MAX_BATCHES 20u
#define SYNC_MAX_MS 100u

/* Compiler-owned streams and analyzer metadata have deliberately independent
 * limits.  Do not reuse the much larger raw process-stream limits here. */
#define COMPILER_STREAM_MAX_BYTES UINT64_C(67108864)
#define COMPILER_STREAM_MAX_RECORDS UINT64_C(1000000)
#define COMPILER_STREAM_RESERVE_BYTES UINT64_C(65536)
#define COMPILER_STREAM_RESERVE_RECORDS UINT64_C(64)
#define COMPILER_STREAM_MAX_RECORD_BYTES 65536u
#define METADATA_MAX_BYTES UINT64_C(16777216)
#define METADATA_MAX_RECORDS UINT64_C(100000)
#define METADATA_MAX_RECORD_BYTES 65536u
#define DECODED_PATH_MAX 16384u
#define DECODED_MODULE_MAX 1024u
#define DECODED_DETAIL_MAX 4096u
#define DERIVED_MAX_FILES 100u
#define DERIVED_MAX_TOTAL_BYTES UINT64_C(134217728)
#define DERIVED_MAX_FILE_BYTES UINT64_C(67108864)
#define DERIVED_MAX_RECORDS UINT64_C(1000000)
#define RECEIPT_MAX_BYTES UINT64_C(1048576)

extern char **environ;

static volatile sig_atomic_t interrupted_signal;
/* The control-signal handler owns these only until the measured executable is
 * deliberately released from its exec-stop.  Closing the one-byte gate makes
 * signal-before-gate-write and gate-write-before-signal a kernel-linearized
 * choice.  The pidfd is the identity-safe backstop after the gate write and
 * before PTRACE_DETACH completes. */
static volatile sig_atomic_t launch_gate_write_fd = -1;
static volatile sig_atomic_t pre_exec_pidfd = -1;
#ifdef EVIDENCE_TEST_HOOKS
static volatile sig_atomic_t control_signal_observation_fd = -1;
static volatile sig_atomic_t control_signal_delivery_count;
#endif

static int control_signal_priority(int sig) {
    switch (sig) {
        case SIGTERM: return 1;
        case SIGINT: return 2;
        case SIGHUP: return 3;
        case SIGQUIT: return 4;
        default: return 5;
    }
}

static void on_control_signal(int sig) {
    int saved = errno;
    sig_atomic_t prior = interrupted_signal;
    if (!prior || control_signal_priority(sig) < control_signal_priority(prior))
        interrupted_signal = sig;
#ifdef EVIDENCE_TEST_HOOKS
    sig_atomic_t observation_fd = control_signal_observation_fd;
    if (observation_fd >= 0) {
        unsigned char observed = (unsigned char)sig;
        if (write((int)observation_fd, &observed, 1) == 1)
            control_signal_delivery_count++;
    }
#endif
    sig_atomic_t gate_fd = launch_gate_write_fd;
    if (gate_fd >= 0) {
        launch_gate_write_fd = -1;
        (void)close((int)gate_fd);
    }
    sig_atomic_t pidfd = pre_exec_pidfd;
    if (pidfd >= 0)
        (void)syscall(SYS_pidfd_send_signal, (int)pidfd, SIGKILL, NULL, 0);
    errno = saved;
}

static int pending_control_signal(void) {
    sigset_t pending;
    if (sigpending(&pending) != 0) return -1;
    if (sigismember(&pending, SIGTERM) == 1) return SIGTERM;
    if (sigismember(&pending, SIGINT) == 1) return SIGINT;
    if (sigismember(&pending, SIGHUP) == 1) return SIGHUP;
    if (sigismember(&pending, SIGQUIT) == 1) return SIGQUIT;
    return 0;
}

static uint64_t mono_ns(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return 0;
    return (uint64_t)ts.tv_sec * UINT64_C(1000000000) + (uint64_t)ts.tv_nsec;
}

static int sleep_ms(uint64_t ms) {
    struct timespec ts = {
        .tv_sec = (time_t)(ms / 1000),
        .tv_nsec = (long)((ms % 1000) * 1000000),
    };
    while (nanosleep(&ts, &ts) != 0) {
        if (errno != EINTR) return -1;
        if (interrupted_signal) return 0;
    }
    return 0;
}

static int evidence_clock_nanosleep(const struct timespec *deadline) {
#ifdef EVIDENCE_TEST_HOOKS
    static int injected;
    const char *hook = getenv("SIMPLE_STAGE3_RSS_TEST_CLOCK_NANOSLEEP");
    if (!injected && hook) {
        injected = 1;
        if (!strcmp(hook, "eintr-errno-einval")) {
            errno = EINVAL;
            return EINTR;
        }
        if (!strcmp(hook, "einval-errno-eintr")) {
            errno = EINTR;
            return EINVAL;
        }
    }
#endif
    return clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, deadline, NULL);
}

static int sleep_until_ns(uint64_t deadline_ns) {
    struct timespec deadline = {
        .tv_sec = (time_t)(deadline_ns / UINT64_C(1000000000)),
        .tv_nsec = (long)(deadline_ns % UINT64_C(1000000000)),
    };
    for (;;) {
        int rc = evidence_clock_nanosleep(&deadline);
        if (rc == 0) return 0;
        if (rc != EINTR) return -1;
        if (interrupted_signal) return 0;
    }
}

static int terminal_durability_sync(int fd) {
#ifdef EVIDENCE_TEST_HOOKS
    if (getenv("SIMPLE_STAGE3_RSS_TEST_FAIL_TERMINAL_DURABILITY_SYNC")) {
        errno = EIO;
        return -1;
    }
#endif
    return fdatasync(fd);
}

static int created_output_parent_sync(int fd) {
#ifdef EVIDENCE_TEST_HOOKS
    if (getenv("SIMPLE_STAGE3_RSS_TEST_FAIL_CREATED_OUTPUT_PARENT_SYNC")) {
        errno = EIO;
        return -1;
    }
#endif
    return fsync(fd);
}

static int quarantine_raw_unlink(int parent_fd, const char *leaf) {
#ifdef EVIDENCE_TEST_HOOKS
    if (getenv("SIMPLE_STAGE3_RSS_TEST_FAIL_QUARANTINE_UNLINK")) {
        errno = EIO;
        return -1;
    }
#endif
    return unlinkat(parent_fd, leaf, 0);
}

static int quarantine_raw_parent_sync(int parent_fd) {
#ifdef EVIDENCE_TEST_HOOKS
    if (getenv("SIMPLE_STAGE3_RSS_TEST_FAIL_QUARANTINE_PARENT_SYNC")) {
        errno = EIO;
        return -1;
    }
#endif
    return fsync(parent_fd);
}

static int terminal_rollback_sync(int fd) {
    int result = fdatasync(fd);
#ifdef EVIDENCE_TEST_HOOKS
    if (result == 0 &&
        getenv("SIMPLE_STAGE3_RSS_TEST_TRACE_TERMINAL_ROLLBACK_SYNC"))
        fprintf(stderr, "terminal rollback fdatasync committed\n");
#endif
    return result;
}

static uint64_t deadline_after_ms(uint64_t now_ns, uint64_t delta_ms) {
    uint64_t delta_ns = delta_ms * UINT64_C(1000000);
    return now_ns > UINT64_MAX - delta_ns ? UINT64_MAX : now_ns + delta_ns;
}

static int parse_u64(const char *text, uint64_t *out) {
    if (!text || !*text || text[0] == '-' || text[0] == '+' ||
        (text[0] == '0' && text[1])) return -1;
    uint64_t value = 0;
    for (const unsigned char *p = (const unsigned char *)text; *p; ++p) {
        if (!isdigit(*p)) return -1;
        unsigned digit = (unsigned)(*p - '0');
        if (value > (UINT64_MAX - digit) / 10) return -1;
        value = value * 10 + digit;
    }
    *out = value;
    return 0;
}

#ifdef EVIDENCE_TEST_HOOKS
static int parse_pid(const char *text, pid_t *out) {
    uint64_t value;
    if (parse_u64(text, &value) != 0 || value == 0 || value > INT_MAX) return -1;
    *out = (pid_t)value;
    return 0;
}
#endif

static int safe_run_id(const char *text) {
    size_t n = text ? strlen(text) : 0;
    if (n < 8 || n > 64) return 0;
    for (size_t i = 0; i < n; ++i) {
        unsigned char c = (unsigned char)text[i];
        if (!((c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
              (c >= '0' && c <= '9') || c == '-' || c == '_')) return 0;
    }
    return 1;
}

static int valid_sha256(const char *text) {
    if (!text || strlen(text) != 64) return 0;
    for (size_t i = 0; i < 64; ++i)
        if (!isdigit((unsigned char)text[i]) && (text[i] < 'a' || text[i] > 'f')) return 0;
    return 1;
}

static int valid_hex(const char *text, size_t max_bytes) {
    size_t n = text ? strlen(text) : 0;
    if (!n || (n & 1u) || n > max_bytes * 2) return 0;
    for (size_t i = 0; i < n; ++i)
        if (!isdigit((unsigned char)text[i]) && (text[i] < 'a' || text[i] > 'f')) return 0;
    return 1;
}

/* Dependency-free SHA-256 keeps executable/input identity independent of PATH. */
typedef struct {
    uint32_t h[8];
    uint64_t bytes;
    unsigned char block[64];
    size_t used;
} Sha256;

static uint32_t ror32(uint32_t x, unsigned n) { return (x >> n) | (x << (32 - n)); }

static void sha256_transform(Sha256 *s, const unsigned char *p) {
    static const uint32_t k[64] = {
        0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
        0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
        0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
        0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
        0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
        0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
        0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
        0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2,
    };
    uint32_t w[64], a, b, c, d, e, f, g, h;
    for (int i = 0; i < 16; ++i)
        w[i] = (uint32_t)p[4*i] << 24 | (uint32_t)p[4*i+1] << 16 |
               (uint32_t)p[4*i+2] << 8 | p[4*i+3];
    for (int i = 16; i < 64; ++i) {
        uint32_t x = w[i-15], y = w[i-2];
        w[i] = (ror32(x,7)^ror32(x,18)^(x>>3)) + w[i-16] +
               (ror32(y,17)^ror32(y,19)^(y>>10)) + w[i-7];
    }
    a=s->h[0]; b=s->h[1]; c=s->h[2]; d=s->h[3];
    e=s->h[4]; f=s->h[5]; g=s->h[6]; h=s->h[7];
    for (int i = 0; i < 64; ++i) {
        uint32_t p1 = h + (ror32(e,6)^ror32(e,11)^ror32(e,25)) +
                      ((e&f)^(~e&g)) + k[i] + w[i];
        uint32_t p2 = (ror32(a,2)^ror32(a,13)^ror32(a,22)) +
                      ((a&b)^(a&c)^(b&c));
        h=g; g=f; f=e; e=d+p1; d=c; c=b; b=a; a=p1+p2;
    }
    s->h[0]+=a; s->h[1]+=b; s->h[2]+=c; s->h[3]+=d;
    s->h[4]+=e; s->h[5]+=f; s->h[6]+=g; s->h[7]+=h;
}

static void sha256_init(Sha256 *s) {
    static const uint32_t init[8] = {
        0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,
        0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19,
    };
    memset(s, 0, sizeof(*s));
    memcpy(s->h, init, sizeof(init));
}

static void sha256_update(Sha256 *s, const void *data, size_t n) {
    const unsigned char *p = data;
    s->bytes += n;
    while (n) {
        size_t take = 64 - s->used;
        if (take > n) take = n;
        memcpy(s->block + s->used, p, take);
        s->used += take; p += take; n -= take;
        if (s->used == 64) { sha256_transform(s, s->block); s->used = 0; }
    }
}

static void sha256_final(Sha256 *s, unsigned char digest[32]) {
    uint64_t bits = s->bytes * 8;
    unsigned char byte = 0x80;
    sha256_update(s, &byte, 1);
    byte = 0;
    while (s->used != 56) sha256_update(s, &byte, 1);
    unsigned char length[8];
    for (int i = 0; i < 8; ++i) length[7-i] = (unsigned char)(bits >> (8*i));
    sha256_update(s, length, sizeof(length));
    for (int i = 0; i < 8; ++i) {
        digest[4*i] = (unsigned char)(s->h[i] >> 24);
        digest[4*i+1] = (unsigned char)(s->h[i] >> 16);
        digest[4*i+2] = (unsigned char)(s->h[i] >> 8);
        digest[4*i+3] = (unsigned char)s->h[i];
    }
}

static int hash_fd(int fd, char hex[65]) {
    if (lseek(fd, 0, SEEK_SET) < 0) return -1;
    Sha256 sha;
    sha256_init(&sha);
    unsigned char buffer[32768], digest[32];
    for (;;) {
        ssize_t n = read(fd, buffer, sizeof(buffer));
        if (n < 0) { if (errno == EINTR) continue; return -1; }
        if (!n) break;
        sha256_update(&sha, buffer, (size_t)n);
    }
    sha256_final(&sha, digest);
    for (int i = 0; i < 32; ++i) snprintf(hex + 2*i, 3, "%02x", digest[i]);
    hex[64] = 0;
    return lseek(fd, 0, SEEK_SET) < 0 ? -1 : 0;
}

typedef struct {
    uint64_t dev;
    uint64_t ino;
    char sha256[65];
} FileIdentity;

static int identity_fd(int fd, FileIdentity *identity) {
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) || hash_fd(fd, identity->sha256) != 0)
        return -1;
    struct stat after;
    if (fstat(fd, &after) != 0 || st.st_dev != after.st_dev || st.st_ino != after.st_ino ||
        st.st_size != after.st_size) return -1;
    identity->dev = (uint64_t)st.st_dev;
    identity->ino = (uint64_t)st.st_ino;
    return 0;
}

static int open_identity_nofollow(const char *path, FileIdentity *identity) {
    int fd = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return -1;
    if (identity_fd(fd, identity) != 0) { close(fd); return -1; }
    return fd;
}

static int self_identity(FileIdentity *identity) {
    int fd = open("/proc/self/exe", O_RDONLY | O_CLOEXEC);
    if (fd < 0) return -1;
    int result = identity_fd(fd, identity);
    close(fd);
    return result;
}

static int sealed_snapshot_fd(int source_fd, const FileIdentity *source_identity,
                              FileIdentity *snapshot_identity) {
    int snapshot = (int)syscall(SYS_memfd_create, "stage3-evidence-script",
                                MFD_CLOEXEC | MFD_ALLOW_SEALING);
    if (snapshot < 0 || lseek(source_fd, 0, SEEK_SET) < 0) {
        if (snapshot >= 0) close(snapshot);
        return -1;
    }
    unsigned char buffer[32768];
    for (;;) {
        ssize_t n = read(source_fd, buffer, sizeof(buffer));
        if (n < 0) { if (errno == EINTR) continue; close(snapshot); return -1; }
        if (!n) break;
        size_t off = 0;
        while (off < (size_t)n) {
            ssize_t written = write(snapshot, buffer + off, (size_t)n - off);
            if (written < 0) { if (errno == EINTR) continue; close(snapshot); return -1; }
            if (!written) { close(snapshot); errno = EIO; return -1; }
            off += (size_t)written;
        }
    }
    FileIdentity source_after;
    if (identity_fd(source_fd, &source_after) != 0 ||
        source_after.dev != source_identity->dev || source_after.ino != source_identity->ino ||
        strcmp(source_after.sha256, source_identity->sha256) ||
        fcntl(snapshot, F_ADD_SEALS, F_SEAL_WRITE|F_SEAL_GROW|F_SEAL_SHRINK|F_SEAL_SEAL) != 0 ||
        identity_fd(snapshot, snapshot_identity) != 0 ||
        strcmp(snapshot_identity->sha256, source_identity->sha256)) {
        close(snapshot);
        return -1;
    }
    return snapshot;
}

static char *hex_encode(const unsigned char *data, size_t n) {
    static const char digits[] = "0123456789abcdef";
    char *out = malloc(n * 2 + 1);
    if (!out) return NULL;
    for (size_t i = 0; i < n; ++i) {
        out[2*i] = digits[data[i] >> 4];
        out[2*i+1] = digits[data[i] & 15];
    }
    out[2*n] = 0;
    return out;
}

static char *encode_argv(char *const argv[]) {
    size_t bytes = 0;
    for (size_t i = 0; argv[i]; ++i) {
        size_t n = strlen(argv[i]) + 1;
        if (n > MAX_ARGV_BYTES - bytes) return NULL;
        bytes += n;
    }
    unsigned char *raw = malloc(bytes ? bytes : 1);
    if (!raw) return NULL;
    size_t off = 0;
    for (size_t i = 0; argv[i]; ++i) {
        size_t n = strlen(argv[i]) + 1;
        memcpy(raw + off, argv[i], n);
        off += n;
    }
    char *encoded = hex_encode(raw, bytes);
    free(raw);
    return encoded;
}

static int parent_dir_fd(const char *path, char leaf[NAME_MAX + 1]) {
    char copy[PATH_MAX];
    if (!path || !*path || strlen(path) >= sizeof(copy)) { errno = EINVAL; return -1; }
    strcpy(copy, path);
    char *slash = strrchr(copy, '/');
    const char *base;
    if (slash) {
        base = slash + 1;
        if (slash == copy) slash[1] = 0; else *slash = 0;
    } else {
        strcpy(copy, ".");
        base = path;
    }
    if (!*base || strlen(base) > NAME_MAX || strchr(base, '/')) { errno = EINVAL; return -1; }
    strcpy(leaf, base);
    int dir = open(copy[0] == '/' ? "/" : ".", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (dir < 0) return -1;
    char *part = copy + (copy[0] == '/');
    while (*part) {
        while (*part == '/') ++part;
        if (!*part) break;
        char *next = strchr(part, '/');
        if (next) *next = 0;
        int child = openat(dir, part, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
        close(dir);
        if (child < 0) return -1;
        dir = child;
        if (!next) break;
        part = next + 1;
    }
    return dir;
}

typedef struct {
    int fd;
    int parent_fd;
    char leaf[NAME_MAX + 1];
    uint64_t dev;
    uint64_t ino;
} RawTarget;

static int open_absent_append(const char *path, RawTarget *target) {
    memset(target, 0, sizeof(*target));
    target->fd = target->parent_fd = -1;
    char leaf[NAME_MAX + 1];
    int parent = parent_dir_fd(path, leaf);
    if (parent < 0) return -1;
    int fd = openat(parent, leaf,
                    O_WRONLY | O_CREAT | O_EXCL | O_APPEND | O_NOFOLLOW | O_CLOEXEC,
                    0600);
    if (fd < 0) { int saved = errno; close(parent); errno = saved; return -1; }
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) || st.st_nlink != 1) {
        int saved = errno ? errno : EINVAL;
        close(fd); unlinkat(parent, leaf, 0); close(parent); errno = saved; return -1;
    }
    target->fd = fd;
    target->parent_fd = parent;
    strcpy(target->leaf, leaf);
    target->dev = (uint64_t)st.st_dev;
    target->ino = (uint64_t)st.st_ino;
    if (fsync(parent) != 0) {
        int saved = errno;
        close(fd);
        (void)unlinkat(parent, leaf, 0);
        (void)fsync(parent);
        close(parent);
        errno = saved;
        return -1;
    }
    return 0;
}

static int raw_target_matches(const RawTarget *target) {
    struct stat opened, visible;
    return fstat(target->fd, &opened) == 0 && S_ISREG(opened.st_mode) && opened.st_nlink == 1 &&
           fstatat(target->parent_fd, target->leaf, &visible, AT_SYMLINK_NOFOLLOW) == 0 &&
           S_ISREG(visible.st_mode) && visible.st_nlink == 1 &&
           (uint64_t)opened.st_dev == target->dev && (uint64_t)opened.st_ino == target->ino &&
           opened.st_dev == visible.st_dev && opened.st_ino == visible.st_ino;
}

static void close_raw_target(RawTarget *target) {
    if (target->fd >= 0) close(target->fd);
    if (target->parent_fd >= 0) close(target->parent_fd);
    target->fd = target->parent_fd = -1;
}

typedef struct {
    int fd;
    uint64_t bytes;
    uint64_t data_records;
    uint64_t control_records;
    uint64_t control_bytes;
    uint64_t max_bytes;
    uint64_t max_records;
    uint64_t batches_since_sync;
    uint64_t last_sync_ns;
#ifdef EVIDENCE_TEST_HOOKS
    uint64_t fail_write_after;
    uint64_t fail_sync_after;
    uint64_t sync_calls;
    uint64_t short_write_after;
#endif
} RawWriter;

static int writer_sync(RawWriter *writer, int force) {
    uint64_t now = mono_ns();
    if (!now) return -1;
    int due = force || writer->batches_since_sync >= SYNC_MAX_BATCHES ||
              !writer->last_sync_ns ||
              now - writer->last_sync_ns >= SYNC_MAX_MS * UINT64_C(1000000);
    if (!due) return 0;
#ifdef EVIDENCE_TEST_HOOKS
    if (writer->fail_sync_after && writer->sync_calls++ >= writer->fail_sync_after) {
        errno = EIO;
        return -1;
    }
#endif
    if (fdatasync(writer->fd) != 0) return -1;
    writer->last_sync_ns = mono_ns();
    if (!writer->last_sync_ns) return -1;
    writer->batches_since_sync = 0;
    return 0;
}

static int writer_blob_mode(RawWriter *writer, int control, int complete_batch,
                            const char *data, size_t length, uint64_t records) {
    if (!length || !records || data[length-1] != '\n' ||
        writer->bytes > writer->max_bytes ||
        (uint64_t)length > writer->max_bytes - writer->bytes ||
        (!control && (writer->data_records > writer->max_records ||
                      writer->bytes > writer->max_bytes - CLOSURE_RESERVE_BYTES ||
                      (uint64_t)length > writer->max_bytes - CLOSURE_RESERVE_BYTES - writer->bytes ||
                      writer->max_records < CLOSURE_RESERVE_RECORDS ||
                      writer->data_records > writer->max_records - CLOSURE_RESERVE_RECORDS ||
                      records > writer->max_records - CLOSURE_RESERVE_RECORDS - writer->data_records)) ||
        (control && ((uint64_t)length > CLOSURE_RESERVE_BYTES - writer->control_bytes ||
                     records > CLOSURE_RESERVE_RECORDS - writer->control_records))) {
        errno = EFBIG;
        return -1;
    }
#ifdef EVIDENCE_TEST_HOOKS
    if (writer->fail_write_after && writer->data_records >= writer->fail_write_after) {
        errno = EIO;
        return -1;
    }
    if (!control && writer->short_write_after &&
        writer->data_records >= writer->short_write_after) {
        size_t partial = length > 1 ? length / 2 : 1;
        ssize_t written;
        do { written = write(writer->fd, data, partial); } while (written < 0 && errno == EINTR);
        errno = EIO;
        return -1;
    }
#endif
    size_t offset = 0;
    while (offset < length) {
        ssize_t n = write(writer->fd, data + offset, length - offset);
        if (n < 0) { if (errno == EINTR) continue; return -1; }
        if (!n) { errno = EIO; return -1; }
        offset += (size_t)n;
    }
    writer->bytes += (uint64_t)length;
    if (control) {
        writer->control_bytes += (uint64_t)length;
        writer->control_records += records;
    } else {
        writer->data_records += records;
        if (complete_batch) writer->batches_since_sync++;
    }
    return complete_batch || control ? writer_sync(writer, control) : 0;
}

static int writer_blob(RawWriter *writer, int control, const char *data, size_t length,
                       uint64_t records) {
    return writer_blob_mode(writer, control, !control, data, length, records);
}

static int writer_record(RawWriter *writer, int control, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    char *record = NULL;
    int length = vasprintf(&record, fmt, ap);
    va_end(ap);
    if (length <= 0 || !record || (size_t)length > MAX_RECORD_BYTES || record[length-1] != '\n') {
        free(record); errno = EINVAL; return -1;
    }
    int result = writer_blob(writer, control, record, (size_t)length, 1);
    free(record);
    return result;
}

static int writer_data_record_unsynced(RawWriter *writer, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    char *record = NULL;
    int length = vasprintf(&record, fmt, ap);
    va_end(ap);
    if (length <= 0 || !record || (size_t)length > MAX_RECORD_BYTES || record[length-1] != '\n') {
        free(record); errno = EINVAL; return -1;
    }
    int result = writer_blob_mode(writer, 0, 0, record, (size_t)length, 1);
    free(record);
    return result;
}

typedef struct {
    pid_t pid, ppid, pgrp, sid;
    uint64_t start;
    char state;
    uint64_t rss, hwm, anon, file;
} Proc;

static int proc_stat(pid_t pid, Proc *out) {
    char path[64], buffer[4096];
    snprintf(path, sizeof(path), "/proc/%ld/stat", (long)pid);
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return -1;
    ssize_t n;
    do { n = read(fd, buffer, sizeof(buffer) - 1); } while (n < 0 && errno == EINTR);
    int saved = errno;
    close(fd);
    errno = saved;
    if (n <= 0) return -1;
    buffer[n] = 0;
    char *right = strrchr(buffer, ')');
    if (!right || right[1] != ' ') { errno = EPROTO; return -1; }
    char *save = NULL;
    char *token = strtok_r(right + 2, " ", &save);
    int field = 3;
    memset(out, 0, sizeof(*out));
    out->pid = pid;
    while (token) {
        if (field == 3) {
            if (strlen(token) != 1) { errno = EPROTO; return -1; }
            out->state = token[0];
        } else if (field == 4 || field == 5 || field == 6) {
            uint64_t value;
            if (parse_u64(token, &value) != 0 || value > INT_MAX) { errno = EPROTO; return -1; }
            if (field == 4) out->ppid = (pid_t)value;
            if (field == 5) out->pgrp = (pid_t)value;
            if (field == 6) out->sid = (pid_t)value;
        } else if (field == 22) {
            if (parse_u64(token, &out->start) != 0 || !out->start) { errno = EPROTO; return -1; }
            return 0;
        }
        ++field;
        token = strtok_r(NULL, " ", &save);
    }
    errno = EPROTO;
    return -1;
}

#ifdef EVIDENCE_TEST_HOOKS
static int publish_pre_gate_ready(const char *path, const sigset_t *controls,
                                  pid_t sampler_pid) {
    if (!path || !*path) return 0;
    sigset_t blocked;
    Proc sampler;
    if (sigprocmask(SIG_SETMASK, NULL, &blocked) != 0 ||
        proc_stat(sampler_pid, &sampler) != 0) return -1;
    for (int sig = 1; sig < NSIG; ++sig) {
        if (sigismember(controls, sig) == 1 && sigismember(&blocked, sig) != 1) {
            errno = EINVAL;
            return -1;
        }
    }
    int fd = open(path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC, 0600);
    if (fd < 0) return -1;
    char ready[128];
    int length = snprintf(ready, sizeof(ready), "blocked-pre-gate %ld %" PRIu64 "\n",
                          (long)sampler_pid, sampler.start);
    ssize_t wrote = length > 0 && (size_t)length < sizeof(ready)
        ? write(fd, ready, (size_t)length) : -1;
    int failed = 0;
    int saved = 0;
    if (wrote != length) {
        failed = 1;
        saved = wrote < 0 ? errno : EIO;
    } else if (fdatasync(fd) != 0) {
        failed = 1;
        saved = errno;
    }
    if (close(fd) != 0 && !failed) {
        failed = 1;
        saved = errno;
    }
    if (!failed) return 0;
    errno = saved;
    return -1;
}

static int test_write_all(int fd, const char *text, size_t length) {
    size_t offset = 0;
    while (offset < length) {
        ssize_t wrote = write(fd, text + offset, length - offset);
        if (wrote > 0) offset += (size_t)wrote;
        else if (wrote < 0 && errno == EINTR) continue;
        else { errno = wrote == 0 ? EIO : errno; return -1; }
    }
    return 0;
}

static int test_fifo_barrier(const char *ready_path, const char *continue_path,
                             const char *record) {
    if (!ready_path || ready_path[0] != '/' || !continue_path || continue_path[0] != '/') {
        errno = EINVAL;
        return -1;
    }
    /* Open and validate the continuation endpoint first. A reader that receives
     * the ready record therefore knows there is no signal-before-open window. */
    int continue_fd = open(continue_path,
                           O_RDONLY | O_NONBLOCK | O_NOFOLLOW | O_CLOEXEC);
    if (continue_fd < 0) return -1;
    struct stat continue_stat;
    int failed = fstat(continue_fd, &continue_stat) != 0;
    if (!failed && !S_ISFIFO(continue_stat.st_mode)) { errno = EINVAL; failed = 1; }
    int saved = failed ? errno : 0;
    if (failed) {
        (void)close(continue_fd);
        errno = saved;
        return -1;
    }

    int ready_fd = open(ready_path, O_WRONLY | O_NOFOLLOW | O_CLOEXEC);
    if (ready_fd < 0) { saved = errno; (void)close(continue_fd); errno = saved; return -1; }
    struct stat ready_stat;
    failed = fstat(ready_fd, &ready_stat) != 0;
    if (!failed && !S_ISFIFO(ready_stat.st_mode)) { errno = EINVAL; failed = 1; }
    if (!failed && test_write_all(ready_fd, record, strlen(record)) != 0) failed = 1;
    saved = failed ? errno : 0;
    if (close(ready_fd) != 0 && !failed) { failed = 1; saved = errno; }
    if (failed) {
        (void)close(continue_fd);
        errno = saved;
        return -1;
    }

    uint64_t deadline = deadline_after_ms(mono_ns(), 5000);
    char byte;
    while (!failed) {
        ssize_t got = read(continue_fd, &byte, 1);
        if (got == 1) break;
        if (got < 0 && errno != EINTR && errno != EAGAIN && errno != EWOULDBLOCK) {
            failed = 1;
            break;
        }
        if (interrupted_signal) { errno = EINTR; failed = 1; break; }
        if (mono_ns() >= deadline) { errno = ETIMEDOUT; failed = 1; break; }
        struct timespec tick = { .tv_sec = 0, .tv_nsec = 1000000 };
        while (nanosleep(&tick, &tick) != 0 && errno == EINTR && !interrupted_signal) {}
    }
    saved = failed ? errno : 0;
    if (close(continue_fd) != 0 && !failed) { failed = 1; saved = errno; }
    if (failed) { errno = saved; return -1; }
    return 0;
}

static int child_post_gate_barrier(void) {
    const char *ready = getenv("SIMPLE_STAGE3_RSS_TEST_CHILD_POST_GATE_READY_FIFO");
    const char *proceed = getenv("SIMPLE_STAGE3_RSS_TEST_CHILD_POST_GATE_CONTINUE_FIFO");
    if (!ready && !proceed) return 0;
    Proc child;
    if (proc_stat(getpid(), &child) != 0) return -1;
    char record[160];
    int length = snprintf(record, sizeof(record), "child-post-gate %ld %" PRIu64 "\n",
                          (long)child.pid, child.start);
    if (length <= 0 || (size_t)length >= sizeof(record)) { errno = EOVERFLOW; return -1; }
    return test_fifo_barrier(ready, proceed, record);
}

static int parent_exec_stop_barrier(pid_t parent_pid, const Proc *child) {
    const char *ready = getenv("SIMPLE_STAGE3_RSS_TEST_PARENT_EXEC_STOP_READY_FIFO");
    const char *proceed = getenv("SIMPLE_STAGE3_RSS_TEST_PARENT_EXEC_STOP_CONTINUE_FIFO");
    if (!ready && !proceed) return 0;
    Proc parent;
    if (proc_stat(parent_pid, &parent) != 0) return -1;
    char record[256];
    int length = snprintf(record, sizeof(record),
        "parent-ptrace-exec-stop %ld %" PRIu64 " %ld %" PRIu64 "\n",
        (long)parent.pid, parent.start, (long)child->pid, child->start);
    if (length <= 0 || (size_t)length >= sizeof(record)) { errno = EOVERFLOW; return -1; }
    return test_fifo_barrier(ready, proceed, record);
}

static int wait_for_test_signal_deliveries(uint64_t expected) {
    if (!expected) return 0;
    uint64_t deadline = deadline_after_ms(mono_ns(), 5000);
    struct timespec tick = { .tv_sec = 0, .tv_nsec = 1000000 };
    while ((uint64_t)control_signal_delivery_count < expected) {
        if (mono_ns() >= deadline) { errno = ETIMEDOUT; return -1; }
        struct timespec remaining = tick;
        while (nanosleep(&remaining, &remaining) != 0 && errno == EINTR) {}
    }
    return 0;
}

static long evidence_ptrace_detach(pid_t pid, int signal_value) {
    int injected_errno = signal_value == 0 &&
        getenv("SIMPLE_STAGE3_RSS_TEST_FAIL_ZERO_SIGNAL_DETACH") ? EIO : 0;
    const char *observation = getenv("SIMPLE_STAGE3_RSS_TEST_DETACH_OBSERVATION_PATH");
    if (observation) {
        if (observation[0] != '/') { errno = EINVAL; return -1; }
        int fd = open(observation, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0600);
        if (fd < 0) return -1;
        char record[64];
        int length = snprintf(record, sizeof(record),
                              "detach signal=%d injected_errno=%d\n",
                              signal_value, injected_errno);
        int failed = length <= 0 || (size_t)length >= sizeof(record) ||
                     test_write_all(fd, record, (size_t)length) != 0 || fdatasync(fd) != 0;
        int saved = failed ? errno : 0;
        if (close(fd) != 0 && !failed) { failed = 1; saved = errno; }
        if (failed) { errno = saved; return -1; }
    }
    if (injected_errno) {
        errno = injected_errno;
        return -1;
    }
    return ptrace(PTRACE_DETACH, pid, NULL, (void *)(uintptr_t)signal_value);
}
#endif

#ifndef EVIDENCE_TEST_HOOKS
static long evidence_ptrace_detach(pid_t pid, int signal_value) {
    return ptrace(PTRACE_DETACH, pid, NULL, (void *)(uintptr_t)signal_value);
}
#endif

static int proc_memory(Proc *proc) {
    char path[64], line[256];
    snprintf(path, sizeof(path), "/proc/%ld/status", (long)proc->pid);
    FILE *file = fopen(path, "re");
    if (!file) return -1;
    unsigned mask = 0;
    while (fgets(line, sizeof(line), file)) {
        uint64_t value;
        char key[32], unit[8];
        if (sscanf(line, "%31[^:]: %" SCNu64 " %7s", key, &value, unit) != 3 ||
            strcmp(unit, "kB") != 0) continue;
        if (!strcmp(key, "VmRSS")) { proc->rss = value; mask |= 1; }
        else if (!strcmp(key, "VmHWM")) { proc->hwm = value; mask |= 2; }
        else if (!strcmp(key, "RssAnon")) { proc->anon = value; mask |= 4; }
        else if (!strcmp(key, "RssFile")) { proc->file = value; mask |= 8; }
    }
    int failed = ferror(file);
    fclose(file);
    return failed || mask != 15 ? -1 : 0;
}

static char *proc_argv_hex(pid_t pid) {
    char path[64];
    snprintf(path, sizeof(path), "/proc/%ld/cmdline", (long)pid);
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return NULL;
    unsigned char data[MAX_CMDLINE_BYTES + 1];
    size_t used = 0;
    for (;;) {
        ssize_t n = read(fd, data + used, sizeof(data) - used);
        if (n < 0) { if (errno == EINTR) continue; close(fd); return NULL; }
        if (!n) break;
        used += (size_t)n;
        if (used == sizeof(data)) { close(fd); errno = E2BIG; return NULL; }
    }
    close(fd);
    if (!used) { data[used++] = 0; }
    return hex_encode(data, used);
}

static int proc_executable_matches(pid_t pid, const FileIdentity *identity) {
    char path[64];
    snprintf(path, sizeof(path), "/proc/%ld/exe", (long)pid);
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return 0;
    struct stat st;
    int matches = fstat(fd, &st) == 0 && S_ISREG(st.st_mode) &&
                  (uint64_t)st.st_dev == identity->dev && (uint64_t)st.st_ino == identity->ino;
    close(fd);
    return matches;
}

typedef struct {
    pid_t pid;
    uint64_t start;
    int pidfd;
    int alive;
    int term_sent;
    int kill_sent;
} Member;

typedef struct {
    uint64_t interval_ms, max_gap_ms, max_rss_kb;
    uint64_t term_grace_ms, kill_grace_ms, max_runtime_ms;
    uint64_t max_batches, max_records, max_raw_bytes;
    uint64_t max_tracked, closure_reserve_bytes, closure_reserve_records;
} RunConfig;

typedef struct {
    pid_t root_pid;
    uint64_t root_start;
    pid_t self_pid;
    pid_t outer_pgid;
    Member members[MAX_TRACKED];
    size_t member_count;
    Proc *snapshot;
    unsigned char *belongs;
    size_t snapshot_count;
    pid_t baseline_pid[MAX_BASELINE_CHILDREN];
    uint64_t baseline_start[MAX_BASELINE_CHILDREN];
    size_t baseline_count;
    int root_reaped;
    int root_status;
    int identity_error;
    int cleanup_started;
} Supervisor;

static int pidfd_open_checked(pid_t pid, uint64_t start) {
    int fd = (int)syscall(SYS_pidfd_open, pid, 0);
    if (fd < 0) return -1;
    Proc check;
    if (proc_stat(pid, &check) != 0 || check.start != start) {
        close(fd); errno = ESTALE; return -1;
    }
    return fd;
}

static int member_index(const Supervisor *supervisor, pid_t pid, uint64_t start) {
    for (size_t i = 0; i < supervisor->member_count; ++i)
        if (supervisor->members[i].pid == pid && supervisor->members[i].start == start)
            return (int)i;
    return -1;
}

static int member_pid_seen_different(const Supervisor *supervisor, pid_t pid, uint64_t start) {
    for (size_t i = 0; i < supervisor->member_count; ++i)
        if (supervisor->members[i].pid == pid && supervisor->members[i].start != start)
            return 1;
    return 0;
}

static int add_member(Supervisor *supervisor, const Proc *proc) {
    if (member_index(supervisor, proc->pid, proc->start) >= 0) return 0;
    if (member_pid_seen_different(supervisor, proc->pid, proc->start)) {
        supervisor->identity_error = 1; errno = ESTALE; return -1;
    }
    size_t persistent_cap = MAX_TRACKED;
#ifdef EVIDENCE_TEST_HOOKS
    const char *cap_text = getenv("SIMPLE_STAGE3_RSS_TEST_PERSISTENT_MEMBER_CAP");
    uint64_t cap_value = 0;
    if (cap_text && parse_u64(cap_text, &cap_value) == 0 &&
        cap_value > 0 && cap_value <= MAX_TRACKED)
        persistent_cap = (size_t)cap_value;
#endif
    if (supervisor->member_count == persistent_cap) { errno = E2BIG; return -1; }
    int pidfd = pidfd_open_checked(proc->pid, proc->start);
    if (pidfd < 0) {
        if (errno == ESRCH || errno == ENOENT || errno == ESTALE) return 0;
        return -1;
    }
    Member *member = &supervisor->members[supervisor->member_count++];
    *member = (Member){ .pid=proc->pid, .start=proc->start, .pidfd=pidfd, .alive=1 };
    return 0;
}

static int baseline_contains(const Supervisor *supervisor, pid_t pid, uint64_t start) {
    for (size_t i = 0; i < supervisor->baseline_count; ++i)
        if (supervisor->baseline_pid[i] == pid && supervisor->baseline_start[i] == start) return 1;
    return 0;
}

static int scan_all_procs(Supervisor *supervisor) {
    supervisor->snapshot_count = 0;
    DIR *dir = opendir("/proc");
    if (!dir) return -1;
    struct dirent *entry;
    while ((entry = readdir(dir))) {
        char *end = NULL;
        errno = 0;
        long value = strtol(entry->d_name, &end, 10);
        if (errno || !*entry->d_name || *end || value <= 0 || value > INT_MAX) continue;
        if (supervisor->snapshot_count == MAX_PROCS) { closedir(dir); errno = E2BIG; return -1; }
        Proc proc;
        if (proc_stat((pid_t)value, &proc) == 0)
            supervisor->snapshot[supervisor->snapshot_count++] = proc;
    }
    if (closedir(dir) != 0) return -1;
    return 0;
}

static int snapshot_index_pid(const Supervisor *supervisor, pid_t pid) {
    for (size_t i = 0; i < supervisor->snapshot_count; ++i)
        if (supervisor->snapshot[i].pid == pid) return (int)i;
    return -1;
}

static int discover_tree(Supervisor *supervisor) {
#ifdef EVIDENCE_TEST_HOOKS
    static int injected_cleanup_discovery_failure;
    if (supervisor->cleanup_started && !injected_cleanup_discovery_failure &&
        getenv("SIMPLE_STAGE3_RSS_TEST_FAIL_CLEANUP_DISCOVERY_ONCE")) {
        injected_cleanup_discovery_failure = 1;
        errno = EIO;
        return -1;
    }
#endif
    if (scan_all_procs(supervisor) != 0) return -1;
    memset(supervisor->belongs, 0, supervisor->snapshot_count);
    for (size_t i = 0; i < supervisor->snapshot_count; ++i) {
        Proc *proc = &supervisor->snapshot[i];
        if ((proc->pid == supervisor->root_pid && proc->start == supervisor->root_start) ||
            member_index(supervisor, proc->pid, proc->start) >= 0 ||
            (proc->ppid == supervisor->self_pid && proc->pid != supervisor->self_pid &&
             !baseline_contains(supervisor, proc->pid, proc->start)))
            supervisor->belongs[i] = 1;
        if (member_pid_seen_different(supervisor, proc->pid, proc->start))
            supervisor->identity_error = 1;
    }
    int changed;
    do {
        changed = 0;
        for (size_t i = 0; i < supervisor->snapshot_count; ++i) {
            if (supervisor->belongs[i]) continue;
            int parent = snapshot_index_pid(supervisor, supervisor->snapshot[i].ppid);
            if (parent >= 0 && supervisor->belongs[parent]) {
                supervisor->belongs[i] = 1;
                changed = 1;
            }
        }
    } while (changed);
    for (size_t i = 0; i < supervisor->snapshot_count; ++i)
        if (supervisor->belongs[i] && add_member(supervisor, &supervisor->snapshot[i]) != 0)
            return -1;
    for (size_t i = 0; i < supervisor->member_count; ++i) supervisor->members[i].alive = 0;
    for (size_t i = 0; i < supervisor->snapshot_count; ++i) {
        if (!supervisor->belongs[i]) continue;
        int member = member_index(supervisor, supervisor->snapshot[i].pid, supervisor->snapshot[i].start);
        if (member >= 0) supervisor->members[member].alive = 1;
    }
    return supervisor->identity_error ? -1 : 0;
}

static int capture_baseline_children(Supervisor *supervisor) {
    if (scan_all_procs(supervisor) != 0) return -1;
    for (size_t i = 0; i < supervisor->snapshot_count; ++i) {
        Proc *proc = &supervisor->snapshot[i];
        if (proc->ppid != supervisor->self_pid) continue;
        if (supervisor->baseline_count == MAX_BASELINE_CHILDREN) { errno = E2BIG; return -1; }
        size_t n = supervisor->baseline_count++;
        supervisor->baseline_pid[n] = proc->pid;
        supervisor->baseline_start[n] = proc->start;
    }
    if (supervisor->baseline_count != 0) { errno = EBUSY; return -1; }
    return 0;
}

static void reap_children(Supervisor *supervisor, int *echild) {
    *echild = 0;
    for (;;) {
        int status = 0;
        pid_t pid = waitpid(-1, &status, WNOHANG);
        if (pid > 0) {
            if (pid == supervisor->root_pid && !supervisor->root_reaped) {
                supervisor->root_reaped = 1;
                supervisor->root_status = status;
            }
            continue;
        }
        if (pid == 0) return;
        if (errno == EINTR) continue;
        if (errno == ECHILD) *echild = 1;
        return;
    }
}

static int signal_member(Member *member, int sig) {
    if (!member->alive) return 0;
#ifdef EVIDENCE_TEST_HOOKS
    static int injected_pidfd_failure;
    if (!injected_pidfd_failure && getenv("SIMPLE_STAGE3_RSS_TEST_FAIL_PIDFD_SIGNAL_ONCE")) {
        injected_pidfd_failure = 1;
        errno = EIO;
        return -1;
    }
#endif
    Proc current;
    if (proc_stat(member->pid, &current) != 0) {
        if (errno == ENOENT || errno == ESRCH) { member->alive = 0; return 0; }
        return -1;
    }
    if (current.start != member->start) {
        member->alive = 0;
        errno = ESTALE;
        return -1;
    }
    if (syscall(SYS_pidfd_send_signal, member->pidfd, sig, NULL, 0) != 0) {
        if (errno == ESRCH) { member->alive = 0; return 0; }
        return -1;
    }
    return 0;
}

/* Cleanup is an authority boundary, not an evidence collection boundary.
 * Sampling may deliberately reject a tree which exceeds MAX_PROCS or the
 * persistent member ledger, but that cap must never decide which owned
 * processes are terminated.  Build a fresh, dynamically-sized /proc view for
 * every cleanup sweep and derive ownership from the identity ledger, the
 * measured root, newly adopted children, and transitive parentage. */
static int cleanup_scan_all(Proc **snapshot_out, unsigned char **belongs_out,
                            size_t *count_out) {
    DIR *dir = opendir("/proc");
    if (!dir) return -1;
    Proc *snapshot = NULL;
    size_t count = 0, capacity = 0;
    int failed = 0;
    struct dirent *entry;
    errno = 0;
    while ((entry = readdir(dir)) != NULL) {
        char *end = NULL;
        errno = 0;
        long value = strtol(entry->d_name, &end, 10);
        if (errno || !*entry->d_name || *end || value <= 0 || value > INT_MAX)
            continue;
        Proc proc;
        if (proc_stat((pid_t)value, &proc) != 0) continue;
        if (count == capacity) {
            size_t next = capacity ? capacity * 2 : 1024;
            if (next < capacity || next > SIZE_MAX / sizeof(*snapshot)) {
                errno = EOVERFLOW; failed = 1; break;
            }
            Proc *grown = realloc(snapshot, next * sizeof(*snapshot));
            if (!grown) { failed = 1; break; }
            snapshot = grown;
            capacity = next;
        }
        snapshot[count++] = proc;
    }
    if (entry == NULL && errno != 0) failed = 1;
    if (closedir(dir) != 0) failed = 1;
    unsigned char *belongs = failed ? NULL : calloc(count ? count : 1, 1);
    if (!belongs) failed = 1;
    if (failed) { free(snapshot); free(belongs); return -1; }
    *snapshot_out = snapshot;
    *belongs_out = belongs;
    *count_out = count;
    return 0;
}

static int cleanup_snapshot_index_pid(const Proc *snapshot, size_t count,
                                      pid_t pid) {
    for (size_t i = 0; i < count; ++i)
        if (snapshot[i].pid == pid) return (int)i;
    return -1;
}

static int cleanup_sweep(Supervisor *supervisor, int sig, size_t *live_out) {
    Proc *snapshot = NULL;
    unsigned char *belongs = NULL;
    size_t count = 0;
#ifdef EVIDENCE_TEST_HOOKS
    static int injected_cleanup_discovery_failure;
    if (!injected_cleanup_discovery_failure &&
        getenv("SIMPLE_STAGE3_RSS_TEST_FAIL_CLEANUP_DISCOVERY_ONCE")) {
        injected_cleanup_discovery_failure = 1;
        errno = EIO;
        return -1;
    }
#endif
    if (cleanup_scan_all(&snapshot, &belongs, &count) != 0) return -1;
    for (size_t i = 0; i < count; ++i) {
        Proc *proc = &snapshot[i];
        if ((proc->pid == supervisor->root_pid && proc->start == supervisor->root_start) ||
            member_index(supervisor, proc->pid, proc->start) >= 0 ||
            (proc->ppid == supervisor->self_pid && proc->pid != supervisor->self_pid &&
             !baseline_contains(supervisor, proc->pid, proc->start)))
            belongs[i] = 1;
        if (member_pid_seen_different(supervisor, proc->pid, proc->start)) {
            free(snapshot); free(belongs); errno = ESTALE; return -1;
        }
    }
    int changed;
    do {
        changed = 0;
        for (size_t i = 0; i < count; ++i) {
            if (belongs[i]) continue;
            int parent = cleanup_snapshot_index_pid(snapshot, count, snapshot[i].ppid);
            if (parent >= 0 && belongs[parent]) { belongs[i] = 1; changed = 1; }
        }
    } while (changed);
    size_t live = 0;
    int failed = 0;
    for (size_t i = 0; i < count; ++i) {
        if (!belongs[i]) continue;
        ++live;
        int pidfd = pidfd_open_checked(snapshot[i].pid, snapshot[i].start);
        if (pidfd < 0) {
            if (errno != ESRCH && errno != ENOENT && errno != ESTALE) failed = 1;
            continue;
        }
#ifdef EVIDENCE_TEST_HOOKS
        static int injected_pidfd_failure;
        if (!injected_pidfd_failure &&
            getenv("SIMPLE_STAGE3_RSS_TEST_FAIL_PIDFD_SIGNAL_ONCE")) {
            injected_pidfd_failure = 1;
            errno = EIO;
            failed = 1;
        } else
#endif
        if (syscall(SYS_pidfd_send_signal, pidfd, sig, NULL, 0) != 0 && errno != ESRCH)
            failed = 1;
        if (close(pidfd) != 0) failed = 1;
    }
    free(snapshot);
    free(belongs);
    *live_out = live;
    return failed ? -1 : 0;
}

static int cleanup_tree(Supervisor *supervisor, const RunConfig *config,
                        size_t *survivors, int *survivors_known,
                        int *closure_proven, int *cleanup_stage) {
    int failed = 0, discovery_failed = 0, echild = 0, stable_zero = 0;
    *survivors = 0;
    *survivors_known = 0;
    *closure_proven = 0;
    *cleanup_stage = 0;
    supervisor->cleanup_started = 1;
    uint64_t term_deadline = deadline_after_ms(mono_ns(), config->term_grace_ms);
    size_t live = 0;
    if (cleanup_sweep(supervisor, SIGTERM, &live) != 0)
        failed = discovery_failed = 1;
    while (mono_ns() < term_deadline) {
        reap_children(supervisor, &echild);
        if (cleanup_sweep(supervisor, SIGTERM, &live) != 0)
            failed = discovery_failed = 1;
        if (!live && echild) {
            if (++stable_zero >= 3) {
                *survivors = 0;
                *survivors_known = !discovery_failed;
                *closure_proven = !failed && !discovery_failed;
                *cleanup_stage = 1;
                return *closure_proven ? 0 : -1;
            }
        } else stable_zero = 0;
        sleep_ms(10);
    }
    uint64_t kill_deadline = deadline_after_ms(mono_ns(), config->kill_grace_ms);
    stable_zero = 0;
    if (cleanup_sweep(supervisor, SIGKILL, &live) != 0)
        failed = discovery_failed = 1;
    while (mono_ns() < kill_deadline) {
        reap_children(supervisor, &echild);
        if (cleanup_sweep(supervisor, SIGKILL, &live) != 0)
            failed = discovery_failed = 1;
        if (!live && echild) {
            if (++stable_zero >= 3) {
                *survivors = 0;
                *survivors_known = !discovery_failed;
                *closure_proven = !failed && !discovery_failed;
                *cleanup_stage = 2;
                return *closure_proven ? 0 : -1;
            }
        } else stable_zero = 0;
        sleep_ms(10);
    }
    reap_children(supervisor, &echild);
    if (cleanup_sweep(supervisor, SIGKILL, &live) != 0) discovery_failed = 1;
    if (!discovery_failed) {
        *survivors = live;
        *survivors_known = 1;
    }
    return -1;
}

static void close_members(Supervisor *supervisor) {
    for (size_t i = 0; i < supervisor->member_count; ++i)
        if (supervisor->members[i].pidfd >= 0) close(supervisor->members[i].pidfd);
}

typedef struct {
    FileIdentity sampler, command, script;
    const char *run_id;
    char *command_argv_hex;
    char environment_sha256[65];
    uint64_t raw_dev, raw_ino;
} EvidenceIdentity;

static const char *const environment_keys[27] = {
    "HOME", "TMPDIR", "PATH", "LC_ALL", "LANG", "RUST_LOG", "LIBRARY_PATH",
    "SIMPLE_BOOTSTRAP_LINK_COMPAT_SHA256", "SIMPLE_BOOTSTRAP",
    "SIMPLE_NO_DEPRECATED_WARNINGS", "SIMPLE_STAGE3_STREAMING_SURFACES",
    "MALLOC_ARENA_MAX", "MALLOC_TRIM_THRESHOLD_", "SIMPLE_NATIVE_ARENA_DECLS",
    "SIMPLE_NO_STUB_FALLBACK", "SIMPLE_BUILD_PROGRESS_EVENTS",
    "SIMPLE_COMPILER_PHASE_PROFILE", "SIMPLE_COMPILER_PHASE_PROFILE_FILE",
    "SIMPLE_MEM_SNAPSHOT_FILE", "SIMPLE_EVIDENCE_RUN_ID",
    "LLVM_DISABLE_ABI_BREAKING_CHECKS_ENFORCING", "SIMPLE_NATIVE_BUILD_TARGET",
    "SIMPLE_NATIVE_BUILD_THREADS", "SIMPLE_NATIVE_BUILD_CACHE_DIR",
    "SIMPLE_RUNTIME_PATH", "SIMPLE_NATIVE_RUNTIME_BUNDLE", "SIMPLE_BINARY",
};

static void sha256_u64be(Sha256 *sha, uint64_t value) {
    unsigned char framing[8];
    for (unsigned byte = 0; byte < 8; ++byte)
        framing[7-byte] = (unsigned char)(value >> (byte * 8));
    sha256_update(sha, framing, sizeof(framing));
}

static void sha256_hex_finish(Sha256 *sha, char hex[65]) {
    unsigned char digest[32];
    sha256_final(sha, digest);
    for (int i = 0; i < 32; ++i) snprintf(hex + 2*i, 3, "%02x", digest[i]);
    hex[64] = 0;
}

static int absolute_path_list(const char *value) {
    if (!value || value[0] != '/') return 0;
    const char *part = value;
    for (;;) {
        const char *colon = strchr(part, ':');
        size_t length = colon ? (size_t)(colon - part) : strlen(part);
        if (!length || part[0] != '/' || (length == 1 && part[0] == '/')) return 0;
        if (!colon) return 1;
        part = colon + 1;
    }
}

static int environment_sha256(char hex[65]) {
    size_t count = 0;
    while (environ[count]) if (++count > 128) return -1;
    const char *path = getenv("PATH");
    const char *home = getenv("HOME");
    const char *tmpdir = getenv("TMPDIR");
    const char *lc_all = getenv("LC_ALL");
    const char *lang = getenv("LANG");
    if (!absolute_path_list(path) || !home || home[0] != '/' || !tmpdir || tmpdir[0] != '/' ||
        !lc_all || strcmp(lc_all, "C") || !lang || strcmp(lang, "C")) return -1;
    Sha256 sha;
    sha256_init(&sha);
    for (size_t i = 0; i < 27; ++i) {
        const char *value = getenv(environment_keys[i]);
        if (!value || (!*value && i != 6) || strlen(value) > 65536) return -1;
        sha256_u64be(&sha, strlen(environment_keys[i]));
        sha256_update(&sha, environment_keys[i], strlen(environment_keys[i]));
        sha256_u64be(&sha, strlen(value));
        sha256_update(&sha, value, strlen(value));
    }
    /* Reject alternate names and duplicates, independent of environ order. */
    unsigned char seen[27] = {0};
    size_t admitted = 0;
    for (size_t i = 0; i < count; ++i) {
        const char *equals = strchr(environ[i], '=');
        if (!equals || equals == environ[i]) return -1;
        size_t name_length = (size_t)(equals - environ[i]);
        size_t matches = 0, matched = 0;
        for (size_t k = 0; k < 27; ++k) {
            if (strlen(environment_keys[k]) == name_length &&
                !memcmp(environment_keys[k], environ[i], name_length)) {
                matches++;
                matched = k;
            }
        }
#ifdef EVIDENCE_TEST_HOOKS
        if (!matches && name_length > strlen("SIMPLE_STAGE3_RSS_TEST_") &&
            !memcmp(environ[i], "SIMPLE_STAGE3_RSS_TEST_",
                    strlen("SIMPLE_STAGE3_RSS_TEST_"))) continue;
#endif
        if (matches != 1 || seen[matched]) return -1;
        seen[matched] = 1;
        admitted++;
    }
    if (admitted != 27) return -1;
    sha256_hex_finish(&sha, hex);
    return 0;
}

static int write_open_record(RawWriter *writer, const Supervisor *supervisor,
                             const RunConfig *config, const EvidenceIdentity *identity) {
    return writer_record(writer, 1,
        "open schema=%s run_id=%s mono_ns=%" PRIu64
        " root_pid=%ld root_start=%" PRIu64 " outer_pgid=%ld"
        " raw_dev=%" PRIu64 " raw_ino=%" PRIu64 " environment_sha256=%s"
        " sampler_dev=%" PRIu64 " sampler_ino=%" PRIu64 " sampler_sha256=%s"
        " command_dev=%" PRIu64 " command_ino=%" PRIu64 " command_sha256=%s"
        " script_dev=%" PRIu64 " script_ino=%" PRIu64 " script_sha256=%s"
        " command_argv_hex=%s interval_ms=%" PRIu64 " max_gap_ms=%" PRIu64
        " max_rss_kb=%" PRIu64 " term_grace_ms=%" PRIu64 " kill_grace_ms=%" PRIu64
        " max_runtime_ms=%" PRIu64 " max_batches=%" PRIu64
        " max_records=%" PRIu64 " max_tracked=%u max_raw_bytes=%" PRIu64
        " sync_max_batches=%u sync_max_ms=%u closure_reserve_bytes=%u"
        " closure_reserve_records=%u\n",
        RAW_SCHEMA, identity->run_id, mono_ns(), (long)supervisor->root_pid,
        supervisor->root_start, (long)supervisor->outer_pgid,
        identity->raw_dev, identity->raw_ino, identity->environment_sha256,
        identity->sampler.dev, identity->sampler.ino, identity->sampler.sha256,
        identity->command.dev, identity->command.ino, identity->command.sha256,
        identity->script.dev, identity->script.ino,
        identity->script.ino ? identity->script.sha256 : "none",
        identity->command_argv_hex, config->interval_ms, config->max_gap_ms,
        config->max_rss_kb, config->term_grace_ms, config->kill_grace_ms,
        config->max_runtime_ms, config->max_batches, config->max_records, (unsigned)config->max_tracked,
        config->max_raw_bytes, SYNC_MAX_BATCHES, SYNC_MAX_MS,
        (unsigned)config->closure_reserve_bytes, (unsigned)config->closure_reserve_records);
}

typedef struct {
    uint64_t last_batch_ns, max_start_gap_ns, max_batch_duration_ns;
    uint64_t peak_tree_rss_kb;
    uint64_t sample_records, sample_batches, root_samples;
} SampleStats;

static int write_batch_close_record(RawWriter *writer, const Supervisor *supervisor,
                                    const EvidenceIdentity *identity, uint64_t batch_seq,
                                    uint64_t start_ns, uint64_t end_ns, uint64_t records,
                                    uint64_t tree_rss) {
    return writer_data_record_unsynced(writer,
        "batch-close schema=%s run_id=%s mono_ns=%" PRIu64
        " root_pid=%ld root_start=%" PRIu64
        " raw_dev=%" PRIu64 " raw_ino=%" PRIu64 " environment_sha256=%s"
        " command_dev=%" PRIu64 " command_ino=%" PRIu64 " command_sha256=%s"
        " script_dev=%" PRIu64 " script_ino=%" PRIu64 " script_sha256=%s"
        " batch_seq=%" PRIu64 " batch_start_ns=%" PRIu64 " batch_end_ns=%" PRIu64
        " batch_records=%" PRIu64 " tree_rss_kb=%" PRIu64 "\n",
        RAW_SCHEMA, identity->run_id, end_ns, (long)supervisor->root_pid,
        supervisor->root_start, identity->raw_dev, identity->raw_ino,
        identity->environment_sha256, identity->command.dev, identity->command.ino,
        identity->command.sha256, identity->script.dev, identity->script.ino,
        identity->script.ino ? identity->script.sha256 : "none", batch_seq,
        start_ns, end_ns, records, tree_rss);
}

static int format_sample_record(char **record, const Supervisor *supervisor,
                                const EvidenceIdentity *identity, const Proc *proc,
                                const char *argv_hex, uint64_t at_ns, uint64_t tree_rss,
                                uint64_t batch_seq) {
    int length = asprintf(record,
        "sample schema=%s run_id=%s mono_ns=%" PRIu64
        " root_pid=%ld root_start=%" PRIu64
        " raw_dev=%" PRIu64 " raw_ino=%" PRIu64 " environment_sha256=%s"
        " command_dev=%" PRIu64 " command_ino=%" PRIu64 " command_sha256=%s"
        " script_dev=%" PRIu64 " script_ino=%" PRIu64 " script_sha256=%s"
        " batch_seq=%" PRIu64 " pid=%ld start=%" PRIu64
        " ppid=%ld pgrp=%ld sid=%ld state=%c"
        " vmrss_kb=%" PRIu64 " vmhwm_kb=%" PRIu64 " rssanon_kb=%" PRIu64
        " rssfile_kb=%" PRIu64 " tree_rss_kb=%" PRIu64 " argv_hex=%s\n",
        RAW_SCHEMA, identity->run_id, at_ns, (long)supervisor->root_pid,
        supervisor->root_start, identity->raw_dev, identity->raw_ino,
        identity->environment_sha256, identity->command.dev, identity->command.ino,
        identity->command.sha256, identity->script.dev, identity->script.ino,
        identity->script.ino ? identity->script.sha256 : "none", batch_seq,
        (long)proc->pid, proc->start, (long)proc->ppid, (long)proc->pgrp,
        (long)proc->sid, proc->state, proc->rss, proc->hwm, proc->anon,
        proc->file, tree_rss, argv_hex);
    if (length <= 0 || !*record || (size_t)length > MAX_RECORD_BYTES || (*record)[length-1] != '\n') {
        free(*record);
        *record = NULL;
        errno = EINVAL;
        return -1;
    }
    return length;
}

static int sample_tree(Supervisor *supervisor, RawWriter *writer,
                       const RunConfig *config, const EvidenceIdentity *identity,
                       SampleStats *stats, const char **reason) {
    uint64_t ordinary_record_cap = config->max_records - config->closure_reserve_records;
    if (stats->sample_batches >= config->max_batches ||
        stats->sample_records >= ordinary_record_cap) {
        *reason = "sample-count-limit";
        return -1;
    }
#ifdef EVIDENCE_TEST_HOOKS
    static uint64_t attempts;
    const char *fail_after_text = getenv("SIMPLE_STAGE3_RSS_TEST_FAIL_SAMPLE_AFTER");
    uint64_t fail_after = 0;
    if (fail_after_text && parse_u64(fail_after_text, &fail_after) == 0 && attempts++ >= fail_after) {
        *reason = "sampler-failure"; errno = EIO; return -1;
    }
#endif
    uint64_t at_ns = mono_ns();
    if (!at_ns) { *reason = "clock-failure"; return -1; }
    uint64_t start_gap_ns = 0;
    if (stats->last_batch_ns) {
        start_gap_ns = at_ns - stats->last_batch_ns;
        if (start_gap_ns > config->max_gap_ms * UINT64_C(1000000)) {
            *reason = "sample-gap-limit"; return -1;
        }
    }
    if (discover_tree(supervisor) != 0) {
        *reason = supervisor->identity_error ? "pid-identity-reuse" : "sampler-failure";
        return -1;
    }
#ifdef EVIDENCE_TEST_HOOKS
    const char *scan_delay_text = getenv("SIMPLE_STAGE3_RSS_TEST_SCAN_DELAY_MS");
    uint64_t scan_delay_ms = 0;
    if (scan_delay_text && parse_u64(scan_delay_text, &scan_delay_ms) == 0)
        sleep_ms(scan_delay_ms);
#endif
    int root_index = snapshot_index_pid(supervisor, supervisor->root_pid);
    if (root_index < 0 || supervisor->snapshot[root_index].start != supervisor->root_start ||
        !supervisor->belongs[root_index] ||
        !proc_executable_matches(supervisor->root_pid, &identity->command)) {
        *reason = "root-loss";
        return -1;
    }
    Proc *batch = calloc(supervisor->snapshot_count, sizeof(*batch));
    char **argv_hex = calloc(supervisor->snapshot_count, sizeof(*argv_hex));
    if (!batch || !argv_hex) { free(batch); free(argv_hex); *reason = "sampler-failure"; return -1; }
    size_t count = 0;
    uint64_t tree_rss = 0;
    for (size_t i = 0; i < supervisor->snapshot_count; ++i) {
        if (!supervisor->belongs[i]) continue;
        Proc current;
        if (proc_stat(supervisor->snapshot[i].pid, &current) != 0) continue;
        if (current.start != supervisor->snapshot[i].start) {
            *reason = "pid-identity-reuse";
            goto failed;
        }
        if (proc_memory(&current) != 0) {
            if (current.state == 'Z') current.rss = current.hwm = current.anon = current.file = 0;
            else {
                Proc vanished;
                if (proc_stat(current.pid, &vanished) != 0 &&
                    (errno == ENOENT || errno == ESRCH)) {
                    if (current.pid == supervisor->root_pid) { *reason = "root-loss"; goto failed; }
                    continue;
                }
                *reason = "sampler-failure";
                goto failed;
            }
        }
        char *encoded = proc_argv_hex(current.pid);
        if (!encoded) {
            if (current.state == 'Z') encoded = strdup("00");
            if (!encoded) {
                Proc vanished;
                if (proc_stat(current.pid, &vanished) != 0 &&
                    (errno == ENOENT || errno == ESRCH)) {
                    if (current.pid == supervisor->root_pid) { *reason = "root-loss"; goto failed; }
                    continue;
                }
                *reason = "sampler-failure";
                goto failed;
            }
        }
        Proc final_identity;
        if (proc_stat(current.pid, &final_identity) != 0) {
            free(encoded);
            if (errno == ENOENT || errno == ESRCH) {
                if (current.pid == supervisor->root_pid) { *reason = "root-loss"; goto failed; }
                continue;
            }
            *reason = "sampler-failure";
            goto failed;
        }
        if (final_identity.start != current.start) {
            free(encoded);
            *reason = "pid-identity-reuse";
            goto failed;
        }
#ifdef EVIDENCE_TEST_HOOKS
        if (getenv("SIMPLE_STAGE3_RSS_TEST_FORCE_POSTREAD_START_MISMATCH")) {
            free(encoded);
            *reason = "pid-identity-reuse";
            goto failed;
        }
#endif
        current.ppid = final_identity.ppid;
        current.pgrp = final_identity.pgrp;
        current.sid = final_identity.sid;
        current.state = final_identity.state;
        if (UINT64_MAX - tree_rss < current.rss) { free(encoded); *reason = "rss-overflow"; goto failed; }
        tree_rss += current.rss;
        batch[count] = current;
        argv_hex[count++] = encoded;
    }
    if (!count) { *reason = "root-loss"; goto failed; }
#ifdef EVIDENCE_TEST_HOOKS
    if (getenv("SIMPLE_STAGE3_RSS_TEST_FORCE_RSS_EQUAL")) tree_rss = config->max_rss_kb;
#endif
    if (count > ordinary_record_cap - stats->sample_records) {
        *reason = "sample-count-limit";
        goto failed;
    }
    char **records = calloc(count, sizeof(*records));
    if (!records) { *reason = "sampler-failure"; goto failed; }
    size_t batch_bytes = 0;
    for (size_t i = 0; i < count; ++i) {
        int length = format_sample_record(&records[i], supervisor, identity, &batch[i], argv_hex[i],
                                          at_ns, tree_rss, stats->sample_batches);
        if (length < 0 || batch_bytes > SIZE_MAX - (size_t)length) {
            *reason = "raw-write-failure";
            for (size_t j = 0; j < count; ++j) free(records[j]);
            free(records);
            goto failed;
        }
        batch_bytes += (size_t)length;
    }
    char *batch_blob = malloc(batch_bytes);
    if (!batch_blob) {
        for (size_t i = 0; i < count; ++i) free(records[i]);
        free(records);
        *reason = "sampler-failure";
        goto failed;
    }
    size_t batch_offset = 0;
    for (size_t i = 0; i < count; ++i) {
        size_t length = strlen(records[i]);
        memcpy(batch_blob + batch_offset, records[i], length);
        batch_offset += length;
        free(records[i]);
    }
    free(records);
    if (writer_blob(writer, 0, batch_blob, batch_bytes, count) != 0) {
        free(batch_blob);
        *reason = "raw-write-failure";
        goto failed;
    }
    free(batch_blob);
    uint64_t batch_end_ns = mono_ns();
    if (!batch_end_ns || batch_end_ns < at_ns ||
        batch_end_ns - at_ns > config->max_gap_ms * UINT64_C(1000000)) {
        *reason = "batch-duration-limit";
        goto failed;
    }
    uint64_t batch_duration = batch_end_ns - at_ns;
    if (start_gap_ns > stats->max_start_gap_ns) stats->max_start_gap_ns = start_gap_ns;
    if (batch_duration > stats->max_batch_duration_ns)
        stats->max_batch_duration_ns = batch_duration;
    if (write_batch_close_record(writer, supervisor, identity, stats->sample_batches,
                                 at_ns, batch_end_ns, count, tree_rss) != 0) {
        *reason = "raw-write-failure";
        goto failed;
    }
    for (size_t i = 0; i < count; ++i) {
        stats->sample_records++;
        if (batch[i].pid == supervisor->root_pid && batch[i].start == supervisor->root_start)
            stats->root_samples++;
    }
    for (size_t i = 0; i < count; ++i) free(argv_hex[i]);
    free(argv_hex); free(batch);
    stats->last_batch_ns = at_ns;
    stats->sample_batches++;
    if (tree_rss > stats->peak_tree_rss_kb) stats->peak_tree_rss_kb = tree_rss;
    if (tree_rss >= config->max_rss_kb) { *reason = "rss-limit"; return -1; }
    return 0;
failed:
    for (size_t i = 0; i < count; ++i) free(argv_hex[i]);
    free(argv_hex); free(batch);
    return -1;
}

static int write_failure_record(RawWriter *writer, const Supervisor *supervisor,
                                const EvidenceIdentity *identity, const SampleStats *stats,
                                const char *reason, int exit_code, int signal_number,
                                size_t survivors, int survivors_known,
                                int closure_proven) {
    char survivor_text[32];
    if (survivors_known) snprintf(survivor_text, sizeof(survivor_text), "%zu", survivors);
    else strcpy(survivor_text, "unknown");
    return writer_record(writer, 1,
        "failure schema=%s run_id=%s mono_ns=%" PRIu64
        " root_pid=%ld root_start=%" PRIu64
        " raw_dev=%" PRIu64 " raw_ino=%" PRIu64 " environment_sha256=%s"
        " command_dev=%" PRIu64 " command_ino=%" PRIu64 " command_sha256=%s"
        " script_dev=%" PRIu64 " script_ino=%" PRIu64 " script_sha256=%s"
        " reason=%s exit_code=%d signal=%d sample_records=%" PRIu64
        " sample_batches=%" PRIu64 " survivors=%s closure_proven=%d zero_survivors=%d\n",
        RAW_SCHEMA, identity->run_id, mono_ns(), (long)supervisor->root_pid,
        supervisor->root_start, identity->raw_dev, identity->raw_ino,
        identity->environment_sha256, identity->command.dev, identity->command.ino,
        identity->command.sha256, identity->script.dev, identity->script.ino,
        identity->script.ino ? identity->script.sha256 : "none", reason,
        exit_code, signal_number, stats->sample_records, stats->sample_batches,
        survivor_text, closure_proven, closure_proven && survivors_known && survivors == 0);
}

static int write_terminal_record(RawWriter *writer, const Supervisor *supervisor,
                                 const RunConfig *config, const EvidenceIdentity *identity,
                                 const SampleStats *stats, int cleanup_stage) {
    return writer_record(writer, 1,
        "terminal schema=%s run_id=%s mono_ns=%" PRIu64
        " root_pid=%ld root_start=%" PRIu64
        " raw_dev=%" PRIu64 " raw_ino=%" PRIu64 " environment_sha256=%s"
        " command_dev=%" PRIu64 " command_ino=%" PRIu64 " command_sha256=%s"
        " script_dev=%" PRIu64 " script_ino=%" PRIu64 " script_sha256=%s"
        " exit_code=0 signal=0 interval_ms=%" PRIu64 " max_gap_ms=%" PRIu64
        " observed_max_start_gap_ns=%" PRIu64
        " observed_max_batch_duration_ns=%" PRIu64
        " max_observed_gap_ms=%" PRIu64 " max_rss_kb=%" PRIu64
        " peak_tree_rss_kb=%" PRIu64 " sample_records=%" PRIu64
        " sample_batches=%" PRIu64
        " survivors=0 closure_proven=1 zero_survivors=1 cleanup=%s\n",
        RAW_SCHEMA, identity->run_id, mono_ns(), (long)supervisor->root_pid,
        supervisor->root_start, identity->raw_dev, identity->raw_ino,
        identity->environment_sha256, identity->command.dev, identity->command.ino,
        identity->command.sha256, identity->script.dev, identity->script.ino,
        identity->script.ino ? identity->script.sha256 : "none",
        config->interval_ms, config->max_gap_ms, stats->max_start_gap_ns,
        stats->max_batch_duration_ns,
        ((stats->max_start_gap_ns > stats->max_batch_duration_ns
              ? stats->max_start_gap_ns : stats->max_batch_duration_ns) + UINT64_C(999999)) /
            UINT64_C(1000000),
        config->max_rss_kb, stats->peak_tree_rss_kb, stats->sample_records,
        stats->sample_batches,
        cleanup_stage == 1 ? "term-reaped" : "kill-reaped");
}

static int run_supervised(int argc, char **argv) {
    const char *raw_path = NULL, *expected_command = NULL, *expected_self = NULL, *run_id = NULL;
    const char *script_path = NULL, *expected_script = NULL;
    RunConfig config = {
        DEFAULT_INTERVAL_MS, DEFAULT_MAX_GAP_MS, DEFAULT_MAX_RSS_KB,
        DEFAULT_TERM_GRACE_MS, DEFAULT_KILL_GRACE_MS, DEFAULT_MAX_RUNTIME_MS,
        DEFAULT_MAX_BATCHES, DEFAULT_MAX_RECORDS, DEFAULT_MAX_RAW_BYTES,
        MAX_TRACKED, CLOSURE_RESERVE_BYTES, CLOSURE_RESERVE_RECORDS,
    };
    int command_at = -1;
#ifdef EVIDENCE_TEST_HOOKS
    int test_signal_observer_fd = -1;
    control_signal_observation_fd = -1;
    control_signal_delivery_count = 0;
#endif
    for (int i = 2; i < argc; ++i) {
#define OPT_VALUE(name, target) if (!strcmp(argv[i], name) && i + 1 < argc) { target = argv[++i]; }
        OPT_VALUE("--raw", raw_path)
        else OPT_VALUE("--sha256", expected_command)
        else OPT_VALUE("--self-sha256", expected_self)
        else OPT_VALUE("--run-id", run_id)
        else OPT_VALUE("--script", script_path)
        else OPT_VALUE("--script-sha256", expected_script)
        else if (!strcmp(argv[i], "--interval-ms") && i + 1 < argc) {
            if (parse_u64(argv[++i], &config.interval_ms)) return 64;
        } else if (!strcmp(argv[i], "--max-gap-ms") && i + 1 < argc) {
            if (parse_u64(argv[++i], &config.max_gap_ms)) return 64;
        } else if (!strcmp(argv[i], "--max-rss-kb") && i + 1 < argc) {
            if (parse_u64(argv[++i], &config.max_rss_kb)) return 64;
        } else if (!strcmp(argv[i], "--term-grace-ms") && i + 1 < argc) {
            if (parse_u64(argv[++i], &config.term_grace_ms)) return 64;
        } else if (!strcmp(argv[i], "--kill-grace-ms") && i + 1 < argc) {
            if (parse_u64(argv[++i], &config.kill_grace_ms)) return 64;
        } else if (!strcmp(argv[i], "--max-runtime-ms") && i + 1 < argc) {
            if (parse_u64(argv[++i], &config.max_runtime_ms)) return 64;
        } else if (!strcmp(argv[i], "--max-records") && i + 1 < argc) {
            if (parse_u64(argv[++i], &config.max_records)) return 64;
        } else if (!strcmp(argv[i], "--max-batches") && i + 1 < argc) {
            if (parse_u64(argv[++i], &config.max_batches)) return 64;
        } else if (!strcmp(argv[i], "--max-raw-bytes") && i + 1 < argc) {
            if (parse_u64(argv[++i], &config.max_raw_bytes)) return 64;
        } else if (!strcmp(argv[i], "--max-tracked-per-batch") && i + 1 < argc) {
            if (parse_u64(argv[++i], &config.max_tracked)) return 64;
        } else if (!strcmp(argv[i], "--closure-reserve-bytes") && i + 1 < argc) {
            if (parse_u64(argv[++i], &config.closure_reserve_bytes)) return 64;
        } else if (!strcmp(argv[i], "--closure-reserve-records") && i + 1 < argc) {
            if (parse_u64(argv[++i], &config.closure_reserve_records)) return 64;
        } else if (!strcmp(argv[i], "--")) { command_at = i + 1; break; }
        else return 64;
#undef OPT_VALUE
    }
    if (!raw_path || !valid_sha256(expected_command) || !valid_sha256(expected_self) ||
        !safe_run_id(run_id) ||
        command_at < 0 || command_at >= argc ||
        config.interval_ms != DEFAULT_INTERVAL_MS || config.max_gap_ms != DEFAULT_MAX_GAP_MS ||
        config.max_rss_kb != DEFAULT_MAX_RSS_KB ||
        config.term_grace_ms != DEFAULT_TERM_GRACE_MS ||
        config.kill_grace_ms != DEFAULT_KILL_GRACE_MS ||
        config.max_runtime_ms != DEFAULT_MAX_RUNTIME_MS ||
        config.max_batches != DEFAULT_MAX_BATCHES ||
        config.max_records != DEFAULT_MAX_RECORDS ||
        config.max_raw_bytes != DEFAULT_MAX_RAW_BYTES || config.max_tracked != MAX_TRACKED ||
        config.closure_reserve_bytes != CLOSURE_RESERVE_BYTES ||
        config.closure_reserve_records != CLOSURE_RESERVE_RECORDS ||
        config.max_gap_ms < config.interval_ms ||
        config.max_gap_ms > UINT64_MAX / UINT64_C(1000000) ||
        config.interval_ms > UINT64_MAX / UINT64_C(1000000))
        return 64;
    if ((script_path != NULL) != (expected_script != NULL) ||
        (expected_script && !valid_sha256(expected_script))) return 64;
    if (script_path && (!argv[command_at + 1] || strcmp(argv[command_at + 1], script_path))) return 64;

    FileIdentity command_identity, script_identity = {0}, sampler_identity;
    int command_fd = open_identity_nofollow(argv[command_at], &command_identity);
    if (command_fd < 0) { perror("open measured executable"); return 2; }
    if (strcmp(command_identity.sha256, expected_command)) {
        fprintf(stderr, "measured executable hash mismatch\n"); close(command_fd); return 2;
    }
    int script_fd = -1;
    if (script_path) {
        FileIdentity source_script_identity;
        int source_script_fd = open_identity_nofollow(script_path, &source_script_identity);
        if (source_script_fd < 0 || strcmp(source_script_identity.sha256, expected_script)) {
            fprintf(stderr, "measured script identity mismatch\n");
            if (source_script_fd >= 0) close(source_script_fd);
            close(command_fd); return 2;
        }
        script_fd = sealed_snapshot_fd(source_script_fd, &source_script_identity, &script_identity);
        close(source_script_fd);
        if (script_fd < 0) {
            fprintf(stderr, "could not seal measured script snapshot\n");
            close(command_fd);
            return 2;
        }
    }
    if (self_identity(&sampler_identity) != 0 || strcmp(sampler_identity.sha256, expected_self)) {
        perror("sampler identity"); if (script_fd >= 0) close(script_fd); close(command_fd); return 2;
    }
    char **exec_argv = &argv[command_at];
    char **bound_script_argv = NULL;
    if (script_fd >= 0) {
        size_t original_count = 0;
        while (argv[command_at + original_count]) ++original_count;
        bound_script_argv = calloc(original_count + 3, sizeof(*bound_script_argv));
        if (!bound_script_argv) {
            close(script_fd);
            close(command_fd);
            return 2;
        }
        bound_script_argv[0] = argv[command_at];
        bound_script_argv[1] = "-c";
        bound_script_argv[2] = ". /proc/self/fd/198";
        bound_script_argv[3] = (char *)script_path;
        for (size_t i = 2; i < original_count; ++i)
            bound_script_argv[i + 2] = argv[command_at + i];
        exec_argv = bound_script_argv;
    }
    char *command_argv_hex = encode_argv(exec_argv);
    if (!command_argv_hex) {
        fprintf(stderr, "command argv exceeds cap\n");
        free(bound_script_argv);
        if (script_fd >= 0) close(script_fd);
        close(command_fd);
        return 2;
    }
    RawTarget raw_target;
    if (open_absent_append(raw_path, &raw_target) != 0) {
        perror("raw evidence target"); free(command_argv_hex); free(bound_script_argv);
        if (script_fd >= 0) close(script_fd);
        close(command_fd);
        return 2;
    }
    RawWriter writer = {
        .fd=raw_target.fd,
        .max_bytes=config.max_raw_bytes,
        .max_records=config.max_records,
    };
#ifdef EVIDENCE_TEST_HOOKS
    const char *fail_write = getenv("SIMPLE_STAGE3_RSS_TEST_FAIL_WRITE_AFTER");
    if (fail_write) (void)parse_u64(fail_write, &writer.fail_write_after);
    const char *fail_sync = getenv("SIMPLE_STAGE3_RSS_TEST_FAIL_SYNC_AFTER");
    if (fail_sync) (void)parse_u64(fail_sync, &writer.fail_sync_after);
    const char *short_write = getenv("SIMPLE_STAGE3_RSS_TEST_SHORT_WRITE_AFTER");
    if (short_write) (void)parse_u64(short_write, &writer.short_write_after);
#endif
    Supervisor supervisor;
    memset(&supervisor, 0, sizeof(supervisor));
    supervisor.self_pid = getpid();
    supervisor.outer_pgid = getpgrp();
    supervisor.snapshot = calloc(MAX_PROCS, sizeof(*supervisor.snapshot));
    supervisor.belongs = calloc(MAX_PROCS, 1);
    if (!supervisor.snapshot || !supervisor.belongs ||
        prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) != 0 ||
        capture_baseline_children(&supervisor) != 0) {
        perror("supervisor setup");
        free(supervisor.snapshot); free(supervisor.belongs);
        (void)unlinkat(raw_target.parent_fd, raw_target.leaf, 0);
        (void)fsync(raw_target.parent_fd);
        close_raw_target(&raw_target); free(command_argv_hex); free(bound_script_argv);
        if (script_fd >= 0) close(script_fd);
        close(command_fd);
        return 2;
    }

#ifdef EVIDENCE_TEST_HOOKS
    const char *signal_observation_path =
        getenv("SIMPLE_STAGE3_RSS_TEST_SIGNAL_OBSERVATION_PATH");
    if (signal_observation_path) {
        struct stat observation_stat;
        if (signal_observation_path[0] != '/' ||
            (test_signal_observer_fd = open(signal_observation_path,
                O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC | O_APPEND, 0600)) < 0 ||
            fstat(test_signal_observer_fd, &observation_stat) != 0 ||
            !S_ISREG(observation_stat.st_mode)) {
            perror("signal observation target");
            goto pre_fork_fail;
        }
        control_signal_observation_fd = test_signal_observer_fd;
    }
#endif

    sigset_t controls, oldmask, runmask;
    sigemptyset(&controls);
    sigaddset(&controls, SIGHUP); sigaddset(&controls, SIGINT);
    sigaddset(&controls, SIGTERM); sigaddset(&controls, SIGQUIT);
    if (sigprocmask(SIG_BLOCK, &controls, &oldmask) != 0) {
        perror("block control signals"); goto pre_fork_fail;
    }
    runmask = oldmask;
    sigdelset(&runmask, SIGHUP); sigdelset(&runmask, SIGINT);
    sigdelset(&runmask, SIGTERM); sigdelset(&runmask, SIGQUIT);
    struct sigaction action;
    memset(&action, 0, sizeof(action));
    action.sa_handler = on_control_signal;
    action.sa_mask = controls;
    if (sigaction(SIGHUP, &action, NULL) || sigaction(SIGINT, &action, NULL) ||
        sigaction(SIGTERM, &action, NULL) || sigaction(SIGQUIT, &action, NULL)) {
        perror("install signal handlers"); sigprocmask(SIG_SETMASK, &oldmask, NULL); goto pre_fork_fail;
    }
    struct sigaction child_default;
    memset(&child_default, 0, sizeof(child_default));
    child_default.sa_handler = SIG_DFL;
    sigemptyset(&child_default.sa_mask);
    if (sigaction(SIGCHLD, &child_default, NULL) || signal(SIGPIPE, SIG_IGN) == SIG_ERR) {
        perror("signal setup"); sigprocmask(SIG_SETMASK, &oldmask, NULL); goto pre_fork_fail;
    }
    int gate[2];
    if (pipe2(gate, O_CLOEXEC) != 0) {
        perror("launch gate"); sigprocmask(SIG_SETMASK, &oldmask, NULL); goto pre_fork_fail;
    }
    pid_t child = fork();
    if (child < 0) {
        perror("fork"); close(gate[0]); close(gate[1]);
        sigprocmask(SIG_SETMASK, &oldmask, NULL); goto pre_fork_fail;
    }
    if (child == 0) {
#ifdef EVIDENCE_TEST_HOOKS
        if (test_signal_observer_fd >= 0) close(test_signal_observer_fd);
        control_signal_observation_fd = -1;
#endif
        if (prctl(PR_SET_PDEATHSIG, SIGKILL, 0, 0, 0) != 0 ||
            getppid() != supervisor.self_pid) _exit(126);
        close(gate[1]);
        for (int sig = 1; sig < NSIG; ++sig) {
            if (sig == SIGKILL || sig == SIGSTOP) continue;
            (void)sigaction(sig, &child_default, NULL);
        }
        if (setpgid(0, 0) != 0) _exit(126);
        char byte;
        ssize_t got;
        do { got = read(gate[0], &byte, 1); } while (got < 0 && errno == EINTR);
        close(gate[0]);
        if (got != 1) _exit(126);
        if (sigprocmask(SIG_SETMASK, &runmask, NULL) != 0) _exit(126);
#ifdef EVIDENCE_TEST_HOOKS
        if (child_post_gate_barrier() != 0) _exit(126);
        const char *pre_exec_delay = getenv("SIMPLE_STAGE3_RSS_TEST_PRE_EXEC_DELAY_MS");
        uint64_t pre_exec_delay_ms = 0;
        if (pre_exec_delay && parse_u64(pre_exec_delay, &pre_exec_delay_ms) == 0)
            (void)sleep_ms(pre_exec_delay_ms);
#endif
        if (script_fd >= 0) {
            int bound_fd = 198;
            if (dup2(script_fd, bound_fd) < 0 || fcntl(bound_fd, F_SETFD, 0) != 0) _exit(126);
        }
        if (ptrace(PTRACE_TRACEME, 0, NULL, NULL) != 0) _exit(126);
        fexecve(command_fd, exec_argv, environ);
        _exit(127);
    }

    close(gate[0]);
    supervisor.root_pid = child;
    if (setpgid(child, child) != 0 && errno != EACCES) {
        perror("root process group"); close(gate[1]);
    }
    Proc root;
    memset(&root, 0, sizeof(root));
    for (int i = 0; i < 100 && proc_stat(child, &root) != 0; ++i) sleep_ms(1);
    const char *reason = NULL;
    int command_exit = 255, command_signal = 0;
    size_t survivors = 0;
    int survivors_known = 0, closure_proven = 0, cleanup_stage = 0;
    SampleStats stats = {0};
    EvidenceIdentity evidence = {
        .sampler=sampler_identity,
        .command=command_identity,
        .script=script_identity,
        .run_id=run_id,
        .command_argv_hex=command_argv_hex,
        .raw_dev=raw_target.dev,
        .raw_ino=raw_target.ino,
    };
    const char *environment_run_id = getenv("SIMPLE_EVIDENCE_RUN_ID");
    if (!environment_run_id || strcmp(environment_run_id, run_id) ||
        environment_sha256(evidence.environment_sha256) != 0)
        reason = "environment-identity-failure";
    if (!root.start) reason = "root-identity-failure";
    else {
        supervisor.root_start = root.start;
        if (add_member(&supervisor, &root) != 0) reason = "root-identity-failure";
    }
    int root_member = root.start ? member_index(&supervisor, child, root.start) : -1;
    if (!reason && root_member < 0) reason = "root-identity-failure";
    if (!reason && write_open_record(&writer, &supervisor, &config, &evidence) != 0)
        reason = "raw-write-failure";
#ifdef EVIDENCE_TEST_HOOKS
    const char *pre_gate_delay = getenv("SIMPLE_STAGE3_RSS_TEST_PRE_GATE_DELAY_MS");
    const char *pre_gate_ready = getenv("SIMPLE_STAGE3_RSS_TEST_PRE_GATE_READY_PATH");
    uint64_t pre_gate_delay_ms = 0;
    if (!reason && pre_gate_delay && parse_u64(pre_gate_delay, &pre_gate_delay_ms) == 0) {
        if (publish_pre_gate_ready(pre_gate_ready, &controls, supervisor.self_pid) != 0)
            reason = "pre-gate-ready-failure";
        else
            sleep_ms(pre_gate_delay_ms);
    }
#endif
    uint64_t started_ns = mono_ns();
    int exec_trace_stop = 0;
    if (!reason && !started_ns) reason = "clock-failure";
    if (!reason) {
        pre_exec_pidfd = supervisor.members[root_member].pidfd;
        launch_gate_write_fd = gate[1];
        /* Deliver every already-pending control before attempting the gate
         * write.  A control delivered in the remaining window closes this fd,
         * so it cannot be ordered before a successful one-byte release. */
        if (sigprocmask(SIG_SETMASK, &runmask, NULL) != 0)
            reason = "signal-mask-failure";
    }
#ifdef EVIDENCE_TEST_HOOKS
    if (!reason) {
        const char *expected_text =
            getenv("SIMPLE_STAGE3_RSS_TEST_EXPECT_SIGNAL_DELIVERIES");
        uint64_t expected_deliveries = 0;
        if (expected_text &&
            (parse_u64(expected_text, &expected_deliveries) != 0 ||
             expected_deliveries == 0 || expected_deliveries > 32 ||
             test_signal_observer_fd < 0 ||
             wait_for_test_signal_deliveries(expected_deliveries) != 0))
            reason = interrupted_signal ? "interrupted" : "signal-observation-failure";
    }
#endif
    if (!reason && interrupted_signal) reason = "interrupted";
    if (!reason) {
        char byte = 'x';
        ssize_t sent;
        int release_fd = (int)launch_gate_write_fd;
        do { sent = release_fd < 0 ? -1 : write(release_fd, &byte, 1); }
        while (sent < 0 && errno == EINTR && !interrupted_signal);
        if (sent != 1)
            reason = interrupted_signal ? "interrupted" : "launch-gate-failure";
    }
    launch_gate_write_fd = -1;
    if (close(gate[1]) != 0 && errno != EBADF && !reason)
        reason = "launch-gate-close-failure";
    gate[1] = -1;
    if (!reason) {
        int trace_status = 0;
        pid_t waited = 0;
        uint64_t exec_wait_ms = config.max_gap_ms;
#ifdef EVIDENCE_TEST_HOOKS
        if (getenv("SIMPLE_STAGE3_RSS_TEST_CHILD_POST_GATE_READY_FIFO"))
            exec_wait_ms = 5000;
#endif
        uint64_t exec_deadline = deadline_after_ms(mono_ns(), exec_wait_ms);
        while (mono_ns() < exec_deadline) {
            waited = waitpid(child, &trace_status, WNOHANG);
            if (waited == child) break;
            if (waited < 0 && errno != EINTR) break;
            int pending = pending_control_signal();
            if (pending < 0) { reason = "signal-pending-check-failure"; break; }
            if (pending) {
                if (!interrupted_signal ||
                    control_signal_priority(pending) < control_signal_priority(interrupted_signal))
                    interrupted_signal = pending;
                reason = "interrupted";
                break;
            }
            sleep_ms(1);
        }
        if (waited == child && WIFSTOPPED(trace_status) && WSTOPSIG(trace_status) == SIGTRAP &&
            proc_executable_matches(supervisor.root_pid, &command_identity)) {
            exec_trace_stop = 1;
            if (ptrace(PTRACE_SETOPTIONS, child, NULL, (void *)(uintptr_t)PTRACE_O_EXITKILL) != 0)
                reason = "exec-trace-exitkill-failure";
#ifdef EVIDENCE_TEST_HOOKS
            else if (parent_exec_stop_barrier(supervisor.self_pid, &root) != 0)
                reason = interrupted_signal ? "interrupted" : "parent-exec-stop-barrier-failure";
#endif
        } else {
            if (waited == child && (WIFEXITED(trace_status) || WIFSIGNALED(trace_status))) {
                supervisor.root_reaped = 1;
                supervisor.root_status = trace_status;
            }
            if (!reason) reason = waited == 0 ? "root-exec-timeout" : "root-exec-identity-failure";
        }
    }
    if (sigprocmask(SIG_SETMASK, &runmask, NULL) != 0 && !reason) reason = "signal-mask-failure";
    if (interrupted_signal && !reason) reason = "interrupted";

#ifdef EVIDENCE_TEST_HOOKS
    const char *pre_delay = getenv("SIMPLE_STAGE3_RSS_TEST_PRE_SAMPLE_DELAY_MS");
    uint64_t pre_delay_ms = 0;
    if (pre_delay && parse_u64(pre_delay, &pre_delay_ms) == 0) sleep_ms(pre_delay_ms);
#endif
    if (!reason && sample_tree(&supervisor, &writer, &config, &evidence, &stats, &reason) != 0) {
        if (!reason) reason = "initial-sample-failure";
    }
    if (interrupted_signal) reason = "interrupted";
    if (!reason && writer_sync(&writer, 1) != 0) reason = "initial-sample-sync-failure";
    if (exec_trace_stop) {
        if (interrupted_signal && !reason) reason = "interrupted";
        if (reason) {
            /* The ptrace relationship itself pins this exact process identity.
             * SIGKILL is injected as part of detach, so no measured user code
             * can run between an abort decision and termination. */
            if (evidence_ptrace_detach(child, SIGKILL) != 0 &&
                signal_member(&supervisor.members[root_member], SIGKILL) != 0)
                (void)ptrace(PTRACE_KILL, child, NULL, NULL);
        } else if (evidence_ptrace_detach(child, 0) != 0) {
            (void)ptrace(PTRACE_KILL, child, NULL, NULL);
            reason = "exec-trace-detach-failure";
        } else {
            /* This is the only successful measured-executable release. */
            pre_exec_pidfd = -1;
#ifdef EVIDENCE_TEST_HOOKS
            const char *post_release_delay =
                getenv("SIMPLE_STAGE3_RSS_TEST_POST_TRACE_RELEASE_DELAY_MS");
            uint64_t post_release_delay_ms = 0;
            if (post_release_delay &&
                parse_u64(post_release_delay, &post_release_delay_ms) == 0)
                (void)sleep_ms(post_release_delay_ms);
#endif
        }
        exec_trace_stop = 0;
    }
    pre_exec_pidfd = -1;
    uint64_t interval_ns = config.interval_ms * UINT64_C(1000000);
    uint64_t next_sample_ns = stats.last_batch_ns > UINT64_MAX - interval_ns
        ? UINT64_MAX : stats.last_batch_ns + interval_ns;
    while (!reason) {
        int echild = 0;
        reap_children(&supervisor, &echild);
        if (interrupted_signal) { reason = "interrupted"; break; }
        if (supervisor.root_reaped) break;
        uint64_t now = mono_ns();
        if (!now || now - started_ns > config.max_runtime_ms * UINT64_C(1000000)) {
            reason = "runtime-limit"; break;
        }
        if (sleep_until_ns(next_sample_ns) != 0) { reason = "clock-failure"; break; }
        if (interrupted_signal) { reason = "interrupted"; break; }
        if (sample_tree(&supervisor, &writer, &config, &evidence, &stats, &reason) != 0) {
            if (interrupted_signal) { reason = "interrupted"; break; }
            if (reason && !strcmp(reason, "root-loss")) {
                int echild = 0;
                reap_children(&supervisor, &echild);
                if (supervisor.root_reaped) { reason = NULL; break; }
            }
            break;
        }
        next_sample_ns = next_sample_ns > UINT64_MAX - interval_ns
            ? UINT64_MAX : next_sample_ns + interval_ns;
        uint64_t after_sample_ns = mono_ns();
        if (!after_sample_ns) { reason = "clock-failure"; break; }
        if (next_sample_ns <= after_sample_ns) {
            uint64_t behind = after_sample_ns - next_sample_ns;
            uint64_t skipped = behind / interval_ns + 1;
            if (skipped > (UINT64_MAX - next_sample_ns) / interval_ns) {
                reason = "clock-overflow";
                break;
            }
            next_sample_ns += skipped * interval_ns;
        }
    }
    if (cleanup_tree(&supervisor, &config, &survivors,
                     &survivors_known, &closure_proven, &cleanup_stage) != 0 && !reason)
        reason = survivors_known && survivors ? "cleanup-timeout" : "cleanup-identity-failure";
    if (interrupted_signal && !reason) reason = "interrupted";
    if (!supervisor.root_reaped) {
        int echild = 0;
        reap_children(&supervisor, &echild);
    }
    if (supervisor.root_reaped) {
        if (WIFEXITED(supervisor.root_status)) command_exit = WEXITSTATUS(supervisor.root_status);
        else if (WIFSIGNALED(supervisor.root_status)) {
            command_signal = WTERMSIG(supervisor.root_status);
            command_exit = 128 + command_signal;
        }
    }
    if (!reason && (!supervisor.root_reaped || !stats.root_samples))
        reason = !stats.root_samples ? "missing-root-sample" : "root-status-missing";
    if (!reason && (command_exit != 0 || command_signal != 0))
        reason = command_signal ? "command-signal" : "command-exit";
    int result;
    if (interrupted_signal && !reason) reason = "interrupted";
    if (!reason && (!closure_proven || !survivors_known || survivors != 0))
        reason = "cleanup-identity-failure";
    if (!reason && !raw_target_matches(&raw_target))
        reason = "raw-path-identity-failure";
    if (!reason) {
        /* Signals remain blocked across the final pending check and terminal
         * commit.  Setting this flag is the success linearization point: a
         * signal pending before it forces failure; signals ordered after it
         * cannot run a handler that rewrites the committed outcome. */
        if (sigprocmask(SIG_BLOCK, &controls, NULL) != 0) reason = "signal-mask-failure";
        int final_pending = reason ? 0 : pending_control_signal();
        if (final_pending < 0) reason = "signal-pending-check-failure";
        else if (final_pending || interrupted_signal) reason = "interrupted";
    }
    int completion_committed = 0;
    int terminal_commit_failed = 0;
    off_t terminal_rollback_offset = -1;
    if (!reason) {
        off_t terminal_offset = lseek(raw_target.fd, 0, SEEK_END);
        terminal_rollback_offset = terminal_offset;
        uint64_t terminal_bytes = writer.bytes;
        uint64_t terminal_control_bytes = writer.control_bytes;
        uint64_t terminal_control_records = writer.control_records;
        result = terminal_offset >= 0 &&
                 write_terminal_record(&writer, &supervisor, &config, &evidence, &stats,
                                       cleanup_stage) == 0 ? 0 : 2;
        if (result != 0) terminal_commit_failed = 1;
        if (result == 0 && !raw_target_matches(&raw_target)) {
            if (ftruncate(raw_target.fd, terminal_offset) == 0) {
                writer.bytes = terminal_bytes;
                writer.control_bytes = terminal_control_bytes;
                writer.control_records = terminal_control_records;
                (void)writer_record(&writer, 1,
                    "failure schema=%s run_id=%s mono_ns=%" PRIu64
                    " root_pid=%ld root_start=%" PRIu64
                    " raw_dev=%" PRIu64 " raw_ino=%" PRIu64 " environment_sha256=%s"
                    " command_dev=%" PRIu64 " command_ino=%" PRIu64 " command_sha256=%s"
                    " script_dev=%" PRIu64 " script_ino=%" PRIu64 " script_sha256=%s"
                    " reason=raw-path-identity-failure exit_code=%d signal=%d"
                    " sample_records=%" PRIu64 " sample_batches=%" PRIu64
                    " survivors=0 closure_proven=1 zero_survivors=1\n",
                    RAW_SCHEMA, run_id, mono_ns(), (long)supervisor.root_pid,
                    supervisor.root_start, evidence.raw_dev, evidence.raw_ino,
                    evidence.environment_sha256, evidence.command.dev, evidence.command.ino,
                    evidence.command.sha256, evidence.script.dev, evidence.script.ino,
                    evidence.script.ino ? evidence.script.sha256 : "none", command_exit,
                    command_signal, stats.sample_records, stats.sample_batches);
            }
            result = 2;
        }
        int post_terminal_pending = pending_control_signal();
        if (post_terminal_pending < 0 || post_terminal_pending || interrupted_signal) {
            terminal_commit_failed = 1;
            result = post_terminal_pending > 0 ? 128 + post_terminal_pending : 2;
        }
    } else {
        if (!reason) reason = "cleanup-timeout";
        (void)write_failure_record(&writer, &supervisor, &evidence, &stats,
                                   reason, command_exit, command_signal, survivors,
                                   survivors_known, closure_proven);
        if (!strcmp(reason, "interrupted") && interrupted_signal) result = 128 + interrupted_signal;
        else if (!strcmp(reason, "command-exit") || !strcmp(reason, "command-signal")) result = command_exit;
        else result = 2;
    }
    /* A complete terminal is not committed until its bytes, pathname, and
     * directory entry are durable and the data descriptor closes cleanly. */
    int finalization_failed = terminal_commit_failed;
    int terminal_rolled_back = 0;
    if (terminal_commit_failed && terminal_rollback_offset >= 0) {
        if (ftruncate(raw_target.fd, terminal_rollback_offset) == 0 &&
            terminal_rollback_sync(raw_target.fd) == 0) terminal_rolled_back = 1;
        else finalization_failed = 1;
    }
    if ((!terminal_commit_failed && terminal_durability_sync(raw_target.fd) != 0) ||
        !raw_target_matches(&raw_target) || fsync(raw_target.parent_fd) != 0)
        finalization_failed = 1;
    if (!finalization_failed && result == 0) {
        int commit_pending = pending_control_signal();
        if (commit_pending < 0 || commit_pending || interrupted_signal) {
            if (terminal_rollback_offset < 0 ||
                ftruncate(raw_target.fd, terminal_rollback_offset) != 0 ||
                terminal_rollback_sync(raw_target.fd) != 0) finalization_failed = 1;
            else finalization_failed = 1;
            result = commit_pending > 0 ? 128 + commit_pending : 2;
        }
    }
    /* Any failure after terminal emission first makes the descriptor durable
     * without that terminal.  Unlink is only a second quarantine fence. */
    if (finalization_failed && terminal_rollback_offset >= 0 && !terminal_rolled_back) {
        if (ftruncate(raw_target.fd, terminal_rollback_offset) == 0 &&
            terminal_rollback_sync(raw_target.fd) == 0) terminal_rolled_back = 1;
    }
    if (close(raw_target.fd) != 0) finalization_failed = 1;
    raw_target.fd = -1;
    if (finalization_failed) {
        struct stat visible;
        if (fstatat(raw_target.parent_fd, raw_target.leaf, &visible,
                    AT_SYMLINK_NOFOLLOW) == 0 && S_ISREG(visible.st_mode) &&
            (uint64_t)visible.st_dev == raw_target.dev &&
            (uint64_t)visible.st_ino == raw_target.ino) {
            if (quarantine_raw_unlink(raw_target.parent_fd,
                                      raw_target.leaf) != 0)
                fprintf(stderr, "could not unlink failed raw evidence\n");
            /* Attempt the directory durability fence independently: an
             * unlink fault must not suppress this ownership obligation. */
            if (quarantine_raw_parent_sync(raw_target.parent_fd) != 0)
                fprintf(stderr, "could not sync failed raw evidence parent\n");
        }
        result = 2;
    } else if (result == 0) {
        completion_committed = 1;
    }
    if (close(raw_target.parent_fd) != 0 && !completion_committed) result = 2;
    raw_target.parent_fd = -1;
    (void)completion_committed;
    pre_exec_pidfd = -1;
    launch_gate_write_fd = -1;
#ifdef EVIDENCE_TEST_HOOKS
    control_signal_observation_fd = -1;
    if (test_signal_observer_fd >= 0) (void)close(test_signal_observer_fd);
#endif
    close_members(&supervisor);
    free(supervisor.snapshot); free(supervisor.belongs); free(command_argv_hex);
    free(bound_script_argv);
    if (script_fd >= 0) close(script_fd);
    close(command_fd);
    return result;

pre_fork_fail:
#ifdef EVIDENCE_TEST_HOOKS
    control_signal_observation_fd = -1;
    if (test_signal_observer_fd >= 0) (void)close(test_signal_observer_fd);
#endif
    free(supervisor.snapshot); free(supervisor.belongs);
    (void)unlinkat(raw_target.parent_fd, raw_target.leaf, 0);
    (void)fsync(raw_target.parent_fd);
    close_raw_target(&raw_target); free(command_argv_hex); free(bound_script_argv);
    if (script_fd >= 0) close(script_fd);
    close(command_fd);
    return 2;
}

/* Strict parsing/analyzer implementation is below. */

static void usage(const char *program) {
    fprintf(stderr,
        "usage: %s run [limits] --raw FILE --self-sha256 HEX --sha256 HEX --run-id ID "
        "[--script FILE --script-sha256 HEX] -- EXE [ARGS...]\n"
        "       %s validate --run-id ID FILE\n"
        "       %s analyze --samples RAW --memory SNAPSHOT --phase PROFILE "
        "--descriptor FILE --provenance FILE --candidate-provenance FILE "
        "--candidate-provenance-sha256 HEX --candidate-provenance-verify-receipt FILE "
        "--candidate-provenance-verify-receipt-sha256 HEX --launch-plan FILE --run-id ID "
        "--analyzer-sha256 HEX --expected-sampler-sha256 HEX "
        "--expected-admitted-compiler-sha256 HEX "
        "--expected-script-sha256 HEX|none --output-dir ABSENT_DIR\n",
        program, program, program);
}

static int validate_file(const char *path, const char *run_id);
static int analyze_files(int argc, char **argv);

#ifdef EVIDENCE_TEST_HOOKS
static int test_identity_signal(int argc, char **argv) {
    if (argc != 5) return 64;
    pid_t pid;
    uint64_t start, sig;
    if (parse_pid(argv[2], &pid) || parse_u64(argv[3], &start) ||
        parse_u64(argv[4], &sig) || !sig || sig >= NSIG) return 64;
    int pidfd = pidfd_open_checked(pid, start);
    if (pidfd < 0) return 3;
    Proc check;
    if (proc_stat(pid, &check) || check.start != start) { close(pidfd); return 3; }
    int result = syscall(SYS_pidfd_send_signal, pidfd, (int)sig, NULL, 0) == 0 ? 0 : 2;
    close(pidfd);
    return result;
}
#endif

int main(int argc, char **argv) {
#ifdef EVIDENCE_TEST_HOOKS
    if (getenv("SIMPLE_STAGE3_RSS_TEST_INHERIT_SIGCHLD_IGN"))
        (void)signal(SIGCHLD, SIG_IGN);
    if (getenv("SIMPLE_STAGE3_RSS_TEST_INHERIT_NOCLDWAIT")) {
        struct sigaction inherited_child;
        memset(&inherited_child, 0, sizeof(inherited_child));
        inherited_child.sa_handler = SIG_DFL;
        inherited_child.sa_flags = SA_NOCLDWAIT;
        sigemptyset(&inherited_child.sa_mask);
        (void)sigaction(SIGCHLD, &inherited_child, NULL);
    }
    if (getenv("SIMPLE_STAGE3_RSS_TEST_INHERIT_CONTROL_BLOCK")) {
        sigset_t inherited;
        sigemptyset(&inherited);
        sigaddset(&inherited, SIGHUP); sigaddset(&inherited, SIGINT);
        sigaddset(&inherited, SIGTERM); sigaddset(&inherited, SIGQUIT);
        (void)sigprocmask(SIG_BLOCK, &inherited, NULL);
    }
#endif
    if (argc >= 2 && !strcmp(argv[1], "run"))
        return EVIDENCE_BUILD_ROLE == 2 ? 64 : run_supervised(argc, argv);
    if (argc == 5 && !strcmp(argv[1], "validate") && !strcmp(argv[2], "--run-id"))
        return EVIDENCE_BUILD_ROLE == 1 ? 64 : validate_file(argv[4], argv[3]);
    if (argc >= 2 && !strcmp(argv[1], "analyze"))
        return EVIDENCE_BUILD_ROLE == 1 ? 64 : analyze_files(argc, argv);
#ifdef EVIDENCE_TEST_HOOKS
    if (argc >= 2 && !strcmp(argv[1], "test-identity-signal")) return test_identity_signal(argc, argv);
#endif
    usage(argv[0]);
    return 64;
}

enum RawKey {
    RK_SCHEMA, RK_RUN, RK_MONO, RK_ROOT_PID, RK_ROOT_START, RK_OUTER_PGID,
    RK_RAW_DEV, RK_RAW_INO, RK_ENV_SHA,
    RK_SAMPLER_DEV, RK_SAMPLER_INO, RK_SAMPLER_SHA,
    RK_COMMAND_DEV, RK_COMMAND_INO, RK_COMMAND_SHA,
    RK_SCRIPT_DEV, RK_SCRIPT_INO, RK_SCRIPT_SHA, RK_COMMAND_ARGV,
    RK_INTERVAL, RK_MAX_GAP, RK_MAX_RSS, RK_TERM_GRACE, RK_KILL_GRACE,
    RK_MAX_RUNTIME, RK_MAX_BATCHES, RK_MAX_RECORDS, RK_MAX_TRACKED, RK_MAX_RAW,
    RK_SYNC_BATCHES, RK_SYNC_MS, RK_RESERVE_BYTES, RK_RESERVE_RECORDS,
    RK_BATCH_SEQ, RK_BATCH_START, RK_BATCH_END, RK_BATCH_RECORDS,
    RK_PID, RK_START, RK_PPID, RK_PGRP, RK_SID, RK_STATE,
    RK_RSS, RK_HWM, RK_ANON, RK_FILE, RK_TREE_RSS, RK_ARGV,
    RK_EXIT, RK_SIGNAL, RK_SAMPLE_RECORDS, RK_SAMPLE_BATCHES, RK_SURVIVORS,
    RK_CLOSURE_PROVEN, RK_ZERO_SURVIVORS, RK_CLEANUP,
    RK_OBS_START_GAP_NS, RK_OBS_BATCH_DURATION_NS, RK_MAX_OBS_GAP,
    RK_PEAK_RSS, RK_REASON,
    RK_COUNT
};

static const char *const raw_key_names[RK_COUNT] = {
    "schema", "run_id", "mono_ns", "root_pid", "root_start", "outer_pgid",
    "raw_dev", "raw_ino", "environment_sha256",
    "sampler_dev", "sampler_ino", "sampler_sha256",
    "command_dev", "command_ino", "command_sha256",
    "script_dev", "script_ino", "script_sha256", "command_argv_hex",
    "interval_ms", "max_gap_ms", "max_rss_kb", "term_grace_ms", "kill_grace_ms",
    "max_runtime_ms", "max_batches", "max_records", "max_tracked", "max_raw_bytes",
    "sync_max_batches", "sync_max_ms", "closure_reserve_bytes", "closure_reserve_records",
    "batch_seq", "batch_start_ns", "batch_end_ns", "batch_records",
    "pid", "start", "ppid", "pgrp", "sid", "state",
    "vmrss_kb", "vmhwm_kb", "rssanon_kb", "rssfile_kb", "tree_rss_kb", "argv_hex",
    "exit_code", "signal", "sample_records", "sample_batches", "survivors",
    "closure_proven", "zero_survivors", "cleanup",
    "observed_max_start_gap_ns", "observed_max_batch_duration_ns",
    "max_observed_gap_ms", "peak_tree_rss_kb", "reason",
};

#define RB(key) (UINT64_C(1) << (key))

static int raw_key_id(const char *name) {
    for (int i = 0; i < RK_COUNT; ++i) if (!strcmp(name, raw_key_names[i])) return i;
    return -1;
}

typedef struct {
    char *kind;
    char *value[RK_COUNT];
    uint64_t mask;
} RawRecord;

static int parse_raw_record(char *line, RawRecord *record) {
    memset(record, 0, sizeof(*record));
    char *save = NULL;
    record->kind = strtok_r(line, " ", &save);
    if (!record->kind) return -1;
    char *token;
    while ((token = strtok_r(NULL, " ", &save))) {
        char *equals = strchr(token, '=');
        if (!equals || equals == token || !equals[1]) return -1;
        *equals = 0;
        int key = raw_key_id(token);
        if (key < 0 || (record->mask & RB(key))) return -1;
        record->mask |= RB(key);
        record->value[key] = equals + 1;
    }
    return 0;
}

static uint64_t raw_identity_mask(void) {
    return RB(RK_SCHEMA)|RB(RK_RUN)|RB(RK_MONO)|RB(RK_ROOT_PID)|RB(RK_ROOT_START)|
           RB(RK_RAW_DEV)|RB(RK_RAW_INO)|RB(RK_ENV_SHA)|
           RB(RK_COMMAND_DEV)|RB(RK_COMMAND_INO)|RB(RK_COMMAND_SHA)|
           RB(RK_SCRIPT_DEV)|RB(RK_SCRIPT_INO)|RB(RK_SCRIPT_SHA);
}

static uint64_t raw_open_mask(void) {
    return raw_identity_mask() | RB(RK_OUTER_PGID)|RB(RK_SAMPLER_DEV)|
           RB(RK_SAMPLER_INO)|RB(RK_SAMPLER_SHA)|RB(RK_COMMAND_ARGV)|
           RB(RK_INTERVAL)|RB(RK_MAX_GAP)|RB(RK_MAX_RSS)|RB(RK_TERM_GRACE)|
           RB(RK_KILL_GRACE)|RB(RK_MAX_RUNTIME)|RB(RK_MAX_BATCHES)|RB(RK_MAX_RECORDS)|
           RB(RK_MAX_TRACKED)|RB(RK_MAX_RAW)|RB(RK_SYNC_BATCHES)|RB(RK_SYNC_MS)|
           RB(RK_RESERVE_BYTES)|RB(RK_RESERVE_RECORDS);
}

static uint64_t raw_sample_mask(void) {
    return raw_identity_mask() | RB(RK_BATCH_SEQ)|RB(RK_PID)|RB(RK_START)|RB(RK_PPID)|RB(RK_PGRP)|
           RB(RK_SID)|RB(RK_STATE)|RB(RK_RSS)|RB(RK_HWM)|RB(RK_ANON)|RB(RK_FILE)|
           RB(RK_TREE_RSS)|RB(RK_ARGV);
}

static uint64_t raw_batch_close_mask(void) {
    return raw_identity_mask() | RB(RK_BATCH_SEQ)|RB(RK_BATCH_START)|RB(RK_BATCH_END)|
           RB(RK_BATCH_RECORDS)|RB(RK_TREE_RSS);
}

static uint64_t raw_terminal_mask(void) {
    return raw_identity_mask() | RB(RK_EXIT)|RB(RK_SIGNAL)|RB(RK_INTERVAL)|
           RB(RK_MAX_GAP)|RB(RK_MAX_OBS_GAP)|RB(RK_MAX_RSS)|RB(RK_PEAK_RSS)|
           RB(RK_SAMPLE_RECORDS)|RB(RK_SAMPLE_BATCHES)|RB(RK_SURVIVORS)|
           RB(RK_CLOSURE_PROVEN)|RB(RK_ZERO_SURVIVORS)|RB(RK_CLEANUP)|
           RB(RK_OBS_START_GAP_NS)|RB(RK_OBS_BATCH_DURATION_NS);
}

typedef struct {
    pid_t root_pid;
    uint64_t root_start, first_sample_ns, terminal_ns;
    uint64_t interval_ms, max_gap_ms, max_rss_kb, max_observed_gap_ms;
    uint64_t observed_max_start_gap_ns, observed_max_batch_duration_ns;
    uint64_t raw_dev, raw_ino, term_grace_ms, kill_grace_ms, max_runtime_ms;
    uint64_t max_batches, max_records, max_tracked, max_raw_bytes;
    uint64_t sample_records, sample_batches, peak_tree_rss_kb;
    FileIdentity sampler, command, script;
    char environment_sha256[65];
    char command_argv_hex[MAX_ARGV_BYTES * 2 + 1];
} RawSummary;

static int record_number(const RawRecord *record, enum RawKey key, uint64_t *out) {
    return record->value[key] ? parse_u64(record->value[key], out) : -1;
}

static int identity_matches_record(const RawSummary *summary, const RawRecord *record) {
    uint64_t raw_dev, raw_ino, dev, ino, script_dev, script_ino;
    return record_number(record, RK_RAW_DEV, &raw_dev) == 0 &&
           record_number(record, RK_RAW_INO, &raw_ino) == 0 &&
           raw_dev == summary->raw_dev && raw_ino == summary->raw_ino &&
           !strcmp(record->value[RK_ENV_SHA], summary->environment_sha256) &&
           record_number(record, RK_COMMAND_DEV, &dev) == 0 &&
           record_number(record, RK_COMMAND_INO, &ino) == 0 &&
           record_number(record, RK_SCRIPT_DEV, &script_dev) == 0 &&
           record_number(record, RK_SCRIPT_INO, &script_ino) == 0 &&
           dev == summary->command.dev && ino == summary->command.ino &&
           script_dev == summary->script.dev && script_ino == summary->script.ino &&
           !strcmp(record->value[RK_COMMAND_SHA], summary->command.sha256) &&
           !strcmp(record->value[RK_SCRIPT_SHA],
                   summary->script.ino ? summary->script.sha256 : "none");
}

static int parse_complete_raw_fd(int fd, const char *want_run_id, RawSummary *summary) {
    if (!safe_run_id(want_run_id)) return -1;
    int stream_fd = dup(fd);
    if (stream_fd < 0 || lseek(stream_fd, 0, SEEK_SET) < 0) {
        if (stream_fd >= 0) close(stream_fd);
        return -1;
    }
    FILE *stream = fdopen(stream_fd, "r");
    if (!stream) { close(stream_fd); return -1; }
    memset(summary, 0, sizeof(*summary));
    char *line = NULL;
    size_t capacity = 0;
    ssize_t length;
    unsigned line_number = 0;
    int saw_open = 0, saw_terminal = 0, saw_failure = 0;
    uint64_t last_mono = 0, batch_mono = 0, previous_batch_mono = 0;
    uint64_t batch_rss_sum = 0, batch_declared_tree = 0, computed_peak = 0;
    uint64_t current_batch_records = 0;
    int current_batch_root = 0;
    pid_t seen_pid[MAX_TRACKED];
    uint64_t seen_start[MAX_TRACKED];
    size_t seen_count = 0;
    int bad = 0;
    while ((length = getline(&line, &capacity, stream)) >= 0) {
        ++line_number;
        if (length <= 1 || (size_t)length > MAX_RECORD_BYTES || line[length-1] != '\n' ||
            memchr(line, '\0', (size_t)length - 1)) { bad = 1; break; }
        line[length-1] = 0;
        RawRecord record;
        if (parse_raw_record(line, &record) != 0 || !record.value[RK_SCHEMA] ||
            strcmp(record.value[RK_SCHEMA], RAW_SCHEMA) || !record.value[RK_RUN] ||
            strcmp(record.value[RK_RUN], want_run_id)) { bad = 1; break; }
        uint64_t mono;
        if (record_number(&record, RK_MONO, &mono) || !mono || mono < last_mono) { bad = 1; break; }
        last_mono = mono;
        if (!strcmp(record.kind, "open")) {
            if (line_number != 1 || saw_open || record.mask != raw_open_mask()) { bad = 1; break; }
            uint64_t root_pid, outer_pgid, sampler_dev, sampler_ino;
            uint64_t sync_batches, sync_ms, reserve_bytes, reserve_records;
            if (record_number(&record, RK_ROOT_PID, &root_pid) || !root_pid || root_pid > INT_MAX ||
                record_number(&record, RK_ROOT_START, &summary->root_start) || !summary->root_start ||
                record_number(&record, RK_OUTER_PGID, &outer_pgid) || !outer_pgid || outer_pgid > INT_MAX ||
                record_number(&record, RK_RAW_DEV, &summary->raw_dev) ||
                record_number(&record, RK_RAW_INO, &summary->raw_ino) || !summary->raw_ino ||
                record_number(&record, RK_SAMPLER_DEV, &sampler_dev) ||
                record_number(&record, RK_SAMPLER_INO, &sampler_ino) || !sampler_ino ||
                record_number(&record, RK_COMMAND_DEV, &summary->command.dev) ||
                record_number(&record, RK_COMMAND_INO, &summary->command.ino) || !summary->command.ino ||
                record_number(&record, RK_SCRIPT_DEV, &summary->script.dev) ||
                record_number(&record, RK_SCRIPT_INO, &summary->script.ino) ||
                record_number(&record, RK_INTERVAL, &summary->interval_ms) ||
                summary->interval_ms != DEFAULT_INTERVAL_MS ||
                record_number(&record, RK_MAX_GAP, &summary->max_gap_ms) ||
                summary->max_gap_ms != DEFAULT_MAX_GAP_MS ||
                record_number(&record, RK_MAX_RSS, &summary->max_rss_kb) ||
                summary->max_rss_kb != DEFAULT_MAX_RSS_KB ||
                record_number(&record, RK_TERM_GRACE, &summary->term_grace_ms) ||
                summary->term_grace_ms != DEFAULT_TERM_GRACE_MS ||
                record_number(&record, RK_KILL_GRACE, &summary->kill_grace_ms) ||
                summary->kill_grace_ms != DEFAULT_KILL_GRACE_MS ||
                record_number(&record, RK_MAX_RUNTIME, &summary->max_runtime_ms) ||
                summary->max_runtime_ms != DEFAULT_MAX_RUNTIME_MS ||
                record_number(&record, RK_MAX_BATCHES, &summary->max_batches) ||
                summary->max_batches != DEFAULT_MAX_BATCHES ||
                record_number(&record, RK_MAX_RECORDS, &summary->max_records) ||
                summary->max_records != DEFAULT_MAX_RECORDS ||
                record_number(&record, RK_MAX_TRACKED, &summary->max_tracked) ||
                summary->max_tracked != MAX_TRACKED ||
                record_number(&record, RK_MAX_RAW, &summary->max_raw_bytes) ||
                summary->max_raw_bytes != DEFAULT_MAX_RAW_BYTES ||
                record_number(&record, RK_SYNC_BATCHES, &sync_batches) || sync_batches != SYNC_MAX_BATCHES ||
                record_number(&record, RK_SYNC_MS, &sync_ms) || sync_ms != SYNC_MAX_MS ||
                record_number(&record, RK_RESERVE_BYTES, &reserve_bytes) || reserve_bytes != CLOSURE_RESERVE_BYTES ||
                record_number(&record, RK_RESERVE_RECORDS, &reserve_records) || reserve_records != CLOSURE_RESERVE_RECORDS ||
                !valid_sha256(record.value[RK_SAMPLER_SHA]) ||
                !valid_sha256(record.value[RK_COMMAND_SHA]) ||
                !valid_sha256(record.value[RK_ENV_SHA]) ||
                !valid_hex(record.value[RK_COMMAND_ARGV], MAX_ARGV_BYTES)) { bad = 1; break; }
            summary->root_pid = (pid_t)root_pid;
            summary->sampler.dev = sampler_dev; summary->sampler.ino = sampler_ino;
            strcpy(summary->sampler.sha256, record.value[RK_SAMPLER_SHA]);
            strcpy(summary->command.sha256, record.value[RK_COMMAND_SHA]);
            strcpy(summary->environment_sha256, record.value[RK_ENV_SHA]);
            if (summary->script.ino) {
                if (!valid_sha256(record.value[RK_SCRIPT_SHA])) { bad = 1; break; }
                strcpy(summary->script.sha256, record.value[RK_SCRIPT_SHA]);
            } else if (summary->script.dev || strcmp(record.value[RK_SCRIPT_SHA], "none")) {
                bad = 1; break;
            }
            strcpy(summary->command_argv_hex, record.value[RK_COMMAND_ARGV]);
            summary->sampler.dev = sampler_dev;
            summary->sampler.ino = sampler_ino;
            saw_open = 1;
            continue;
        }
        if (!saw_open || saw_terminal || saw_failure) { bad = 1; break; }
        uint64_t root_pid, root_start;
        if (record_number(&record, RK_ROOT_PID, &root_pid) ||
            record_number(&record, RK_ROOT_START, &root_start) ||
            root_pid != (uint64_t)summary->root_pid || root_start != summary->root_start ||
            !identity_matches_record(summary, &record)) { bad = 1; break; }
        if (!strcmp(record.kind, "failure")) {
            saw_failure = 1;
            continue;
        }
        if (!strcmp(record.kind, "sample")) {
            if (record.mask != raw_sample_mask()) { bad = 1; break; }
            uint64_t batch_seq, pid, start, ppid, pgrp, sid, rss, hwm, anon, file_rss, tree;
            if (record_number(&record, RK_BATCH_SEQ, &batch_seq) ||
                record_number(&record, RK_PID, &pid) || !pid || pid > INT_MAX ||
                record_number(&record, RK_START, &start) || !start ||
                record_number(&record, RK_PPID, &ppid) || ppid > INT_MAX ||
                record_number(&record, RK_PGRP, &pgrp) || pgrp > INT_MAX ||
                record_number(&record, RK_SID, &sid) || sid > INT_MAX ||
                record_number(&record, RK_RSS, &rss) || record_number(&record, RK_HWM, &hwm) ||
                record_number(&record, RK_ANON, &anon) || record_number(&record, RK_FILE, &file_rss) ||
                record_number(&record, RK_TREE_RSS, &tree) || tree >= summary->max_rss_kb ||
                !record.value[RK_STATE] || strlen(record.value[RK_STATE]) != 1 ||
                !valid_hex(record.value[RK_ARGV], MAX_CMDLINE_BYTES)) { bad = 1; break; }
            size_t identity;
            for (identity = 0; identity < seen_count; ++identity) {
                if (seen_pid[identity] == (pid_t)pid) {
                    if (seen_start[identity] != start) bad = 1;
                    break;
                }
            }
            if (bad) break;
            if (identity == seen_count) {
                if (seen_count == MAX_TRACKED) { bad = 1; break; }
                seen_pid[seen_count] = (pid_t)pid;
                seen_start[seen_count++] = start;
            }
            if (!batch_mono) {
                if (batch_seq != summary->sample_batches) { bad = 1; break; }
                if (!summary->first_sample_ns) summary->first_sample_ns = mono;
                if (previous_batch_mono) {
                    uint64_t gap = mono - previous_batch_mono;
                    if (gap > summary->max_gap_ms * UINT64_C(1000000)) { bad = 1; break; }
                    if (gap > summary->observed_max_start_gap_ns)
                        summary->observed_max_start_gap_ns = gap;
                    uint64_t gap_ms = (gap + UINT64_C(999999)) / UINT64_C(1000000);
                    if (gap_ms > summary->max_observed_gap_ms)
                        summary->max_observed_gap_ms = gap_ms;
                }
                batch_mono = mono;
                batch_rss_sum = 0;
                batch_declared_tree = tree;
                current_batch_records = 0;
                current_batch_root = 0;
            } else if (mono != batch_mono || tree != batch_declared_tree ||
                       batch_seq != summary->sample_batches) {
                bad = 1; break;
            }
            if (UINT64_MAX - batch_rss_sum < rss) { bad = 1; break; }
            batch_rss_sum += rss;
            current_batch_records++;
            summary->sample_records++;
            if ((pid_t)pid == summary->root_pid && start == summary->root_start) current_batch_root = 1;
            continue;
        }
        if (!strcmp(record.kind, "batch-close")) {
            if (record.mask != raw_batch_close_mask() || !batch_mono || !current_batch_records ||
                !current_batch_root || batch_rss_sum != batch_declared_tree) { bad = 1; break; }
            uint64_t batch_seq, start_ns, end_ns, records, tree;
            if (record_number(&record, RK_BATCH_SEQ, &batch_seq) ||
                batch_seq != summary->sample_batches ||
                record_number(&record, RK_BATCH_START, &start_ns) || start_ns != batch_mono ||
                record_number(&record, RK_BATCH_END, &end_ns) || end_ns != mono || end_ns < start_ns ||
                end_ns - start_ns > summary->max_gap_ms * UINT64_C(1000000) ||
                record_number(&record, RK_BATCH_RECORDS, &records) || records != current_batch_records ||
                record_number(&record, RK_TREE_RSS, &tree) || tree != batch_declared_tree) {
                bad = 1; break;
            }
            uint64_t duration_ns = end_ns - start_ns;
            if (duration_ns > summary->observed_max_batch_duration_ns)
                summary->observed_max_batch_duration_ns = duration_ns;
            uint64_t duration_ms = (duration_ns + UINT64_C(999999)) / UINT64_C(1000000);
            if (duration_ms > summary->max_observed_gap_ms)
                summary->max_observed_gap_ms = duration_ms;
            if (batch_declared_tree > computed_peak) computed_peak = batch_declared_tree;
            previous_batch_mono = batch_mono;
            batch_mono = 0;
            batch_rss_sum = batch_declared_tree = current_batch_records = 0;
            current_batch_root = 0;
            summary->sample_batches++;
            continue;
        }
        if (!strcmp(record.kind, "terminal")) {
            if (record.mask != raw_terminal_mask() || batch_mono || !summary->sample_batches) {
                bad = 1; break;
            }
            uint64_t exit_code, signal_number, interval, max_gap, max_observed, max_rss,
                     observed_start_gap, observed_batch_duration, closure_proven,
                     zero_survivors, peak, sample_records, sample_batches, survivors;
            if (record_number(&record, RK_EXIT, &exit_code) || exit_code != 0 ||
                record_number(&record, RK_SIGNAL, &signal_number) || signal_number != 0 ||
                record_number(&record, RK_INTERVAL, &interval) || interval != summary->interval_ms ||
                record_number(&record, RK_MAX_GAP, &max_gap) || max_gap != summary->max_gap_ms ||
                record_number(&record, RK_OBS_START_GAP_NS, &observed_start_gap) ||
                observed_start_gap != summary->observed_max_start_gap_ns ||
                observed_start_gap > max_gap * UINT64_C(1000000) ||
                record_number(&record, RK_OBS_BATCH_DURATION_NS, &observed_batch_duration) ||
                observed_batch_duration != summary->observed_max_batch_duration_ns ||
                observed_batch_duration > max_gap * UINT64_C(1000000) ||
                record_number(&record, RK_MAX_OBS_GAP, &max_observed) ||
                max_observed != summary->max_observed_gap_ms || max_observed > max_gap ||
                record_number(&record, RK_MAX_RSS, &max_rss) || max_rss != summary->max_rss_kb ||
                record_number(&record, RK_PEAK_RSS, &peak) || peak != computed_peak || peak >= max_rss ||
                record_number(&record, RK_SAMPLE_RECORDS, &sample_records) ||
                sample_records != summary->sample_records ||
                record_number(&record, RK_SAMPLE_BATCHES, &sample_batches) ||
                sample_batches != summary->sample_batches ||
                record_number(&record, RK_SURVIVORS, &survivors) || survivors != 0 ||
                record_number(&record, RK_CLOSURE_PROVEN, &closure_proven) || closure_proven != 1 ||
                record_number(&record, RK_ZERO_SURVIVORS, &zero_survivors) || zero_survivors != 1 ||
                (strcmp(record.value[RK_CLEANUP], "term-reaped") &&
                 strcmp(record.value[RK_CLEANUP], "kill-reaped"))) { bad = 1; break; }
            summary->peak_tree_rss_kb = peak;
            summary->terminal_ns = mono;
            saw_terminal = 1;
            continue;
        }
        bad = 1;
        break;
    }
    if (ferror(stream)) bad = 1;
    free(line);
    fclose(stream);
    if (!saw_open || !summary->sample_records || !summary->sample_batches ||
        !summary->first_sample_ns || !saw_terminal || saw_failure) bad = 1;
    return bad ? -1 : 0;
}

static int validate_file(const char *path, const char *run_id) {
    FileIdentity ignored;
    int fd = open_identity_nofollow(path, &ignored);
    if (fd < 0) { perror(path); return 2; }
    RawSummary summary;
    int result = parse_complete_raw_fd(fd, run_id, &summary) == 0 &&
                 summary.raw_dev == ignored.dev && summary.raw_ino == ignored.ino ? 0 : 2;
    close(fd);
    return result;
}

enum AuxKey {
    AK_SCHEMA, AK_RUN, AK_SEQ, AK_PID, AK_MONO, AK_EVENT, AK_PHASE,
    AK_SOURCE_INDEX, AK_SOURCE_KIND, AK_SOURCE_PATH, AK_RETAINED,
    AK_VALIDATION_KEYS, AK_VALIDATION_VALUES, AK_SHARED_TRAITS,
    AK_HIR_NAMES, AK_HIR_SYMBOLS, AK_HIR_FUNCTIONS, AK_HIR_CONSTANTS,
    AK_HIR_ENUMS, AK_HIR_STRUCTS, AK_HIR_CLASSES, AK_HEAP_LIVE,
    AK_HEAP_PEAK, AK_RSS, AK_HWM, AK_COUNT
};

static const char *const aux_key_names[AK_COUNT] = {
    "schema", "run_id", "seq", "pid", "monotonic_ms", "event", "phase",
    "source_index", "source_path_kind", "source_path", "retained_modules",
    "validation_keys", "validation_values", "shared_traits", "hir_names",
    "hir_symbols", "hir_functions", "hir_constants", "hir_enums", "hir_structs",
    "hir_classes", "heap_live_bytes", "heap_peak_bytes", "rss_kib", "hwm_kib",
};

typedef struct {
    char *value[AK_COUNT];
    uint32_t mask;
} AuxRecord;

static int parse_ordered_row(char *line, const char *const *keys, size_t key_count,
                             char **values);

static int parse_aux_record(char *line, AuxRecord *record) {
    memset(record, 0, sizeof(*record));
    if (parse_ordered_row(line, aux_key_names, AK_COUNT, record->value)) return -1;
    record->mask = (UINT32_C(1) << AK_COUNT) - 1;
    return 0;
}

static int parse_source_index(const char *text, int64_t *out) {
    if (!strcmp(text, "-1")) { *out = -1; return 0; }
    uint64_t value;
    if (parse_u64(text, &value) || value > INT64_MAX) return -1;
    *out = (int64_t)value;
    return 0;
}

static int percent_decode(const char *encoded, char *decoded, size_t capacity) {
    if (!encoded || !decoded || !capacity) return -1;
    size_t out = 0;
    for (size_t i = 0; encoded[i]; ++i) {
        unsigned char value = (unsigned char)encoded[i];
        if (value == '%') {
            unsigned char hi = (unsigned char)encoded[i + 1];
            unsigned char lo = hi ? (unsigned char)encoded[i + 2] : 0;
            if (!hi || !lo || !isxdigit(hi) || !isxdigit(lo)) return -1;
            int high = isdigit(hi) ? hi-'0' : (tolower(hi)-'a'+10);
            int low = isdigit(lo) ? lo-'0' : (tolower(lo)-'a'+10);
            value = (unsigned char)((high << 4) | low);
            i += 2;
            if (!value) return -1;
        }
        if (out + 1 >= capacity) return -1;
        decoded[out++] = (char)value;
    }
    decoded[out] = 0;
    return 0;
}

static int canonical_token(const char *encoded, char *decoded, size_t capacity, int v2) {
    if (percent_decode(encoded, decoded, capacity) != 0) return -1;
    static const char hex[] = "0123456789ABCDEF";
    char rebuilt[METADATA_MAX_RECORD_BYTES + 1];
    size_t used = 0;
    int singleton_dash = v2 && decoded[0] == '-' && decoded[1] == 0;
    for (const unsigned char *p = (const unsigned char *)decoded; *p; ++p) {
        int escaped = v2 ? (singleton_dash || *p < 0x21 || *p > 0x7e || *p == '%' || *p == '=')
                         : (*p == '%' || *p == ' ' || *p == '=' || *p == '\n' || *p == '\r');
        size_t need = escaped ? 3 : 1;
        if (used + need >= sizeof(rebuilt)) return -1;
        if (escaped) {
            rebuilt[used++] = '%';
            rebuilt[used++] = hex[*p >> 4];
            rebuilt[used++] = hex[*p & 15];
        } else rebuilt[used++] = (char)*p;
    }
    rebuilt[used] = 0;
    return strcmp(rebuilt, encoded) ? -1 : 0;
}

static int encode_token_v2(const char *decoded, char *encoded, size_t capacity) {
    static const char hex[] = "0123456789ABCDEF";
    if (!decoded || !*decoded || !encoded || !capacity) return -1;
    size_t used = 0;
    int singleton_dash = decoded[0] == '-' && decoded[1] == 0;
    for (const unsigned char *p = (const unsigned char *)decoded; *p; ++p) {
        int escaped = singleton_dash || *p < 0x21 || *p > 0x7e || *p == '%' || *p == '=';
        size_t need = escaped ? 3 : 1;
        if (used + need >= capacity) return -1;
        if (escaped) {
            encoded[used++] = '%';
            encoded[used++] = hex[*p >> 4];
            encoded[used++] = hex[*p & 15];
        } else encoded[used++] = (char)*p;
    }
    encoded[used] = 0;
    return 0;
}

static int safe_token(const char *text) {
    if (!text || !*text) return 0;
    for (const unsigned char *p = (const unsigned char *)text; *p; ++p)
        if (!((*p >= 'A' && *p <= 'Z') || (*p >= 'a' && *p <= 'z') ||
              (*p >= '0' && *p <= '9') || *p == '.' || *p == '_' || *p == ':' ||
              *p == '+' || *p == '-'))
            return 0;
    return 1;
}

static int normalized_absolute_path(const char *path) {
    if (!path || path[0] != '/' || !path[1] || strlen(path) > DECODED_PATH_MAX ||
        path[strlen(path) - 1] == '/' || strchr(path, '\\')) return 0;
    const char *segment = path + 1;
    while (*segment) {
        const char *slash = strchr(segment, '/');
        size_t length = slash ? (size_t)(slash - segment) : strlen(segment);
        if (!length || (length == 1 && segment[0] == '.') ||
            (length == 2 && segment[0] == '.' && segment[1] == '.')) return 0;
        for (size_t i = 0; i < length; ++i) {
            unsigned char c = (unsigned char)segment[i];
            if (!c || iscntrl(c)) return 0;
        }
        if (!slash) break;
        segment = slash + 1;
    }
    return 1;
}

static int canonical_path_token(const char *encoded, char *decoded, size_t capacity, int v2) {
    return canonical_token(encoded, decoded, capacity, v2) || !normalized_absolute_path(decoded)
        ? -1 : 0;
}

typedef struct {
    uint64_t bytes;
    uint64_t records;
} InputStats;

static int regular_file_size_cap(int fd, uint64_t cap, uint64_t *size) {
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) || st.st_size <= 0 ||
        (uint64_t)st.st_size > cap) return -1;
    if (size) *size = (uint64_t)st.st_size;
    return 0;
}

/* Parse an exact, single-space-separated row.  strtok_r is intentionally not
 * used: it accepts leading, trailing, and repeated separators. */
static int parse_ordered_row(char *line, const char *const *keys, size_t key_count,
                             char **values) {
    if (!line || !*line || line[0] == ' ' || line[strlen(line) - 1] == ' ') return -1;
    char *cursor = line;
    for (size_t i = 0; i < key_count; ++i) {
        char *end = strchr(cursor, ' ');
        if ((i + 1 < key_count) != (end != NULL)) return -1;
        if (end) {
            if (end == cursor || end[1] == ' ' || !end[1]) return -1;
            *end = 0;
        }
        char *equals = strchr(cursor, '=');
        if (!equals || equals == cursor || !equals[1] ||
            (size_t)(equals - cursor) != strlen(keys[i]) ||
            strncmp(cursor, keys[i], (size_t)(equals - cursor))) return -1;
        values[i] = equals + 1;
        cursor = end ? end + 1 : NULL;
    }
    return cursor ? -1 : 0;
}

static int open_identity_absolute(const char *path, uint64_t size_cap, FileIdentity *identity) {
    if (!normalized_absolute_path(path)) { errno = EINVAL; return -1; }
    char leaf[NAME_MAX + 1];
    int parent = parent_dir_fd(path, leaf);
    if (parent < 0) return -1;
    int fd = openat(parent, leaf, O_RDONLY | O_NOFOLLOW | O_CLOEXEC);
    int saved = errno;
    uint64_t ignored_size;
    if (fd >= 0 && (regular_file_size_cap(fd, size_cap, &ignored_size) != 0 ||
                    identity_fd(fd, identity) != 0)) {
        saved = errno;
        close(fd);
        fd = -1;
    }
    if (close(parent) != 0 && fd >= 0) {
        saved = errno;
        close(fd);
        fd = -1;
    }
    errno = saved;
    return fd;
}

typedef struct {
    char *source_path;
    char *module;
} DescriptorSource;

typedef struct {
    DescriptorSource *sources;
    size_t source_count;
    InputStats input;
} DescriptorSummary;

static void free_descriptor_summary(DescriptorSummary *summary) {
    if (!summary) return;
    for (size_t i = 0; i < summary->source_count; ++i) {
        free(summary->sources[i].source_path);
        free(summary->sources[i].module);
    }
    free(summary->sources);
    memset(summary, 0, sizeof(*summary));
}

static int parse_descriptor_fd(int fd, const char *run_id, DescriptorSummary *summary) {
    static const char *const keys[] = {
        "schema", "run_id", "seq", "event", "physical_index",
        "source_path_kind", "source_path", "module_kind", "module",
        "physical_count", "outcome",
    };
    memset(summary, 0, sizeof(*summary));
    uint64_t file_bytes;
    if (regular_file_size_cap(fd, METADATA_MAX_BYTES, &file_bytes) != 0) return -1;
    int stream_fd = dup(fd);
    if (stream_fd < 0 || lseek(stream_fd, 0, SEEK_SET) < 0) {
        if (stream_fd >= 0) close(stream_fd);
        return -1;
    }
    FILE *stream = fdopen(stream_fd, "r");
    if (!stream) { close(stream_fd); return -1; }
    char *line = NULL;
    size_t capacity = 0;
    ssize_t length;
    uint64_t expected_seq = 0, physical_count = 0;
    int saw_open = 0, saw_terminal = 0, bad = 0;
    while ((length = getline(&line, &capacity, stream)) >= 0) {
        if (length <= 1 || (size_t)length > METADATA_MAX_RECORD_BYTES ||
            line[length - 1] != '\n' || memchr(line, 0, (size_t)length - 1) ||
            summary->input.records >= METADATA_MAX_RECORDS) { bad = 1; break; }
        summary->input.bytes += (uint64_t)length;
        summary->input.records++;
        line[length - 1] = 0;
        char *value[sizeof(keys) / sizeof(keys[0])] = {0};
        uint64_t seq, count;
        int64_t index;
        if (parse_ordered_row(line, keys, sizeof(keys)/sizeof(keys[0]), value) ||
            strcmp(value[0], "simple-stage3-physical-source-descriptor-v1") ||
            strcmp(value[1], run_id) || parse_u64(value[2], &seq) || seq != expected_seq++ ||
            parse_source_index(value[4], &index) || parse_u64(value[9], &count)) {
            bad = 1; break;
        }
        if (!strcmp(value[3], "open")) {
            if (saw_open || seq || saw_terminal || index != -1 || !count || count > SIZE_MAX ||
                strcmp(value[5], "none") || strcmp(value[6], "-") ||
                strcmp(value[7], "none") || strcmp(value[8], "-") ||
                strcmp(value[10], "running")) { bad = 1; break; }
            physical_count = count;
            summary->sources = calloc((size_t)count, sizeof(*summary->sources));
            if (!summary->sources) { bad = 1; break; }
            saw_open = 1;
            continue;
        }
        if (!saw_open || saw_terminal || count != physical_count) { bad = 1; break; }
        if (!strcmp(value[3], "physical")) {
            if (index < 0 || (uint64_t)index != summary->source_count ||
                summary->source_count >= physical_count || strcmp(value[5], "recorded") ||
                strcmp(value[7], "recorded") || strcmp(value[10], "bound")) {
                bad = 1; break;
            }
            char decoded_path[DECODED_PATH_MAX + 1];
            char decoded_module[DECODED_MODULE_MAX + 1];
            if (canonical_path_token(value[6], decoded_path, sizeof(decoded_path), 1) ||
                canonical_token(value[8], decoded_module, sizeof(decoded_module), 1) ||
                !*decoded_module) { bad = 1; break; }
            for (size_t i = 0; i < summary->source_count; ++i)
                if (!strcmp(summary->sources[i].source_path, decoded_path)) { bad = 1; break; }
            if (bad) break;
            DescriptorSource *source = &summary->sources[summary->source_count++];
            source->source_path = strdup(decoded_path);
            source->module = strdup(decoded_module);
            if (!source->source_path || !source->module) { bad = 1; break; }
            continue;
        }
        if (!strcmp(value[3], "terminal")) {
            if (++saw_terminal != 1 || summary->source_count != physical_count ||
                index != -1 || strcmp(value[5], "none") || strcmp(value[6], "-") ||
                strcmp(value[7], "none") || strcmp(value[8], "-") ||
                strcmp(value[10], "complete")) { bad = 1; break; }
            continue;
        }
        bad = 1;
        break;
    }
    if (ferror(stream) || summary->input.bytes != file_bytes || !saw_open ||
        saw_terminal != 1 || summary->source_count != physical_count) bad = 1;
    free(line);
    if (fclose(stream) != 0) bad = 1;
    if (bad) { free_descriptor_summary(summary); return -1; }
    return 0;
}

enum PlanKey {
    PLAN_SCHEMA, PLAN_RUN_ID, PLAN_PLATFORM, PLAN_BACKEND, PLAN_MODE, PLAN_JOBS,
    PLAN_THREADS, PLAN_NO_STUB, PLAN_STREAMING, PLAN_UNIT_NAME, PLAN_MEMORY_MAX,
    PLAN_SWAP_MAX, PLAN_OOM, PLAN_INTERVAL, PLAN_MAX_GAP, PLAN_MAX_RSS,
    PLAN_COMPILER_WALL, PLAN_TRANSACTION_WALL, PLAN_MAX_BATCHES,
    PLAN_MAX_PROCESS_RECORDS, PLAN_MAX_TRACKED, PLAN_MAX_RAW_BYTES,
    PLAN_RESERVE_BYTES, PLAN_RESERVE_RECORDS, PLAN_TERM_GRACE, PLAN_KILL_REAP,
    PLAN_DESCRIPTOR_PATH, PLAN_DESCRIPTOR_SHA, PLAN_PROVENANCE_PATH,
    PLAN_PROVENANCE_SHA, PLAN_PROV_RECEIPT_PATH, PLAN_PROV_RECEIPT_SHA,
    PLAN_IDENTITY_PATH, PLAN_IDENTITY_SHA, PLAN_ARGV_PATH, PLAN_ARGV_SHA,
    PLAN_ENV_PATH, PLAN_ENV_SHA, PLAN_SOURCE_PATH, PLAN_SOURCE_SHA,
    PLAN_GIT_PATH, PLAN_GIT_SHA, PLAN_RUNTIME_SNAPSHOT_PATH,
    PLAN_RUNTIME_SNAPSHOT_SHA, PLAN_TOOL_PATH, PLAN_TOOL_SHA,
    PLAN_STAGE2_PATH, PLAN_STAGE2_SHA, PLAN_PLANNER_PATH, PLAN_PLANNER_SHA,
    PLAN_CGROUP_PATH, PLAN_CGROUP_SHA, PLAN_RAW_PATH, PLAN_MEMORY_PATH,
    PLAN_PHASE_PATH, PLAN_CACHE_PATH, PLAN_RUNTIME_PATH, PLAN_CANDIDATE_PATH,
    PLAN_OUTPUT_PATH, PLAN_STATUS, PLAN_KEY_COUNT
};

static const char *const plan_key_names[PLAN_KEY_COUNT] = {
    "schema", "run_id", "platform", "backend", "mode", "jobs", "threads",
    "no_stub_fallback", "streaming_surfaces", "unit_name", "memory_max_bytes",
    "memory_swap_max_bytes", "oom_policy", "sample_interval_ms", "max_gap_ms",
    "max_summed_rss_kib", "compiler_wall_ms", "transaction_wall_ms", "max_batches",
    "max_process_records", "max_tracked_per_batch", "max_raw_bytes",
    "closure_reserve_bytes", "closure_reserve_records", "term_grace_ms", "kill_reap_ms",
    "descriptor_path", "descriptor_sha256", "provenance_path", "provenance_sha256",
    "provenance_verify_receipt_path", "provenance_verify_receipt_sha256",
    "identity_manifest_path", "identity_manifest_sha256", "argv_transcript_path",
    "argv_transcript_sha256", "env_transcript_path", "env_transcript_sha256",
    "source_snapshot_path", "source_snapshot_sha256", "git_receipt_path",
    "git_receipt_sha256", "runtime_snapshot_path", "runtime_snapshot_sha256",
    "tool_snapshot_path", "tool_snapshot_sha256", "stage2_admission_path",
    "stage2_admission_sha256", "planner_receipt_path", "planner_receipt_sha256",
    "cgroup_preflight_receipt_path", "cgroup_preflight_receipt_sha256", "raw_path",
    "memory_path", "phase_path", "cache_path", "runtime_path", "candidate_output_path",
    "evidence_output_dir", "status",
};

typedef struct {
    char *value[PLAN_KEY_COUNT];
    char *decoded_path[PLAN_KEY_COUNT];
    InputStats input;
} LaunchPlan;

static void free_launch_plan(LaunchPlan *plan) {
    if (!plan) return;
    for (size_t i = 0; i < PLAN_KEY_COUNT; ++i) {
        free(plan->value[i]);
        free(plan->decoded_path[i]);
    }
    memset(plan, 0, sizeof(*plan));
}

static int plan_is_path_key(size_t key) {
    switch (key) {
    case PLAN_DESCRIPTOR_PATH: case PLAN_PROVENANCE_PATH: case PLAN_PROV_RECEIPT_PATH:
    case PLAN_IDENTITY_PATH: case PLAN_ARGV_PATH: case PLAN_ENV_PATH: case PLAN_SOURCE_PATH:
    case PLAN_GIT_PATH: case PLAN_RUNTIME_SNAPSHOT_PATH: case PLAN_TOOL_PATH:
    case PLAN_STAGE2_PATH: case PLAN_PLANNER_PATH: case PLAN_CGROUP_PATH: case PLAN_RAW_PATH:
    case PLAN_MEMORY_PATH: case PLAN_PHASE_PATH: case PLAN_CACHE_PATH: case PLAN_RUNTIME_PATH:
    case PLAN_CANDIDATE_PATH: case PLAN_OUTPUT_PATH: return 1;
    default: return 0;
    }
}

static int plan_is_hash_key(size_t key) {
    return key == PLAN_DESCRIPTOR_SHA || key == PLAN_PROVENANCE_SHA ||
           key == PLAN_PROV_RECEIPT_SHA || key == PLAN_IDENTITY_SHA ||
           key == PLAN_ARGV_SHA || key == PLAN_ENV_SHA || key == PLAN_SOURCE_SHA ||
           key == PLAN_GIT_SHA || key == PLAN_RUNTIME_SNAPSHOT_SHA || key == PLAN_TOOL_SHA ||
           key == PLAN_STAGE2_SHA || key == PLAN_PLANNER_SHA || key == PLAN_CGROUP_SHA;
}

static int parse_launch_plan_fd(int fd, const char *run_id, LaunchPlan *plan) {
    static const char *const fixed[PLAN_KEY_COUNT] = {
        [PLAN_SCHEMA]="simple-stage3-launch-plan-v1", [PLAN_PLATFORM]="x86_64-unknown-linux-gnu",
        [PLAN_BACKEND]="cranelift", [PLAN_MODE]="dynload", [PLAN_JOBS]="1",
        [PLAN_THREADS]="1", [PLAN_NO_STUB]="1", [PLAN_STREAMING]="1",
        [PLAN_MEMORY_MAX]="8589934592", [PLAN_SWAP_MAX]="0", [PLAN_OOM]="kill",
        [PLAN_INTERVAL]="5", [PLAN_MAX_GAP]="50", [PLAN_MAX_RSS]="8388608",
        [PLAN_COMPILER_WALL]="3600000", [PLAN_TRANSACTION_WALL]="3900000",
        [PLAN_MAX_BATCHES]="1000000", [PLAN_MAX_PROCESS_RECORDS]="16000000",
        [PLAN_MAX_TRACKED]="4096", [PLAN_MAX_RAW_BYTES]="1073741824",
        [PLAN_RESERVE_BYTES]="65536", [PLAN_RESERVE_RECORDS]="256",
        [PLAN_TERM_GRACE]="5000", [PLAN_KILL_REAP]="10000", [PLAN_STATUS]="ready",
    };
    memset(plan, 0, sizeof(*plan));
    uint64_t file_bytes;
    if (regular_file_size_cap(fd, METADATA_MAX_BYTES, &file_bytes) != 0) return -1;
    int stream_fd = dup(fd);
    if (stream_fd < 0 || lseek(stream_fd, 0, SEEK_SET) < 0) {
        if (stream_fd >= 0) close(stream_fd);
        return -1;
    }
    FILE *stream = fdopen(stream_fd, "r");
    if (!stream) { close(stream_fd); return -1; }
    char *line = NULL;
    size_t capacity = 0, index = 0;
    ssize_t length;
    int bad = 0;
    while ((length = getline(&line, &capacity, stream)) >= 0) {
        if (index >= PLAN_KEY_COUNT || length <= 1 ||
            (size_t)length > METADATA_MAX_RECORD_BYTES || line[length - 1] != '\n' ||
            memchr(line, 0, (size_t)length - 1)) { bad = 1; break; }
        plan->input.bytes += (uint64_t)length;
        plan->input.records++;
        line[length - 1] = 0;
        char *equals = strchr(line, '=');
        if (!equals || equals == line || !equals[1] || strchr(equals + 1, '=') ||
            (size_t)(equals - line) != strlen(plan_key_names[index]) ||
            strncmp(line, plan_key_names[index], (size_t)(equals - line))) { bad = 1; break; }
        plan->value[index] = strdup(equals + 1);
        if (!plan->value[index]) { bad = 1; break; }
        index++;
    }
    if (ferror(stream) || index != PLAN_KEY_COUNT || plan->input.bytes != file_bytes) bad = 1;
    free(line);
    if (fclose(stream) != 0) bad = 1;
    if (!bad) {
        for (size_t i = 0; i < PLAN_KEY_COUNT; ++i) {
            if (fixed[i] && strcmp(plan->value[i], fixed[i])) { bad = 1; break; }
            if (plan_is_hash_key(i) && !valid_sha256(plan->value[i])) { bad = 1; break; }
            if (plan_is_path_key(i)) {
                char decoded[DECODED_PATH_MAX + 1];
                if (canonical_path_token(plan->value[i], decoded, sizeof(decoded), 1)) {
                    bad = 1; break;
                }
                plan->decoded_path[i] = strdup(decoded);
                if (!plan->decoded_path[i]) { bad = 1; break; }
            } else if (!plan_is_hash_key(i) && !safe_token(plan->value[i])) {
                bad = 1; break;
            }
        }
        if (!bad && (strcmp(plan->value[PLAN_RUN_ID], run_id) ||
                     !safe_run_id(plan->value[PLAN_RUN_ID]) ||
                     !safe_token(plan->value[PLAN_UNIT_NAME]))) bad = 1;
    }
    if (bad) { free_launch_plan(plan); return -1; }
    return 0;
}

#define IDENTITY_ROLE_COUNT 15u
static const char *const identity_roles[IDENTITY_ROLE_COUNT] = {
    "admitted_compiler", "sampler", "analyzer", "transaction_supervisor",
    "shared_runner", "gate_helper", "dash", "perl", "session_helper",
    "bootstrap_script", "candidate_builder", "systemd_run", "systemctl", "planner",
    "provenance_verifier",
};

typedef struct {
    char *path;
    FileIdentity identity;
    int fd;
} IdentityRole;

typedef struct {
    IdentityRole role[IDENTITY_ROLE_COUNT];
    InputStats input;
} IdentitySummary;

static void free_identity_summary(IdentitySummary *summary) {
    if (!summary) return;
    for (size_t i = 0; i < IDENTITY_ROLE_COUNT; ++i) {
        if (summary->role[i].fd >= 0) close(summary->role[i].fd);
        free(summary->role[i].path);
    }
    memset(summary, 0, sizeof(*summary));
    for (size_t i = 0; i < IDENTITY_ROLE_COUNT; ++i) summary->role[i].fd = -1;
}

static int parse_identity_fd(int fd, const char *run_id, IdentitySummary *summary) {
    static const char *const keys[] = {
        "schema", "run_id", "seq", "event", "role", "path_kind", "path",
        "dev", "ino", "sha256", "outcome",
    };
    memset(summary, 0, sizeof(*summary));
    for (size_t i = 0; i < IDENTITY_ROLE_COUNT; ++i) summary->role[i].fd = -1;
    uint64_t file_bytes;
    if (regular_file_size_cap(fd, METADATA_MAX_BYTES, &file_bytes) != 0) return -1;
    int stream_fd = dup(fd);
    if (stream_fd < 0 || lseek(stream_fd, 0, SEEK_SET) < 0) {
        if (stream_fd >= 0) close(stream_fd);
        return -1;
    }
    FILE *stream = fdopen(stream_fd, "r");
    if (!stream) { close(stream_fd); return -1; }
    char *line = NULL;
    size_t capacity = 0;
    ssize_t length;
    uint64_t expected_seq = 0;
    int bad = 0;
    while ((length = getline(&line, &capacity, stream)) >= 0) {
        if (length <= 1 || (size_t)length > METADATA_MAX_RECORD_BYTES ||
            line[length - 1] != '\n' || memchr(line, 0, (size_t)length - 1) ||
            summary->input.records >= 2 + IDENTITY_ROLE_COUNT) { bad = 1; break; }
        summary->input.bytes += (uint64_t)length;
        summary->input.records++;
        line[length - 1] = 0;
        char *value[sizeof(keys)/sizeof(keys[0])] = {0};
        uint64_t seq, dev, ino;
        if (parse_ordered_row(line, keys, sizeof(keys)/sizeof(keys[0]), value) ||
            strcmp(value[0], "simple-stage3-transitive-identity-manifest-v1") ||
            strcmp(value[1], run_id) || parse_u64(value[2], &seq) || seq != expected_seq++ ||
            parse_u64(value[7], &dev) || parse_u64(value[8], &ino)) { bad = 1; break; }
        if (seq == 0) {
            if (strcmp(value[3], "open") || strcmp(value[4], "-") ||
                strcmp(value[5], "none") || strcmp(value[6], "-") || dev || ino ||
                strcmp(value[9], "-") || strcmp(value[10], "running")) bad = 1;
            if (bad) break;
            continue;
        }
        if (seq >= 1 && seq <= IDENTITY_ROLE_COUNT) {
            size_t role = (size_t)seq - 1;
            char decoded[DECODED_PATH_MAX + 1];
            if (strcmp(value[3], "identity") || strcmp(value[4], identity_roles[role]) ||
                strcmp(value[5], "recorded") || canonical_path_token(value[6], decoded,
                    sizeof(decoded), 1) || !dev || !ino || !valid_sha256(value[9]) ||
                strcmp(value[10], "bound")) { bad = 1; break; }
            IdentityRole *entry = &summary->role[role];
            entry->path = strdup(decoded);
            entry->fd = entry->path
                ? open_identity_absolute(entry->path, DEFAULT_MAX_RAW_BYTES, &entry->identity) : -1;
            if (!entry->path || entry->fd < 0 || entry->identity.dev != dev ||
                entry->identity.ino != ino || strcmp(entry->identity.sha256, value[9])) {
                bad = 1; break;
            }
            continue;
        }
        if (seq == IDENTITY_ROLE_COUNT + 1) {
            if (strcmp(value[3], "terminal") || strcmp(value[4], "-") ||
                strcmp(value[5], "none") || strcmp(value[6], "-") || dev || ino ||
                strcmp(value[9], "-") || strcmp(value[10], "complete")) bad = 1;
            if (bad) break;
            continue;
        }
        bad = 1;
        break;
    }
    if (ferror(stream) || summary->input.bytes != file_bytes ||
        summary->input.records != IDENTITY_ROLE_COUNT + 2) bad = 1;
    free(line);
    if (fclose(stream) != 0) bad = 1;
    if (bad) { free_identity_summary(summary); return -1; }
    return 0;
}

enum ProvenanceKey {
    PROV_SCHEMA, PROV_RUN_ID, PROV_PROVENANCE_SHA, PROV_CANDIDATE_SHA,
    PROV_SOURCE_SHA, PROV_RUNTIME_SHA, PROV_TOOL_SHA, PROV_GIT_SHA,
    PROV_VERIFIER_SHA, PROV_STATUS, PROV_KEY_COUNT
};

static const char *const provenance_key_names[PROV_KEY_COUNT] = {
    "schema", "run_id", "provenance_sha256", "candidate_sha256",
    "source_snapshot_sha256", "runtime_snapshot_sha256", "tool_snapshot_sha256",
    "git_receipt_sha256", "verifier_sha256", "status",
};

typedef struct {
    char *value[PROV_KEY_COUNT];
    InputStats input;
} ProvenanceReceipt;

static void free_provenance_receipt(ProvenanceReceipt *receipt) {
    if (!receipt) return;
    for (size_t i = 0; i < PROV_KEY_COUNT; ++i) free(receipt->value[i]);
    memset(receipt, 0, sizeof(*receipt));
}

static int parse_provenance_receipt_fd(int fd, const char *run_id,
                                       ProvenanceReceipt *receipt) {
    memset(receipt, 0, sizeof(*receipt));
    uint64_t file_bytes;
    if (regular_file_size_cap(fd, METADATA_MAX_BYTES, &file_bytes) != 0) return -1;
    int stream_fd = dup(fd);
    if (stream_fd < 0 || lseek(stream_fd, 0, SEEK_SET) < 0) {
        if (stream_fd >= 0) close(stream_fd);
        return -1;
    }
    FILE *stream = fdopen(stream_fd, "r");
    if (!stream) { close(stream_fd); return -1; }
    char *line = NULL;
    size_t capacity = 0, index = 0;
    ssize_t length;
    int bad = 0;
    while ((length = getline(&line, &capacity, stream)) >= 0) {
        if (index >= PROV_KEY_COUNT || length <= 1 ||
            (size_t)length > METADATA_MAX_RECORD_BYTES || line[length - 1] != '\n' ||
            memchr(line, 0, (size_t)length - 1)) { bad = 1; break; }
        receipt->input.bytes += (uint64_t)length;
        receipt->input.records++;
        line[length - 1] = 0;
        char *equals = strchr(line, '=');
        if (!equals || equals == line || !equals[1] || strchr(equals + 1, '=') ||
            (size_t)(equals - line) != strlen(provenance_key_names[index]) ||
            strncmp(line, provenance_key_names[index], (size_t)(equals - line))) {
            bad = 1; break;
        }
        receipt->value[index] = strdup(equals + 1);
        if (!receipt->value[index]) { bad = 1; break; }
        index++;
    }
    if (ferror(stream) || index != PROV_KEY_COUNT || receipt->input.bytes != file_bytes ||
        strcmp(receipt->value[PROV_SCHEMA], "simple-stage3-provenance-verification-v1") ||
        strcmp(receipt->value[PROV_RUN_ID], run_id) || strcmp(receipt->value[PROV_STATUS], "pass"))
        bad = 1;
    for (size_t i = PROV_PROVENANCE_SHA; !bad && i <= PROV_VERIFIER_SHA; ++i)
        if (!valid_sha256(receipt->value[i])) bad = 1;
    free(line);
    if (fclose(stream) != 0) bad = 1;
    if (bad) { free_provenance_receipt(receipt); return -1; }
    return 0;
}

static int parse_argv_transcript_fd(int fd, const char *run_id, const char *raw_argv_hex,
                                    char semantic_sha256[65], InputStats *input) {
    static const char *const keys[] = {
        "schema", "run_id", "seq", "event", "argc", "arg_index",
        "arg_kind", "arg", "outcome",
    };
    memset(input, 0, sizeof(*input));
    uint64_t file_bytes;
    if (regular_file_size_cap(fd, METADATA_MAX_BYTES, &file_bytes) != 0) return -1;
    int stream_fd = dup(fd);
    if (stream_fd < 0 || lseek(stream_fd, 0, SEEK_SET) < 0) {
        if (stream_fd >= 0) close(stream_fd);
        return -1;
    }
    FILE *stream = fdopen(stream_fd, "r");
    if (!stream) { close(stream_fd); return -1; }
    unsigned char reconstructed[MAX_ARGV_BYTES];
    size_t reconstructed_bytes = 0;
    char *line = NULL;
    size_t capacity = 0;
    ssize_t length;
    uint64_t expected_seq = 0, argc = 0, args = 0;
    int saw_open = 0, saw_terminal = 0, bad = 0;
    Sha256 semantic;
    sha256_init(&semantic);
    while ((length = getline(&line, &capacity, stream)) >= 0) {
        if (length <= 1 || (size_t)length > METADATA_MAX_RECORD_BYTES ||
            line[length-1] != '\n' || memchr(line,0,(size_t)length-1) ||
            input->records >= METADATA_MAX_RECORDS) { bad=1; break; }
        input->bytes += (uint64_t)length;
        input->records++;
        line[length-1]=0;
        char *value[sizeof(keys)/sizeof(keys[0])] = {0};
        uint64_t seq, row_argc;
        int64_t index;
        if (parse_ordered_row(line,keys,sizeof(keys)/sizeof(keys[0]),value) ||
            strcmp(value[0],"simple-stage3-argv-transcript-v1") ||
            strcmp(value[1],run_id) || parse_u64(value[2],&seq) || seq!=expected_seq++ ||
            parse_u64(value[4],&row_argc) || parse_source_index(value[5],&index)) {
            bad=1; break;
        }
        if (!strcmp(value[3],"open")) {
            if (saw_open || seq || !row_argc || row_argc > METADATA_MAX_RECORDS-2 ||
                index!=-1 || strcmp(value[6],"none") || strcmp(value[7],"-") ||
                strcmp(value[8],"running")) { bad=1; break; }
            argc=row_argc; saw_open=1; continue;
        }
        if (!saw_open || saw_terminal || row_argc!=argc) { bad=1; break; }
        if (!strcmp(value[3],"arg")) {
            if (args>=argc || index<0 || (uint64_t)index!=args ||
                strcmp(value[6],"recorded") || strcmp(value[8],"bound")) { bad=1; break; }
            char decoded[MAX_ARGV_BYTES+1];
            if (canonical_token(value[7],decoded,sizeof(decoded),1)) { bad=1; break; }
            size_t n=strlen(decoded);
            if (!n || n+1>MAX_ARGV_BYTES-reconstructed_bytes) { bad=1; break; }
            memcpy(reconstructed+reconstructed_bytes,decoded,n);
            reconstructed[reconstructed_bytes+n]=0;
            reconstructed_bytes+=n+1;
            sha256_u64be(&semantic,n);
            sha256_update(&semantic,decoded,n);
            args++;
            continue;
        }
        if (!strcmp(value[3],"terminal")) {
            if (++saw_terminal!=1 || args!=argc || index!=-1 ||
                strcmp(value[6],"none") || strcmp(value[7],"-") ||
                strcmp(value[8],"complete")) { bad=1; break; }
            continue;
        }
        bad=1; break;
    }
    if (ferror(stream) || input->bytes!=file_bytes || !saw_open || saw_terminal!=1 || args!=argc)
        bad=1;
    free(line);
    if (fclose(stream)!=0) bad=1;
    char *encoded = bad ? NULL : hex_encode(reconstructed,reconstructed_bytes);
    if (!encoded || strcmp(encoded,raw_argv_hex)) bad=1;
    free(encoded);
    if (!bad) sha256_hex_finish(&semantic,semantic_sha256);
    return bad ? -1 : 0;
}

static int parse_environment_transcript_fd(int fd, const char *run_id,
                                           const char *raw_environment_sha256,
                                           const LaunchPlan *plan,
                                           const char *admitted_compiler_path,
                                           char semantic_sha256[65], InputStats *input) {
    static const char *const keys[] = {
        "schema", "run_id", "seq", "event", "count", "key_kind", "key",
        "value_kind", "value", "outcome",
    };
    char *values[27] = {0};
    memset(input,0,sizeof(*input));
    uint64_t file_bytes;
    if (regular_file_size_cap(fd,METADATA_MAX_BYTES,&file_bytes)!=0) return -1;
    int stream_fd=dup(fd);
    if (stream_fd<0 || lseek(stream_fd,0,SEEK_SET)<0) {
        if(stream_fd>=0)close(stream_fd);
        return -1;
    }
    FILE *stream=fdopen(stream_fd,"r");
    if(!stream){close(stream_fd);return -1;}
    char *line=NULL;
    size_t capacity=0;
    ssize_t length;
    uint64_t expected_seq=0,rows=0;
    int saw_open=0,saw_terminal=0,bad=0;
    Sha256 semantic;
    sha256_init(&semantic);
    while((length=getline(&line,&capacity,stream))>=0){
        if(length<=1 || (size_t)length>METADATA_MAX_RECORD_BYTES || line[length-1]!='\n' ||
           memchr(line,0,(size_t)length-1) || input->records>=METADATA_MAX_RECORDS){bad=1;break;}
        input->bytes+=(uint64_t)length; input->records++; line[length-1]=0;
        char *value[sizeof(keys)/sizeof(keys[0])]={0};
        uint64_t seq,count;
        if(parse_ordered_row(line,keys,sizeof(keys)/sizeof(keys[0]),value) ||
           strcmp(value[0],"simple-stage3-environment-transcript-v1") ||
           strcmp(value[1],run_id) || parse_u64(value[2],&seq) || seq!=expected_seq++ ||
           parse_u64(value[4],&count) || count!=27){bad=1;break;}
        if(!strcmp(value[3],"open")){
            if(saw_open || seq || strcmp(value[5],"none") || strcmp(value[6],"-") ||
               strcmp(value[7],"none") || strcmp(value[8],"-") ||
               strcmp(value[9],"running")){bad=1;break;}
            saw_open=1;continue;
        }
        if(!saw_open || saw_terminal){bad=1;break;}
        if(!strcmp(value[3],"env")){
            if(rows>=27 || strcmp(value[5],"recorded") ||
               strcmp(value[6],environment_keys[rows]) || !safe_token(value[6]) ||
               strcmp(value[9],"bound")){bad=1;break;}
            char decoded[METADATA_MAX_RECORD_BYTES+1];
            if (rows == 6) {
                if (strcmp(value[7],"empty") || strcmp(value[8],"-")) { bad=1; break; }
                decoded[0]=0;
            } else if(strcmp(value[7],"recorded") ||
                      canonical_token(value[8],decoded,sizeof(decoded),1) || !*decoded){bad=1;break;}
            values[rows]=strdup(decoded);
            if(!values[rows]){bad=1;break;}
            sha256_u64be(&semantic,strlen(environment_keys[rows]));
            sha256_update(&semantic,environment_keys[rows],strlen(environment_keys[rows]));
            sha256_u64be(&semantic,strlen(decoded));
            sha256_update(&semantic,decoded,strlen(decoded));
            rows++;continue;
        }
        if(!strcmp(value[3],"terminal")){
            if(++saw_terminal!=1 || rows!=27 || strcmp(value[5],"none") ||
               strcmp(value[6],"-") || strcmp(value[7],"none") ||
               strcmp(value[8],"-") || strcmp(value[9],"complete")){bad=1;break;}
            continue;
        }
        bad=1;break;
    }
    if(ferror(stream) || input->bytes!=file_bytes || !saw_open || saw_terminal!=1 || rows!=27)
        bad=1;
    free(line);
    if(fclose(stream)!=0)bad=1;
    if(!bad){
        sha256_hex_finish(&semantic,semantic_sha256);
        if(strcmp(semantic_sha256,raw_environment_sha256) ||
           strcmp(values[3],"C") || strcmp(values[4],"C") ||
           strcmp(values[6],"") ||
           !normalized_absolute_path(values[0]) || !normalized_absolute_path(values[1]) ||
           !absolute_path_list(values[2]) || strcmp(values[10],plan->value[PLAN_STREAMING]) ||
           strcmp(values[14],plan->value[PLAN_NO_STUB]) ||
           strcmp(values[17],plan->decoded_path[PLAN_PHASE_PATH]) ||
           strcmp(values[18],plan->decoded_path[PLAN_MEMORY_PATH]) ||
           strcmp(values[19],run_id) || strcmp(values[21],plan->value[PLAN_PLATFORM]) ||
           strcmp(values[22],plan->value[PLAN_THREADS]) ||
           strcmp(values[23],plan->decoded_path[PLAN_CACHE_PATH]) ||
           strcmp(values[24],plan->decoded_path[PLAN_RUNTIME_PATH]) ||
           strcmp(values[26],admitted_compiler_path)) bad=1;
    }
    for(size_t i=0;i<27;++i)free(values[i]);
    return bad ? -1 : 0;
}

typedef struct {
    int64_t source_index;
    char *source_path;
    uint64_t time_ms[4], rss_kib[4], heap_live[4];
} MemorySource;

typedef struct {
    uint64_t first_ms, last_ms, rows, bytes;
    MemorySource *sources;
    size_t source_count;
} MemorySummary;

static int aux_nonnegative_scalars(const AuxRecord *record) {
    const enum AuxKey keys[] = {
        AK_RETAINED, AK_VALIDATION_KEYS, AK_VALIDATION_VALUES, AK_SHARED_TRAITS,
        AK_HIR_NAMES, AK_HIR_SYMBOLS, AK_HIR_FUNCTIONS, AK_HIR_CONSTANTS,
        AK_HIR_ENUMS, AK_HIR_STRUCTS, AK_HIR_CLASSES, AK_HEAP_LIVE,
        AK_HEAP_PEAK, AK_RSS, AK_HWM,
    };
    for (size_t i = 0; i < sizeof(keys)/sizeof(keys[0]); ++i) {
        uint64_t ignored;
        if (parse_u64(record->value[keys[i]], &ignored)) return -1;
    }
    uint64_t live, peak, rss, hwm;
    return parse_u64(record->value[AK_HEAP_LIVE], &live) ||
           parse_u64(record->value[AK_HEAP_PEAK], &peak) || peak < live ||
           parse_u64(record->value[AK_RSS], &rss) ||
           parse_u64(record->value[AK_HWM], &hwm) || hwm < rss ? -1 : 0;
}

static int aux_zero_semantic_counters(const AuxRecord *record) {
    for (int key = AK_RETAINED; key <= AK_HIR_CLASSES; ++key)
        if (strcmp(record->value[key], "0")) return -1;
    return 0;
}

static int memory_phase_index(const char *phase) {
    static const char *const phases[4] = {
        "hir-file-start", "hir-post-lowering", "hir-post-diagnostics", "hir-post-store",
    };
    for (int i = 0; i < 4; ++i) if (!strcmp(phase, phases[i])) return i;
    return -1;
}

static void free_memory_summary(MemorySummary *summary) {
    if (!summary || !summary->sources) return;
    for (size_t i = 0; i < summary->source_count; ++i) free(summary->sources[i].source_path);
    free(summary->sources);
    memset(summary, 0, sizeof(*summary));
}

static int parse_memory_fd(int fd, const char *run_id, pid_t root_pid,
                           const DescriptorSummary *descriptor, MemorySummary *summary) {
    memset(summary, 0, sizeof(*summary));
    if (!descriptor || !descriptor->source_count) return -1;
    uint64_t file_bytes;
    if (regular_file_size_cap(fd, COMPILER_STREAM_MAX_BYTES, &file_bytes) != 0) return -1;
    summary->sources = calloc(descriptor->source_count, sizeof(*summary->sources));
    if (!summary->sources) return -1;
    int stream_fd = dup(fd);
    if (stream_fd < 0 || lseek(stream_fd, 0, SEEK_SET) < 0) goto bad_fd;
    FILE *stream = fdopen(stream_fd, "r");
    if (!stream) goto bad_fd;
    char *line = NULL;
    size_t capacity = 0;
    ssize_t length;
    uint64_t expected_seq = 0;
    int open_count = 0, terminal_count = 0;
    int bad = 0;
    while ((length = getline(&line, &capacity, stream)) >= 0) {
        if (length <= 1 || (size_t)length > COMPILER_STREAM_MAX_RECORD_BYTES ||
            line[length-1] != '\n' || memchr(line, '\0', (size_t)length - 1) ||
            summary->rows >= COMPILER_STREAM_MAX_RECORDS) { bad = 1; break; }
        summary->bytes += (uint64_t)length;
        line[length-1] = 0;
        AuxRecord record;
        uint64_t seq, pid, ms;
        int64_t source_index;
        if (parse_aux_record(line, &record) ||
            strcmp(record.value[AK_SCHEMA], "simple.compiler.mem_snapshot.v1") ||
            strcmp(record.value[AK_RUN], run_id) || parse_u64(record.value[AK_SEQ], &seq) ||
            seq != expected_seq++ || parse_u64(record.value[AK_PID], &pid) ||
            pid != (uint64_t)root_pid || parse_u64(record.value[AK_MONO], &ms) || !ms ||
            (summary->last_ms && ms < summary->last_ms) ||
            parse_source_index(record.value[AK_SOURCE_INDEX], &source_index) ||
            aux_nonnegative_scalars(&record)) { bad = 1; break; }
        if (!summary->first_ms) summary->first_ms = ms;
        summary->last_ms = ms;
        summary->rows++;
        if (!strcmp(record.value[AK_EVENT], "open")) {
            if (seq != 0 || ++open_count != 1 || terminal_count || source_index != -1 ||
                strcmp(record.value[AK_PHASE], "hir") ||
                strcmp(record.value[AK_SOURCE_KIND], "none") ||
                strcmp(record.value[AK_SOURCE_PATH], "-") ||
                aux_zero_semantic_counters(&record)) {
                bad = 1; break;
            }
            continue;
        }
        if (!strcmp(record.value[AK_EVENT], "terminal")) {
            if (open_count != 1 || ++terminal_count != 1 || source_index != -1 ||
                strcmp(record.value[AK_PHASE], "hir-complete") ||
                strcmp(record.value[AK_SOURCE_KIND], "none") ||
                strcmp(record.value[AK_SOURCE_PATH], "-") ||
                aux_zero_semantic_counters(&record) ||
                summary->source_count != descriptor->source_count ||
                summary->rows - 1 > COMPILER_STREAM_MAX_RECORDS - COMPILER_STREAM_RESERVE_RECORDS ||
                summary->bytes - (uint64_t)length >
                    COMPILER_STREAM_MAX_BYTES - COMPILER_STREAM_RESERVE_BYTES) {
                bad = 1; break;
            }
            continue;
        }
        if (strcmp(record.value[AK_EVENT], "snapshot") || open_count != 1 || terminal_count ||
            source_index < 0 || strcmp(record.value[AK_SOURCE_KIND], "recorded")) { bad = 1; break; }
        int phase = memory_phase_index(record.value[AK_PHASE]);
        if (phase < 0 || (uint64_t)source_index >= descriptor->source_count) { bad = 1; break; }
        MemorySource *source;
        if ((uint64_t)source_index == summary->source_count) {
            if (summary->source_count >= descriptor->source_count || phase != 0) { bad = 1; break; }
            source = &summary->sources[summary->source_count++];
            source->source_index = source_index;
            char decoded_path[DECODED_PATH_MAX + 1];
            if (canonical_path_token(record.value[AK_SOURCE_PATH], decoded_path,
                                     sizeof(decoded_path), 1) ||
                strcmp(decoded_path, descriptor->sources[summary->source_count - 1].source_path)) {
                bad = 1; break;
            }
            source->source_path = strdup(decoded_path);
            if (!source->source_path) { bad = 1; break; }
        } else if (summary->source_count &&
                   source_index == summary->sources[summary->source_count-1].source_index)
            source = &summary->sources[summary->source_count-1];
        else { bad = 1; break; }
        char decoded_path[DECODED_PATH_MAX + 1];
        if (canonical_path_token(record.value[AK_SOURCE_PATH], decoded_path, sizeof(decoded_path), 1) ||
            !source->source_path || strcmp(source->source_path, decoded_path) ||
            (phase > 0 && !source->time_ms[phase-1]) || source->time_ms[phase]) { bad = 1; break; }
        uint64_t rss, heap;
        if (parse_u64(record.value[AK_RSS], &rss) || parse_u64(record.value[AK_HEAP_LIVE], &heap)) {
            bad = 1; break;
        }
        source->time_ms[phase] = ms;
        source->rss_kib[phase] = rss;
        source->heap_live[phase] = heap;
    }
    if (ferror(stream) || summary->bytes != file_bytes) bad = 1;
    free(line);
    fclose(stream);
    if (open_count != 1 || terminal_count != 1 ||
        summary->source_count != descriptor->source_count) bad = 1;
    for (size_t i = 0; i < summary->source_count; ++i)
        for (int phase = 0; phase < 4; ++phase)
            if (!summary->sources[i].time_ms[phase]) bad = 1;
    if (bad) { free_memory_summary(summary); return -1; }
    return 0;
bad_fd:
    if (stream_fd >= 0) close(stream_fd);
    free_memory_summary(summary);
    return -1;
}

enum PhaseKey {
    PK_SCHEMA, PK_RUN, PK_SEQ, PK_PID, PK_MONO, PK_MODE, PK_EVENT,
    PK_PHYSICAL_INDEX, PK_SOURCE_KIND, PK_SOURCE_PATH, PK_MODULE_KIND,
    PK_MODULE, PK_OUTCOME, PK_DETAIL, PK_COUNT
};

static const char *const phase_key_names[PK_COUNT] = {
    "schema", "run_id", "seq", "pid", "monotonic_ms", "mode", "event",
    "physical_index", "source_path_kind", "source_path", "module_kind",
    "module", "outcome", "detail",
};

typedef struct {
    char *value[PK_COUNT];
    uint16_t mask;
} PhaseRecord;

static int parse_phase_record(char *line, PhaseRecord *record) {
    memset(record, 0, sizeof(*record));
    if (parse_ordered_row(line, phase_key_names, PK_COUNT, record->value)) return -1;
    record->mask = (UINT16_C(1) << PK_COUNT) - 1;
    return 0;
}

typedef struct {
    int64_t source_index;
    char *source_path;
    char *module;
    uint64_t hir_start_ms, hir_release_ms, hir_done_ms;
    unsigned stage;
} PhaseSource;

typedef struct {
    uint64_t first_ms, last_ms, rows, bytes;
    int streaming;
    PhaseSource *sources;
    size_t source_count;
} PhaseSummary;

static void free_phase_summary(PhaseSummary *summary) {
    if (!summary || !summary->sources) return;
    for (size_t i = 0; i < summary->source_count; ++i) {
        free(summary->sources[i].source_path);
        free(summary->sources[i].module);
    }
    free(summary->sources);
    memset(summary, 0, sizeof(*summary));
}

static int phase_none_fields(const PhaseRecord *record) {
    int64_t index;
    return parse_source_index(record->value[PK_PHYSICAL_INDEX], &index) == 0 && index == -1 &&
           !strcmp(record->value[PK_SOURCE_KIND], "none") &&
           !strcmp(record->value[PK_SOURCE_PATH], "-") &&
           !strcmp(record->value[PK_MODULE_KIND], "none") &&
           !strcmp(record->value[PK_MODULE], "-");
}

static int expected_stream_event(unsigned stage, const char **event,
                                 const char **outcome, const char **detail) {
    static const char *const events[6] = {
        "surface-start", "surface-done", "surface-release", "hir-start",
        "hir-transient-scope-release", "hir-done",
    };
    static const char *const outcomes[6] = {
        "attempting", "retained", "released", "attempting", "attempt-complete", "stored",
    };
    static const char *const details[6] = { "-", "-", "scope-end-1", "-", "scope-end-1", "-" };
    if (stage >= 6) return -1;
    *event = events[stage]; *outcome = outcomes[stage]; *detail = details[stage];
    return 0;
}

static int expected_nonstream_event(unsigned stage, const char **event,
                                    const char **outcome, const char **detail) {
    if (stage == 0) { *event="hir-start"; *outcome="attempting"; *detail="-"; return 0; }
    if (stage == 1) { *event="hir-done"; *outcome="stored"; *detail="-"; return 0; }
    return -1;
}

static int parse_phase_fd(int fd, const char *run_id, pid_t root_pid,
                          const DescriptorSummary *descriptor, PhaseSummary *summary) {
    memset(summary, 0, sizeof(*summary));
    if (!descriptor || !descriptor->source_count) return -1;
    uint64_t file_bytes;
    if (regular_file_size_cap(fd, COMPILER_STREAM_MAX_BYTES, &file_bytes) != 0) return -1;
    summary->sources = calloc(descriptor->source_count, sizeof(*summary->sources));
    if (!summary->sources) return -1;
    int stream_fd = dup(fd);
    if (stream_fd < 0 || lseek(stream_fd, 0, SEEK_SET) < 0) goto bad_fd;
    FILE *stream = fdopen(stream_fd, "r");
    if (!stream) goto bad_fd;
    char *line = NULL;
    size_t capacity = 0;
    ssize_t length;
    uint64_t expected_seq = 0;
    int open_count = 0, terminal_count = 0, bad = 0;
    size_t descriptors_seen = 0, surface_source = 0, hir_source = 0;
    unsigned surface_stage = 0, hir_stage = 0;
    char frozen_mode[16] = "";
    while ((length = getline(&line, &capacity, stream)) >= 0) {
        if (length <= 1 || (size_t)length > COMPILER_STREAM_MAX_RECORD_BYTES ||
            line[length-1] != '\n' || memchr(line, '\0', (size_t)length - 1) ||
            summary->rows >= COMPILER_STREAM_MAX_RECORDS) { bad = 1; break; }
        summary->bytes += (uint64_t)length;
        line[length-1] = 0;
        PhaseRecord record;
        uint64_t seq, pid, ms;
        int64_t source_index;
        if (parse_phase_record(line, &record) ||
            strcmp(record.value[PK_SCHEMA], "simple.compiler.phase_profile.v2") ||
            strcmp(record.value[PK_RUN], run_id) ||
            (strcmp(record.value[PK_MODE], "streaming") && strcmp(record.value[PK_MODE], "nonstreaming")) ||
            parse_u64(record.value[PK_SEQ], &seq) || seq != expected_seq++ ||
            parse_u64(record.value[PK_PID], &pid) || pid != (uint64_t)root_pid ||
            parse_u64(record.value[PK_MONO], &ms) || !ms ||
            (summary->last_ms && ms < summary->last_ms) ||
            parse_source_index(record.value[PK_PHYSICAL_INDEX], &source_index)) { bad = 1; break; }
        if (!*frozen_mode) strcpy(frozen_mode, record.value[PK_MODE]);
        else if (strcmp(frozen_mode, record.value[PK_MODE])) { bad = 1; break; }
        if (!summary->first_ms) summary->first_ms = ms;
        summary->last_ms = ms;
        summary->rows++;
        if (!strcmp(record.value[PK_EVENT], "open")) {
            if (seq || ++open_count != 1 || terminal_count || !phase_none_fields(&record) ||
                strcmp(record.value[PK_OUTCOME], "running") || strcmp(record.value[PK_DETAIL], "-")) {
                bad = 1; break;
            }
            summary->streaming = !strcmp(frozen_mode, "streaming");
            continue;
        }
        if (open_count != 1 || terminal_count) { bad = 1; break; }
        if (!strcmp(record.value[PK_EVENT], "phase")) {
            char detail[DECODED_DETAIL_MAX + 1];
            if (!phase_none_fields(&record) || strcmp(record.value[PK_OUTCOME], "observed") ||
                !strcmp(record.value[PK_DETAIL], "-") ||
                canonical_token(record.value[PK_DETAIL], detail, sizeof(detail), 1)) { bad = 1; break; }
            continue;
        }
        if (!strcmp(record.value[PK_EVENT], "terminal")) {
            if (++terminal_count != 1 || !phase_none_fields(&record) ||
                strcmp(record.value[PK_OUTCOME], "hir-complete") ||
                strcmp(record.value[PK_DETAIL], "-") ||
                descriptors_seen != descriptor->source_count ||
                (summary->streaming && surface_source != descriptor->source_count) ||
                hir_source != descriptor->source_count ||
                summary->rows - 1 > COMPILER_STREAM_MAX_RECORDS - COMPILER_STREAM_RESERVE_RECORDS ||
                summary->bytes - (uint64_t)length >
                    COMPILER_STREAM_MAX_BYTES - COMPILER_STREAM_RESERVE_BYTES) {
                bad = 1; break;
            }
            continue;
        }
        if (!strcmp(record.value[PK_EVENT], "physical-descriptor")) {
            if (source_index < 0 || (uint64_t)source_index != descriptors_seen ||
                descriptors_seen >= descriptor->source_count || surface_source || hir_source ||
                strcmp(record.value[PK_SOURCE_KIND], "recorded") ||
                strcmp(record.value[PK_MODULE_KIND], "recorded") ||
                strcmp(record.value[PK_OUTCOME], "bound") || strcmp(record.value[PK_DETAIL], "-")) {
                bad = 1; break;
            }
            char decoded_path[DECODED_PATH_MAX + 1], decoded_module[DECODED_MODULE_MAX + 1];
            if (canonical_path_token(record.value[PK_SOURCE_PATH], decoded_path,
                                     sizeof(decoded_path), 1) ||
                canonical_token(record.value[PK_MODULE], decoded_module, sizeof(decoded_module), 1) ||
                !*decoded_module || strcmp(decoded_path, descriptor->sources[descriptors_seen].source_path) ||
                strcmp(decoded_module, descriptor->sources[descriptors_seen].module)) {
                bad = 1; break;
            }
            PhaseSource *phase_source = &summary->sources[descriptors_seen++];
            phase_source->source_index = source_index;
            phase_source->source_path = strdup(decoded_path);
            phase_source->module = strdup(decoded_module);
            if (!phase_source->source_path || !phase_source->module) { bad = 1; break; }
            summary->source_count = descriptors_seen;
            continue;
        }
        if (source_index < 0 ||
            strcmp(record.value[PK_SOURCE_KIND], "recorded") ||
            strcmp(record.value[PK_MODULE_KIND], "recorded")) { bad = 1; break; }
        char decoded_path[DECODED_PATH_MAX + 1], decoded_module[DECODED_MODULE_MAX + 1];
        if (canonical_path_token(record.value[PK_SOURCE_PATH], decoded_path,
                                 sizeof(decoded_path), 1) ||
            canonical_token(record.value[PK_MODULE], decoded_module, sizeof(decoded_module), 1) ||
            !*decoded_module) {
            bad = 1; break;
        }
        if (descriptors_seen != descriptor->source_count) { bad = 1; break; }
        size_t expected_source;
        unsigned expected_stage;
        if (summary->streaming && !strncmp(record.value[PK_EVENT], "surface-", 8)) {
            if (surface_source >= descriptor->source_count || hir_source) { bad = 1; break; }
            expected_source = surface_source;
            expected_stage = surface_stage;
        } else {
            if ((summary->streaming && surface_source != descriptor->source_count) ||
                hir_source >= descriptor->source_count) { bad = 1; break; }
            expected_source = hir_source;
            expected_stage = summary->streaming ? 3u + hir_stage : hir_stage;
        }
        PhaseSource *source = &summary->sources[expected_source];
        if (source->source_index != source_index) { bad = 1; break; }
        if (strcmp(source->source_path, decoded_path) || strcmp(source->module, decoded_module)) {
            bad = 1; break;
        }
        const char *event, *outcome, *detail;
        int expected = summary->streaming
            ? expected_stream_event(expected_stage, &event, &outcome, &detail)
            : expected_nonstream_event(expected_stage, &event, &outcome, &detail);
        if (expected || strcmp(record.value[PK_EVENT], event) ||
            strcmp(record.value[PK_OUTCOME], outcome) || strcmp(record.value[PK_DETAIL], detail)) {
            bad = 1; break;
        }
        if (!strcmp(event, "hir-start")) source->hir_start_ms = ms;
        else if (!strcmp(event, "hir-transient-scope-release")) source->hir_release_ms = ms;
        else if (!strcmp(event, "hir-done")) source->hir_done_ms = ms;
        source->stage++;
        if (summary->streaming && expected_stage < 3) {
            if (++surface_stage == 3) { surface_stage = 0; surface_source++; }
        } else {
            unsigned limit = summary->streaming ? 3u : 2u;
            if (++hir_stage == limit) { hir_stage = 0; hir_source++; }
        }
    }
    if (ferror(stream) || summary->bytes != file_bytes) bad = 1;
    free(line);
    fclose(stream);
    if (open_count != 1 || terminal_count != 1 ||
        summary->source_count != descriptor->source_count) bad = 1;
    unsigned expected_stages = summary->streaming ? 6 : 2;
    for (size_t i = 0; i < summary->source_count; ++i)
        if (summary->sources[i].stage != expected_stages || !summary->sources[i].hir_start_ms ||
            !summary->sources[i].hir_done_ms ||
            (summary->streaming && !summary->sources[i].hir_release_ms)) bad = 1;
    if (bad) { free_phase_summary(summary); return -1; }
    return 0;
bad_fd:
    if (stream_fd >= 0) close(stream_fd);
    free_phase_summary(summary);
    return -1;
}

static int correlate_streams(const RawSummary *raw, const MemorySummary *memory,
                             const PhaseSummary *phase) {
    const uint64_t tolerance_ms = 5;
    uint64_t raw_lo = raw->first_sample_ns / UINT64_C(1000000);
    uint64_t raw_hi = raw->terminal_ns / UINT64_C(1000000);
    uint64_t lower = raw_lo > tolerance_ms ? raw_lo - tolerance_ms : 0;
    uint64_t upper = raw_hi > UINT64_MAX - tolerance_ms ? UINT64_MAX : raw_hi + tolerance_ms;
    if (memory->first_ms < lower || memory->last_ms > upper ||
        phase->first_ms < lower || phase->last_ms > upper ||
        memory->source_count != phase->source_count) return -1;
    for (size_t i = 0; i < memory->source_count; ++i) {
        const MemorySource *mem = &memory->sources[i];
        const PhaseSource *ph = &phase->sources[i];
        if (mem->source_index != ph->source_index || strcmp(mem->source_path, ph->source_path) ||
            ph->hir_start_ms > mem->time_ms[0] || mem->time_ms[3] > ph->hir_done_ms ||
            (phase->streaming && ph->hir_release_ms > mem->time_ms[1]))
            return -1;
    }
    return 0;
}

static int stable_identity_fd(int fd, const FileIdentity *before) {
    FileIdentity after;
    return identity_fd(fd, &after) == 0 && after.dev == before->dev && after.ino == before->ino &&
           !strcmp(after.sha256, before->sha256);
}

static int put_text_file_at(int dirfd, const char *name, const char *text) {
    int fd = openat(dirfd, name, O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW|O_CLOEXEC, 0600);
    if (fd < 0) return -1;
    size_t size = strlen(text), offset = 0;
    while (offset < size) {
        ssize_t n = write(fd, text + offset, size - offset);
        if (n < 0) { if (errno == EINTR) continue; close(fd); return -1; }
        if (!n) { close(fd); errno = EIO; return -1; }
        offset += (size_t)n;
    }
    int result = fsync(fd);
    if (close(fd) != 0) result = -1;
    return result;
}

static int derived_preflight(const MemorySummary *memory) {
    uint64_t boundary_bytes = 96, delta_bytes = 112;
    uint64_t boundary_records = 1, delta_records = 1;
    for (size_t i = 0; i < memory->source_count; ++i) {
        uint64_t path = strlen(memory->sources[i].source_path);
        uint64_t boundary_add = 4 * (path + 256);
        uint64_t delta_add = 3 * (path + 320);
        if (UINT64_MAX - boundary_bytes < boundary_add ||
            UINT64_MAX - delta_bytes < delta_add) return -1;
        boundary_bytes += boundary_add;
        delta_bytes += delta_add;
        boundary_records += 4;
        delta_records += 3;
    }
    return boundary_bytes <= DERIVED_MAX_FILE_BYTES && delta_bytes <= DERIVED_MAX_FILE_BYTES &&
           boundary_bytes + delta_bytes <= DERIVED_MAX_TOTAL_BYTES &&
           boundary_records + delta_records + 3 <= DERIVED_MAX_RECORDS ? 0 : -1;
}

static int write_boundary_file(int dirfd, const MemorySummary *memory) {
    int fd = openat(dirfd, "boundary.tsv", O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW|O_CLOEXEC, 0600);
    if (fd < 0) return -1;
    FILE *out = fdopen(fd, "w");
    if (!out) { close(fd); return -1; }
    static const char *const phases[4] = {
        "hir-file-start", "hir-post-lowering", "hir-post-diagnostics", "hir-post-store",
    };
    int failed = fprintf(out, "source_index\tsource_path\tphase\tmonotonic_ms\trss_kib\theap_live_bytes\n") < 0;
    for (size_t i = 0; !failed && i < memory->source_count; ++i) {
        for (int p = 0; p < 4; ++p) {
            if (fprintf(out, "%" PRId64 "\t%s\t%s\t%" PRIu64 "\t%" PRIu64 "\t%" PRIu64 "\n",
                        memory->sources[i].source_index, memory->sources[i].source_path,
                        phases[p], memory->sources[i].time_ms[p], memory->sources[i].rss_kib[p],
                        memory->sources[i].heap_live[p]) < 0) { failed = 1; break; }
        }
    }
    if (fflush(out) != 0 || fsync(fd) != 0) failed = 1;
    if (fclose(out) != 0) failed = 1;
    return failed ? -1 : 0;
}

static int write_delta_file(int dirfd, const MemorySummary *memory) {
    int fd = openat(dirfd, "delta.tsv", O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW|O_CLOEXEC, 0600);
    if (fd < 0) return -1;
    FILE *out = fdopen(fd, "w");
    if (!out) { close(fd); return -1; }
    int failed = fprintf(out, "source_index\tsource_path\tfrom_phase\tto_phase\tdelta_ms\tdelta_rss_kib\tdelta_heap_live_bytes\n") < 0;
    static const char *const phases[4] = {
        "hir-file-start", "hir-post-lowering", "hir-post-diagnostics", "hir-post-store",
    };
    for (size_t i = 0; !failed && i < memory->source_count; ++i) {
        for (int p = 1; p < 4; ++p) {
            int64_t rss_delta = (int64_t)memory->sources[i].rss_kib[p] - (int64_t)memory->sources[i].rss_kib[p-1];
            int64_t heap_delta = (int64_t)memory->sources[i].heap_live[p] - (int64_t)memory->sources[i].heap_live[p-1];
            if (fprintf(out, "%" PRId64 "\t%s\t%s\t%s\t%" PRIu64 "\t%" PRId64 "\t%" PRId64 "\n",
                        memory->sources[i].source_index, memory->sources[i].source_path,
                        phases[p-1], phases[p], memory->sources[i].time_ms[p]-memory->sources[i].time_ms[p-1],
                        rss_delta, heap_delta) < 0) { failed = 1; break; }
        }
    }
    if (fflush(out) != 0 || fsync(fd) != 0) failed = 1;
    if (fclose(out) != 0) failed = 1;
    return failed ? -1 : 0;
}

static int discard_output_dir(int parent, const char *leaf) {
    int failed = 0;
    int dir = openat(parent, leaf, O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);
    if (dir >= 0) {
        const char *const files[] = {
            ".receipt.pending", ".receipt.invalid", "receipt.env",
            "summary.env", "delta.tsv", "boundary.tsv",
        };
        for (size_t i = 0; i < sizeof(files)/sizeof(files[0]); ++i)
            if (unlinkat(dir, files[i], 0) != 0 && errno != ENOENT) failed = 1;
        if (fsync(dir) != 0) failed = 1;
        if (close(dir) != 0) failed = 1;
    } else if (errno != ENOENT) {
        failed = 1;
    }
    if (unlinkat(parent, leaf, AT_REMOVEDIR) != 0 && errno != ENOENT) failed = 1;
    if (fsync(parent) != 0) failed = 1;
    return failed ? -1 : 0;
}

static int sync_committed_output_dir(int dirfd, int parentfd) {
#ifdef EVIDENCE_TEST_HOOKS
    if (getenv("SIMPLE_STAGE3_RSS_TEST_FAIL_POST_RENAME_SYNC")) {
        errno = EIO;
        return -1;
    }
#endif
    return fsync(dirfd) || fsync(parentfd) ? -1 : 0;
}

static int same_identity(const FileIdentity *left, const FileIdentity *right) {
    return left->dev == right->dev && left->ino == right->ino &&
           !strcmp(left->sha256, right->sha256);
}

typedef struct {
    enum PlanKey path_key;
    enum PlanKey sha_key;
    int fd;
    FileIdentity identity;
} PlanArtifact;

static int open_plan_artifacts(const LaunchPlan *plan, PlanArtifact *artifacts,
                               size_t count) {
    static const enum PlanKey path_keys[] = {
        PLAN_ARGV_PATH, PLAN_ENV_PATH, PLAN_SOURCE_PATH, PLAN_GIT_PATH,
        PLAN_RUNTIME_SNAPSHOT_PATH, PLAN_TOOL_PATH, PLAN_STAGE2_PATH,
        PLAN_PLANNER_PATH, PLAN_CGROUP_PATH,
    };
    static const enum PlanKey sha_keys[] = {
        PLAN_ARGV_SHA, PLAN_ENV_SHA, PLAN_SOURCE_SHA, PLAN_GIT_SHA,
        PLAN_RUNTIME_SNAPSHOT_SHA, PLAN_TOOL_SHA, PLAN_STAGE2_SHA,
        PLAN_PLANNER_SHA, PLAN_CGROUP_SHA,
    };
    if (count != sizeof(path_keys)/sizeof(path_keys[0])) return -1;
    for (size_t i = 0; i < count; ++i) artifacts[i].fd = -1;
    for (size_t i = 0; i < count; ++i) {
        artifacts[i].path_key = path_keys[i];
        artifacts[i].sha_key = sha_keys[i];
        artifacts[i].fd = open_identity_absolute(plan->decoded_path[path_keys[i]],
                                                  DEFAULT_MAX_RAW_BYTES,
                                                  &artifacts[i].identity);
        if (artifacts[i].fd < 0 ||
            strcmp(artifacts[i].identity.sha256, plan->value[sha_keys[i]])) return -1;
    }
    return 0;
}

static void close_plan_artifacts(PlanArtifact *artifacts, size_t count) {
    for (size_t i = 0; i < count; ++i) {
        if (artifacts[i].fd >= 0) close(artifacts[i].fd);
        artifacts[i].fd = -1;
    }
}

static int stable_plan_artifacts(PlanArtifact *artifacts, size_t count) {
    for (size_t i = 0; i < count; ++i)
        if (artifacts[i].fd < 0 || !stable_identity_fd(artifacts[i].fd,
                                                       &artifacts[i].identity)) return -1;
    return 0;
}

static int stable_identity_roles(const IdentitySummary *identity) {
    for (size_t i = 0; i < IDENTITY_ROLE_COUNT; ++i)
        if (identity->role[i].fd < 0 ||
            !stable_identity_fd(identity->role[i].fd, &identity->role[i].identity)) return -1;
    return 0;
}

static int file_stat_size(int fd, uint64_t *size) {
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode) || st.st_size < 0) return -1;
    *size = (uint64_t)st.st_size;
    return 0;
}

static int path_matches_identity(const char *path, const FileIdentity *identity) {
    char leaf[NAME_MAX + 1];
    int parent = parent_dir_fd(path, leaf);
    if (parent < 0) return 0;
    struct stat st;
    int matches = fstatat(parent, leaf, &st, AT_SYMLINK_NOFOLLOW) == 0 &&
                  S_ISREG(st.st_mode) && (uint64_t)st.st_dev == identity->dev &&
                  (uint64_t)st.st_ino == identity->ino;
    if (close(parent) != 0) matches = 0;
    return matches;
}

static uint64_t text_record_count(const char *text) {
    uint64_t count = 0;
    for (const char *p = text; p && *p; ++p) if (*p == '\n') ++count;
    return count;
}

#if 0
static int analyze_files_legacy(int argc, char **argv) {
    const char *samples=NULL, *memory=NULL, *phase=NULL, *provenance=NULL, *run_id=NULL, *output=NULL;
    const char *expected_analyzer=NULL, *expected_sampler=NULL, *expected_command=NULL;
    const char *expected_script=NULL, *runner_path=NULL, *runner_sha=NULL;
    const char *candidate_builder_path=NULL, *candidate_builder_sha=NULL, *shell_path=NULL, *shell_sha=NULL;
    for (int i = 2; i < argc; ++i) {
#define ANALYZE_OPT(flag, target) if (!strcmp(argv[i], flag) && i + 1 < argc) { target=argv[++i]; }
        ANALYZE_OPT("--samples", samples)
        else ANALYZE_OPT("--memory", memory)
        else ANALYZE_OPT("--phase", phase)
        else ANALYZE_OPT("--provenance", provenance)
        else ANALYZE_OPT("--run-id", run_id)
        else ANALYZE_OPT("--output-dir", output)
        else ANALYZE_OPT("--analyzer-sha256", expected_analyzer)
        else ANALYZE_OPT("--expected-sampler-sha256", expected_sampler)
        else ANALYZE_OPT("--expected-command-sha256", expected_command)
        else ANALYZE_OPT("--expected-script-sha256", expected_script)
        else ANALYZE_OPT("--runner", runner_path)
        else ANALYZE_OPT("--runner-sha256", runner_sha)
        else ANALYZE_OPT("--candidate-builder", candidate_builder_path)
        else ANALYZE_OPT("--candidate-builder-sha256", candidate_builder_sha)
        else ANALYZE_OPT("--shell", shell_path)
        else ANALYZE_OPT("--shell-sha256", shell_sha)
        else return 64;
#undef ANALYZE_OPT
    }
    if (!samples||!memory||!phase||!provenance||!safe_run_id(run_id)||!output||
        !valid_sha256(expected_analyzer)||!valid_sha256(expected_sampler)||
        !valid_sha256(expected_command)||!expected_script||
        (!strcmp(expected_script,"none") ? 0 : !valid_sha256(expected_script))||
        !runner_path||!valid_sha256(runner_sha)||!candidate_builder_path||!valid_sha256(candidate_builder_sha)||
        !shell_path||!valid_sha256(shell_sha)) return 64;

    FileIdentity analyzer_identity;
    if (self_identity(&analyzer_identity) || strcmp(analyzer_identity.sha256, expected_analyzer)) return 2;
    FileIdentity raw_identity, memory_identity, phase_identity, provenance_identity;
    FileIdentity runner_identity, candidate_builder_identity, shell_identity;
    int raw_fd=open_identity_nofollow(samples,&raw_identity);
    int memory_fd=open_identity_nofollow(memory,&memory_identity);
    int phase_fd=open_identity_nofollow(phase,&phase_identity);
    int provenance_fd=open_identity_nofollow(provenance,&provenance_identity);
    int runner_fd=open_identity_nofollow(runner_path,&runner_identity);
    int candidate_builder_fd=open_identity_nofollow(candidate_builder_path,&candidate_builder_identity);
    int shell_fd=open_identity_nofollow(shell_path,&shell_identity);
    if (raw_fd<0||memory_fd<0||phase_fd<0||provenance_fd<0||runner_fd<0||candidate_builder_fd<0||shell_fd<0 ||
        strcmp(runner_identity.sha256,runner_sha)||strcmp(candidate_builder_identity.sha256,candidate_builder_sha)||
        strcmp(shell_identity.sha256,shell_sha)) goto fail_inputs;
    struct stat size_check;
    if (fstat(raw_fd,&size_check)||size_check.st_size<0||(uint64_t)size_check.st_size>DEFAULT_MAX_RAW_BYTES ||
        fstat(memory_fd,&size_check)||size_check.st_size<0||(uint64_t)size_check.st_size>UINT64_C(536870912) ||
        fstat(phase_fd,&size_check)||size_check.st_size<0||(uint64_t)size_check.st_size>UINT64_C(536870912) ||
        fstat(provenance_fd,&size_check)||size_check.st_size<0||(uint64_t)size_check.st_size>UINT64_C(67108864))
        goto fail_inputs;

    RawSummary raw;
    MemorySummary mem;
    PhaseSummary ph;
    InputStats argv_input={0}, environment_input={0};
    char argv_semantic_sha256[65]={0}, environment_semantic_sha256[65]={0};
    memset(&mem,0,sizeof(mem)); memset(&ph,0,sizeof(ph));
    if (parse_complete_raw_fd(raw_fd,run_id,&raw)||raw.raw_dev!=raw_identity.dev||raw.raw_ino!=raw_identity.ino||
        strcmp(raw.sampler.sha256,expected_sampler)||strcmp(raw.command.sha256,expected_command)||
        (strcmp(expected_script,"none") ? strcmp(raw.script.sha256,expected_script) : raw.script.ino!=0)||
        (analyzer_identity.dev==raw.sampler.dev && analyzer_identity.ino==raw.sampler.ino)||
        parse_memory_fd(memory_fd,run_id,raw.root_pid,&mem)||
        parse_phase_fd(phase_fd,run_id,raw.root_pid,&ph)||correlate_streams(&raw,&mem,&ph)||
        !stable_identity_fd(raw_fd,&raw_identity)||!stable_identity_fd(memory_fd,&memory_identity)||
        !stable_identity_fd(phase_fd,&phase_identity)||!stable_identity_fd(provenance_fd,&provenance_identity)) {
        free_memory_summary(&mem); free_phase_summary(&ph); goto fail_inputs;
    }

    char leaf[NAME_MAX+1];
    int parent=parent_dir_fd(output,leaf);
    if(parent<0) { free_memory_summary(&mem);free_phase_summary(&ph);goto fail_inputs; }
    struct stat existing;
    if(fstatat(parent,leaf,&existing,AT_SYMLINK_NOFOLLOW)==0||errno!=ENOENT||mkdirat(parent,leaf,0700)) {
        close(parent);free_memory_summary(&mem);free_phase_summary(&ph);goto fail_inputs;
    }
    int outdir=openat(parent,leaf,O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);
    if(outdir<0) goto fail_publish;
    if(write_boundary_file(outdir,&mem)||write_delta_file(outdir,&mem)) goto fail_publish_open;
    char summary_text[2048];
    int summary_len=snprintf(summary_text,sizeof(summary_text),
        "run_id=%s\nsample_interval_ms=%"PRIu64"\nmax_gap_ms=%"PRIu64
        "\nmax_observed_gap_ms=%"PRIu64"\nmax_summed_rss_kib=%"PRIu64
        "\npeak_tree_rss_kib=%"PRIu64"\nsample_batches=%"PRIu64
        "\nprocess_records=%"PRIu64"\nphysical_sources=%zu\nphase_mode=%s\nresult=complete\n",
        run_id,raw.interval_ms,raw.max_gap_ms,raw.max_observed_gap_ms,raw.max_rss_kb,
        raw.peak_tree_rss_kb,raw.sample_batches,raw.sample_records,mem.source_count,
        ph.streaming?"streaming":"nonstreaming");
    if(summary_len<=0||(size_t)summary_len>=sizeof(summary_text)||put_text_file_at(outdir,"summary.env",summary_text))
        goto fail_publish_open;
    FileIdentity boundary_identity,delta_identity,summary_identity;
    int boundary_fd=openat(outdir,"boundary.tsv",O_RDONLY|O_NOFOLLOW|O_CLOEXEC);
    int delta_fd=openat(outdir,"delta.tsv",O_RDONLY|O_NOFOLLOW|O_CLOEXEC);
    int summary_fd=openat(outdir,"summary.env",O_RDONLY|O_NOFOLLOW|O_CLOEXEC);
    if(boundary_fd<0||delta_fd<0||summary_fd<0||identity_fd(boundary_fd,&boundary_identity)||
        identity_fd(delta_fd,&delta_identity)||identity_fd(summary_fd,&summary_identity)) {
        if (boundary_fd>=0) close(boundary_fd);
        if (delta_fd>=0) close(delta_fd);
        if (summary_fd>=0) close(summary_fd);
        goto fail_publish_open;
    }
    close(boundary_fd);close(delta_fd);close(summary_fd);
    char receipt[8192];
    int receipt_len=snprintf(receipt,sizeof(receipt),
        "receipt_schema=%s\nrun_id=%s\nresult=complete\n"
        "raw_dev=%"PRIu64"\nraw_ino=%"PRIu64"\nraw_sha256=%s\n"
        "memory_dev=%"PRIu64"\nmemory_ino=%"PRIu64"\nmemory_sha256=%s\n"
        "phase_dev=%"PRIu64"\nphase_ino=%"PRIu64"\nphase_sha256=%s\n"
        "provenance_dev=%"PRIu64"\nprovenance_ino=%"PRIu64"\nprovenance_sha256=%s\n"
        "sampler_dev=%"PRIu64"\nsampler_ino=%"PRIu64"\nsampler_sha256=%s\n"
        "analyzer_dev=%"PRIu64"\nanalyzer_ino=%"PRIu64"\nanalyzer_sha256=%s\n"
        "measured_command_dev=%"PRIu64"\nmeasured_command_ino=%"PRIu64"\nmeasured_command_sha256=%s\n"
        "measured_script_dev=%"PRIu64"\nmeasured_script_ino=%"PRIu64"\nmeasured_script_sha256=%s\n"
        "runner_dev=%"PRIu64"\nrunner_ino=%"PRIu64"\nrunner_sha256=%s\n"
        "candidate_builder_dev=%"PRIu64"\ncandidate_builder_ino=%"PRIu64"\ncandidate_builder_sha256=%s\n"
        "orchestration_shell_dev=%"PRIu64"\norchestration_shell_ino=%"PRIu64"\norchestration_shell_sha256=%s\n"
        "environment_sha256=%s\nboundary_sha256=%s\ndelta_sha256=%s\nsummary_sha256=%s\n"
        "sample_interval_ms=%"PRIu64"\nmax_gap_ms=%"PRIu64"\nmax_summed_rss_kib=%"PRIu64
        "\ncompiler_wall_ms=%"PRIu64"\nmax_sample_batches=%"PRIu64
        "\nmax_process_records=%"PRIu64"\nmax_tracked_processes=%"PRIu64
        "\nraw_evidence_max_bytes=%"PRIu64"\nterm_grace_ms=%"PRIu64
        "\nkill_reap_deadline_ms=%"PRIu64"\n",
        RECEIPT_SCHEMA,run_id,raw_identity.dev,raw_identity.ino,raw_identity.sha256,
        memory_identity.dev,memory_identity.ino,memory_identity.sha256,
        phase_identity.dev,phase_identity.ino,phase_identity.sha256,
        provenance_identity.dev,provenance_identity.ino,provenance_identity.sha256,
        raw.sampler.dev,raw.sampler.ino,raw.sampler.sha256,
        analyzer_identity.dev,analyzer_identity.ino,analyzer_identity.sha256,
        raw.command.dev,raw.command.ino,raw.command.sha256,
        raw.script.dev,raw.script.ino,raw.script.ino?raw.script.sha256:"none",
        runner_identity.dev,runner_identity.ino,runner_identity.sha256,
        candidate_builder_identity.dev,candidate_builder_identity.ino,candidate_builder_identity.sha256,
        shell_identity.dev,shell_identity.ino,shell_identity.sha256,
        raw.environment_sha256,boundary_identity.sha256,delta_identity.sha256,summary_identity.sha256,
        raw.interval_ms,raw.max_gap_ms,raw.max_rss_kb,raw.max_runtime_ms,raw.max_batches,
        raw.max_records,raw.max_tracked,raw.max_raw_bytes,raw.term_grace_ms,raw.kill_grace_ms);
    if(receipt_len<=0||(size_t)receipt_len>=sizeof(receipt)||
       put_text_file_at(outdir,".receipt.pending",receipt)||fsync(outdir)||fsync(parent)) goto fail_publish_open;
    free_memory_summary(&mem);free_phase_summary(&ph);
    close(raw_fd);close(memory_fd);close(phase_fd);close(provenance_fd);
    close(runner_fd);close(candidate_builder_fd);close(shell_fd);
    /* The no-replace rename plus the following directory fsync is the durable
     * commit.  If that fsync fails, quarantine/remove the public name before
     * returning failure so no completed-looking receipt survives. */
    if(syscall(SYS_renameat2,outdir,".receipt.pending",outdir,"receipt.env",RENAME_NOREPLACE)!=0)
        goto fail_publish_open_after_inputs;
    if (sync_committed_output_dir(outdir) != 0) {
        if (syscall(SYS_renameat2,outdir,"receipt.env",outdir,".receipt.invalid",
                    RENAME_NOREPLACE) != 0)
            (void)unlinkat(outdir,"receipt.env",0);
        (void)fsync(outdir);
        goto fail_publish_open_after_inputs;
    }
    close(outdir);
    close(parent);
    return 0;

fail_publish_open_after_inputs:
    close(outdir);discard_output_dir(parent,leaf);close(parent);return 2;
fail_publish_open:
    close(outdir);
fail_publish:
    discard_output_dir(parent,leaf);close(parent);free_memory_summary(&mem);free_phase_summary(&ph);
fail_inputs:
    if (raw_fd>=0) close(raw_fd);
    if (memory_fd>=0) close(memory_fd);
    if (phase_fd>=0) close(phase_fd);
    if (provenance_fd>=0) close(provenance_fd);
    if (runner_fd>=0) close(runner_fd);
    if (candidate_builder_fd>=0) close(candidate_builder_fd);
    if (shell_fd>=0) close(shell_fd);
    return 2;
}
#endif
static int analyze_files(int argc, char **argv) {
    const char *samples=NULL, *memory=NULL, *phase=NULL, *descriptor_path=NULL;
    const char *provenance=NULL, *launch_plan_path=NULL, *run_id=NULL, *output=NULL;
    const char *candidate_provenance=NULL, *candidate_provenance_sha=NULL;
    const char *candidate_verify_receipt=NULL, *candidate_verify_receipt_sha=NULL;
    const char *expected_analyzer=NULL, *expected_sampler=NULL, *expected_admitted=NULL;
    const char *expected_script=NULL, *runner_path=NULL, *runner_sha=NULL;
    const char *candidate_builder_path=NULL, *candidate_builder_sha=NULL, *shell_path=NULL, *shell_sha=NULL;
    for (int i = 2; i < argc; ++i) {
#define ANALYZE_OPT_V2(flag, target) if (!strcmp(argv[i], flag) && i + 1 < argc) { target=argv[++i]; }
        ANALYZE_OPT_V2("--samples", samples)
        else ANALYZE_OPT_V2("--memory", memory)
        else ANALYZE_OPT_V2("--phase", phase)
        else ANALYZE_OPT_V2("--descriptor", descriptor_path)
        else ANALYZE_OPT_V2("--provenance", provenance)
        else ANALYZE_OPT_V2("--candidate-provenance", candidate_provenance)
        else ANALYZE_OPT_V2("--candidate-provenance-sha256", candidate_provenance_sha)
        else ANALYZE_OPT_V2("--candidate-provenance-verify-receipt", candidate_verify_receipt)
        else ANALYZE_OPT_V2("--candidate-provenance-verify-receipt-sha256", candidate_verify_receipt_sha)
        else ANALYZE_OPT_V2("--launch-plan", launch_plan_path)
        else ANALYZE_OPT_V2("--run-id", run_id)
        else ANALYZE_OPT_V2("--output-dir", output)
        else ANALYZE_OPT_V2("--analyzer-sha256", expected_analyzer)
        else ANALYZE_OPT_V2("--expected-sampler-sha256", expected_sampler)
        else ANALYZE_OPT_V2("--expected-admitted-compiler-sha256", expected_admitted)
        else ANALYZE_OPT_V2("--expected-script-sha256", expected_script)
        else ANALYZE_OPT_V2("--runner", runner_path)
        else ANALYZE_OPT_V2("--runner-sha256", runner_sha)
        else ANALYZE_OPT_V2("--candidate-builder", candidate_builder_path)
        else ANALYZE_OPT_V2("--candidate-builder-sha256", candidate_builder_sha)
        else ANALYZE_OPT_V2("--shell", shell_path)
        else ANALYZE_OPT_V2("--shell-sha256", shell_sha)
        else return 64;
#undef ANALYZE_OPT_V2
    }
    const char *path_args[] = {
        samples, memory, phase, descriptor_path, provenance, candidate_provenance,
        candidate_verify_receipt, launch_plan_path, output, runner_path, candidate_builder_path, shell_path,
    };
    if (!samples || !memory || !phase || !descriptor_path || !provenance ||
        !candidate_provenance || !valid_sha256(candidate_provenance_sha) ||
        !candidate_verify_receipt || !valid_sha256(candidate_verify_receipt_sha) ||
        !launch_plan_path || !safe_run_id(run_id) || !output ||
        !valid_sha256(expected_analyzer) || !valid_sha256(expected_sampler) ||
        !valid_sha256(expected_admitted) || !expected_script || strcmp(expected_script, "none") ||
        !runner_path || !valid_sha256(runner_sha) || !candidate_builder_path || !valid_sha256(candidate_builder_sha) ||
        !shell_path || !valid_sha256(shell_sha)) return 64;
    for (size_t i = 0; i < sizeof(path_args)/sizeof(path_args[0]); ++i)
        if (!normalized_absolute_path(path_args[i])) return 64;

    int result = 2;
    int raw_fd=-1, memory_fd=-1, phase_fd=-1, descriptor_fd=-1, provenance_fd=-1;
    int plan_fd=-1, identity_fd_open=-1, provenance_receipt_fd=-1, candidate_fd=-1;
    int candidate_provenance_fd=-1, candidate_verify_receipt_fd=-1;
    int runner_fd=-1, candidate_builder_fd=-1, shell_fd=-1;
    int parent=-1, parent_guard=-1, outdir=-1;
    int output_created = 0, identity_parsed = 0;
    FileIdentity analyzer_identity={0}, raw_identity={0}, memory_identity={0}, phase_identity={0};
    FileIdentity descriptor_identity={0}, provenance_identity={0}, plan_identity={0};
    FileIdentity identity_manifest_identity={0}, provenance_receipt_identity={0};
    FileIdentity candidate_provenance_identity={0}, candidate_verify_receipt_identity={0};
    FileIdentity candidate_identity={0}, runner_identity={0}, candidate_builder_identity={0}, shell_identity={0};
    LaunchPlan plan;
    DescriptorSummary desc;
    IdentitySummary identities;
    ProvenanceReceipt prov_receipt, candidate_prov_receipt;
    RawSummary raw;
    MemorySummary mem;
    PhaseSummary ph;
    InputStats argv_input={0}, environment_input={0};
    char argv_semantic_sha256[65]={0}, environment_semantic_sha256[65]={0};
    PlanArtifact artifacts[9];
    memset(&plan,0,sizeof(plan)); memset(&desc,0,sizeof(desc));
    memset(&identities,0,sizeof(identities)); memset(&prov_receipt,0,sizeof(prov_receipt));
    memset(&candidate_prov_receipt,0,sizeof(candidate_prov_receipt));
    memset(&raw,0,sizeof(raw)); memset(&mem,0,sizeof(mem)); memset(&ph,0,sizeof(ph));
    for (size_t i=0;i<9;++i) artifacts[i].fd=-1;

    if (self_identity(&analyzer_identity) ||
        strcmp(analyzer_identity.sha256, expected_analyzer)) goto cleanup;
    plan_fd = open_identity_absolute(launch_plan_path, METADATA_MAX_BYTES, &plan_identity);
    if (plan_fd < 0 || parse_launch_plan_fd(plan_fd, run_id, &plan)) goto cleanup;
    if (strcmp(plan.decoded_path[PLAN_DESCRIPTOR_PATH], descriptor_path) ||
        strcmp(plan.decoded_path[PLAN_PROVENANCE_PATH], provenance) ||
        strcmp(plan.decoded_path[PLAN_RAW_PATH], samples) ||
        strcmp(plan.decoded_path[PLAN_MEMORY_PATH], memory) ||
        strcmp(plan.decoded_path[PLAN_PHASE_PATH], phase) ||
        strcmp(plan.decoded_path[PLAN_OUTPUT_PATH], output)) goto cleanup;

    raw_fd = open_identity_absolute(samples, DEFAULT_MAX_RAW_BYTES, &raw_identity);
    memory_fd = open_identity_absolute(memory, COMPILER_STREAM_MAX_BYTES, &memory_identity);
    phase_fd = open_identity_absolute(phase, COMPILER_STREAM_MAX_BYTES, &phase_identity);
    descriptor_fd = open_identity_absolute(descriptor_path, METADATA_MAX_BYTES, &descriptor_identity);
    provenance_fd = open_identity_absolute(provenance, METADATA_MAX_BYTES, &provenance_identity);
    runner_fd = open_identity_absolute(runner_path, DEFAULT_MAX_RAW_BYTES, &runner_identity);
    candidate_builder_fd = open_identity_absolute(candidate_builder_path, DEFAULT_MAX_RAW_BYTES, &candidate_builder_identity);
    shell_fd = open_identity_absolute(shell_path, DEFAULT_MAX_RAW_BYTES, &shell_identity);
    if (raw_fd<0 || memory_fd<0 || phase_fd<0 || descriptor_fd<0 || provenance_fd<0 ||
        runner_fd<0 || candidate_builder_fd<0 || shell_fd<0 ||
        strcmp(descriptor_identity.sha256, plan.value[PLAN_DESCRIPTOR_SHA]) ||
        strcmp(provenance_identity.sha256, plan.value[PLAN_PROVENANCE_SHA]) ||
        strcmp(runner_identity.sha256, runner_sha) ||
        strcmp(candidate_builder_identity.sha256, candidate_builder_sha) || strcmp(shell_identity.sha256, shell_sha))
        goto cleanup;

    identity_fd_open = open_identity_absolute(plan.decoded_path[PLAN_IDENTITY_PATH],
                                               METADATA_MAX_BYTES,
                                               &identity_manifest_identity);
    provenance_receipt_fd = open_identity_absolute(plan.decoded_path[PLAN_PROV_RECEIPT_PATH],
                                                    METADATA_MAX_BYTES,
                                                    &provenance_receipt_identity);
    candidate_fd = open_identity_absolute(plan.decoded_path[PLAN_CANDIDATE_PATH],
                                          DEFAULT_MAX_RAW_BYTES, &candidate_identity);
    candidate_provenance_fd = open_identity_absolute(candidate_provenance,
                                                      METADATA_MAX_BYTES,
                                                      &candidate_provenance_identity);
    candidate_verify_receipt_fd = open_identity_absolute(candidate_verify_receipt,
                                                          METADATA_MAX_BYTES,
                                                          &candidate_verify_receipt_identity);
    if (identity_fd_open<0 || provenance_receipt_fd<0 || candidate_fd<0 ||
        candidate_provenance_fd<0 || candidate_verify_receipt_fd<0 ||
        strcmp(identity_manifest_identity.sha256, plan.value[PLAN_IDENTITY_SHA]) ||
        strcmp(provenance_receipt_identity.sha256, plan.value[PLAN_PROV_RECEIPT_SHA]) ||
        strcmp(candidate_provenance_identity.sha256, candidate_provenance_sha) ||
        strcmp(candidate_verify_receipt_identity.sha256, candidate_verify_receipt_sha) ||
        !strcmp(provenance,candidate_provenance) ||
        (provenance_identity.dev==candidate_provenance_identity.dev &&
         provenance_identity.ino==candidate_provenance_identity.ino) ||
        !strcmp(plan.decoded_path[PLAN_PROV_RECEIPT_PATH],candidate_verify_receipt) ||
        (provenance_receipt_identity.dev==candidate_verify_receipt_identity.dev &&
         provenance_receipt_identity.ino==candidate_verify_receipt_identity.ino) ||
        open_plan_artifacts(&plan, artifacts, 9)) goto cleanup;

    identity_parsed = 1;
    if (parse_descriptor_fd(descriptor_fd, run_id, &desc) ||
        parse_identity_fd(identity_fd_open, run_id, &identities) ||
        parse_provenance_receipt_fd(provenance_receipt_fd, run_id, &prov_receipt) ||
        parse_provenance_receipt_fd(candidate_verify_receipt_fd, run_id,
                                    &candidate_prov_receipt) ||
        parse_complete_raw_fd(raw_fd, run_id, &raw) ||
        raw.raw_dev != raw_identity.dev || raw.raw_ino != raw_identity.ino ||
        parse_memory_fd(memory_fd, run_id, raw.root_pid, &desc, &mem) ||
        parse_phase_fd(phase_fd, run_id, raw.root_pid, &desc, &ph) ||
        !ph.streaming || correlate_streams(&raw, &mem, &ph)) goto cleanup;

    if (parse_argv_transcript_fd(artifacts[0].fd,run_id,raw.command_argv_hex,
                                 argv_semantic_sha256,&argv_input) ||
        parse_environment_transcript_fd(artifacts[1].fd,run_id,raw.environment_sha256,
                                         &plan,identities.role[0].path,
                                         environment_semantic_sha256,&environment_input))
        goto cleanup;

    /* PLAN policy is not advisory: it must match the admitted raw owner. */
    if (raw.interval_ms != DEFAULT_INTERVAL_MS || raw.max_gap_ms != DEFAULT_MAX_GAP_MS ||
        raw.max_rss_kb != DEFAULT_MAX_RSS_KB || raw.max_runtime_ms != DEFAULT_MAX_RUNTIME_MS ||
        raw.max_batches != DEFAULT_MAX_BATCHES || raw.max_records != DEFAULT_MAX_RECORDS ||
        raw.max_tracked != MAX_TRACKED || raw.max_raw_bytes != DEFAULT_MAX_RAW_BYTES ||
        raw.term_grace_ms != DEFAULT_TERM_GRACE_MS || raw.kill_grace_ms != DEFAULT_KILL_GRACE_MS)
        goto cleanup;

    enum { ID_ADMITTED=0, ID_SAMPLER=1, ID_ANALYZER=2, ID_SHARED_RUNNER=4,
           ID_DASH=6, ID_CANDIDATE_BUILDER=10, ID_PROVENANCE_VERIFIER=14 };
    if (!same_identity(&identities.role[ID_ADMITTED].identity, &raw.command) ||
        same_identity(&identities.role[ID_ADMITTED].identity, &candidate_identity) ||
        !strcmp(identities.role[ID_ADMITTED].path, plan.decoded_path[PLAN_CANDIDATE_PATH]) ||
        !same_identity(&identities.role[ID_SAMPLER].identity, &raw.sampler) ||
        !same_identity(&identities.role[ID_ANALYZER].identity, &analyzer_identity) ||
        !same_identity(&identities.role[ID_SHARED_RUNNER].identity, &runner_identity) ||
        !same_identity(&identities.role[ID_CANDIDATE_BUILDER].identity, &candidate_builder_identity) ||
        !same_identity(&identities.role[ID_DASH].identity, &shell_identity) ||
        strcmp(raw.sampler.sha256, expected_sampler) ||
        strcmp(raw.command.sha256, expected_admitted) || raw.script.dev || raw.script.ino)
        goto cleanup;

    if (strcmp(prov_receipt.value[PROV_PROVENANCE_SHA], provenance_identity.sha256) ||
        strcmp(prov_receipt.value[PROV_CANDIDATE_SHA], raw.command.sha256) ||
        strcmp(prov_receipt.value[PROV_SOURCE_SHA], plan.value[PLAN_SOURCE_SHA]) ||
        strcmp(prov_receipt.value[PROV_RUNTIME_SHA], plan.value[PLAN_RUNTIME_SNAPSHOT_SHA]) ||
        strcmp(prov_receipt.value[PROV_TOOL_SHA], plan.value[PLAN_TOOL_SHA]) ||
        strcmp(prov_receipt.value[PROV_GIT_SHA], plan.value[PLAN_GIT_SHA]) ||
        strcmp(prov_receipt.value[PROV_VERIFIER_SHA],
               identities.role[ID_PROVENANCE_VERIFIER].identity.sha256) ||
        strcmp(candidate_prov_receipt.value[PROV_PROVENANCE_SHA],
               candidate_provenance_identity.sha256) ||
        strcmp(candidate_prov_receipt.value[PROV_CANDIDATE_SHA], candidate_identity.sha256) ||
        strcmp(candidate_prov_receipt.value[PROV_SOURCE_SHA], plan.value[PLAN_SOURCE_SHA]) ||
        strcmp(candidate_prov_receipt.value[PROV_RUNTIME_SHA],
               plan.value[PLAN_RUNTIME_SNAPSHOT_SHA]) ||
        strcmp(candidate_prov_receipt.value[PROV_TOOL_SHA], plan.value[PLAN_TOOL_SHA]) ||
        strcmp(candidate_prov_receipt.value[PROV_GIT_SHA], plan.value[PLAN_GIT_SHA]) ||
        strcmp(candidate_prov_receipt.value[PROV_VERIFIER_SHA],
               identities.role[ID_PROVENANCE_VERIFIER].identity.sha256)) goto cleanup;

    if (derived_preflight(&mem)) goto cleanup;

#ifdef EVIDENCE_TEST_HOOKS
    const char *stability_ready = getenv("SIMPLE_STAGE3_RSS_TEST_ANALYZE_STABILITY_READY_FIFO");
    const char *stability_continue =
        getenv("SIMPLE_STAGE3_RSS_TEST_ANALYZE_STABILITY_CONTINUE_FIFO");
    if ((stability_ready && !stability_continue) || (!stability_ready && stability_continue))
        goto cleanup;
    if (stability_ready) {
        int ready_fd = open(stability_ready,O_WRONLY|O_CLOEXEC);
        if (ready_fd<0 || test_write_all(ready_fd,"x",1) || close(ready_fd)) goto cleanup;
        int continue_fd = open(stability_continue,O_RDONLY|O_CLOEXEC);
        unsigned char byte;
        ssize_t got;
        if (continue_fd<0) goto cleanup;
        do { got=read(continue_fd,&byte,1); } while(got<0 && errno==EINTR);
        if (close(continue_fd) || got!=1) goto cleanup;
    }
#endif

    /* Rehash every still-open authority and recheck its pathname immediately
     * before any completed receipt can be published. */
    if (!stable_identity_fd(plan_fd,&plan_identity) ||
        !stable_identity_fd(raw_fd,&raw_identity) ||
        !stable_identity_fd(memory_fd,&memory_identity) ||
        !stable_identity_fd(phase_fd,&phase_identity) ||
        !stable_identity_fd(descriptor_fd,&descriptor_identity) ||
        !stable_identity_fd(provenance_fd,&provenance_identity) ||
        !stable_identity_fd(identity_fd_open,&identity_manifest_identity) ||
        !stable_identity_fd(provenance_receipt_fd,&provenance_receipt_identity) ||
        !stable_identity_fd(candidate_fd,&candidate_identity) ||
        !stable_identity_fd(candidate_provenance_fd,&candidate_provenance_identity) ||
        !stable_identity_fd(candidate_verify_receipt_fd,&candidate_verify_receipt_identity) ||
        !stable_identity_fd(runner_fd,&runner_identity) ||
        !stable_identity_fd(candidate_builder_fd,&candidate_builder_identity) ||
        !stable_identity_fd(shell_fd,&shell_identity) ||
        stable_plan_artifacts(artifacts,9) || stable_identity_roles(&identities) ||
        !path_matches_identity(launch_plan_path,&plan_identity) ||
        !path_matches_identity(samples,&raw_identity) ||
        !path_matches_identity(memory,&memory_identity) ||
        !path_matches_identity(phase,&phase_identity) ||
        !path_matches_identity(descriptor_path,&descriptor_identity) ||
        !path_matches_identity(provenance,&provenance_identity) ||
        !path_matches_identity(plan.decoded_path[PLAN_IDENTITY_PATH],&identity_manifest_identity) ||
        !path_matches_identity(plan.decoded_path[PLAN_PROV_RECEIPT_PATH],&provenance_receipt_identity) ||
        !path_matches_identity(plan.decoded_path[PLAN_CANDIDATE_PATH],&candidate_identity) ||
        !path_matches_identity(candidate_provenance,&candidate_provenance_identity) ||
        !path_matches_identity(candidate_verify_receipt,&candidate_verify_receipt_identity))
        goto cleanup;
    for (size_t i=0;i<9;++i)
        if (!path_matches_identity(plan.decoded_path[artifacts[i].path_key],
                                   &artifacts[i].identity)) goto cleanup;
    for (size_t i=0;i<IDENTITY_ROLE_COUNT;++i)
        if (!path_matches_identity(identities.role[i].path,
                                   &identities.role[i].identity)) goto cleanup;

    char leaf[NAME_MAX+1];
    parent=parent_dir_fd(output,leaf);
    if(parent<0) goto cleanup;
    parent_guard=dup(parent);
    if(parent_guard<0) goto cleanup;
    struct stat existing;
    if(fstatat(parent,leaf,&existing,AT_SYMLINK_NOFOLLOW)==0 || errno!=ENOENT ||
       mkdirat(parent,leaf,0700)) goto cleanup;
    output_created=1;
    if(created_output_parent_sync(parent)!=0) goto cleanup;
    outdir=openat(parent,leaf,O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);
    if(outdir<0 || write_boundary_file(outdir,&mem) || write_delta_file(outdir,&mem)) goto cleanup;

    char summary_text[2048];
    int summary_len=snprintf(summary_text,sizeof(summary_text),
        "run_id=%s\nsample_interval_ms=%"PRIu64"\nmax_gap_ms=%"PRIu64
        "\nmax_observed_gap_ms=%"PRIu64"\nmax_summed_rss_kib=%"PRIu64
        "\npeak_tree_rss_kib=%"PRIu64"\nsample_batches=%"PRIu64
        "\nprocess_records=%"PRIu64"\nphysical_sources=%zu\nphase_mode=%s\nresult=complete\n",
        run_id,raw.interval_ms,raw.max_gap_ms,raw.max_observed_gap_ms,raw.max_rss_kb,
        raw.peak_tree_rss_kb,raw.sample_batches,raw.sample_records,mem.source_count,
        ph.streaming?"streaming":"nonstreaming");
    if(summary_len<=0 || (size_t)summary_len>=sizeof(summary_text) ||
       put_text_file_at(outdir,"summary.env",summary_text)) goto cleanup;

    FileIdentity boundary_identity,delta_identity,summary_identity;
    int boundary_fd=openat(outdir,"boundary.tsv",O_RDONLY|O_NOFOLLOW|O_CLOEXEC);
    int delta_fd=openat(outdir,"delta.tsv",O_RDONLY|O_NOFOLLOW|O_CLOEXEC);
    int summary_fd=openat(outdir,"summary.env",O_RDONLY|O_NOFOLLOW|O_CLOEXEC);
    uint64_t boundary_bytes=0,delta_bytes=0,summary_bytes=0;
    if(boundary_fd<0 || delta_fd<0 || summary_fd<0 ||
       identity_fd(boundary_fd,&boundary_identity) || identity_fd(delta_fd,&delta_identity) ||
       identity_fd(summary_fd,&summary_identity) || file_stat_size(boundary_fd,&boundary_bytes) ||
       file_stat_size(delta_fd,&delta_bytes) || file_stat_size(summary_fd,&summary_bytes) ||
       boundary_bytes>DERIVED_MAX_FILE_BYTES || delta_bytes>DERIVED_MAX_FILE_BYTES ||
       summary_bytes>DERIVED_MAX_FILE_BYTES) {
        if(boundary_fd>=0)close(boundary_fd);
        if(delta_fd>=0)close(delta_fd);
        if(summary_fd>=0)close(summary_fd);
        goto cleanup;
    }
    if(close(boundary_fd)||close(delta_fd)||close(summary_fd)) goto cleanup;

    char candidate_provenance_path_token[METADATA_MAX_RECORD_BYTES+1];
    char candidate_verify_receipt_path_token[METADATA_MAX_RECORD_BYTES+1];
    char admitted_compiler_path_token[METADATA_MAX_RECORD_BYTES+1];
    char produced_candidate_path_token[METADATA_MAX_RECORD_BYTES+1];
    if (encode_token_v2(candidate_provenance,candidate_provenance_path_token,
                        sizeof(candidate_provenance_path_token)) ||
        encode_token_v2(candidate_verify_receipt,candidate_verify_receipt_path_token,
                        sizeof(candidate_verify_receipt_path_token)) ||
        encode_token_v2(identities.role[ID_ADMITTED].path,admitted_compiler_path_token,
                        sizeof(admitted_compiler_path_token)) ||
        encode_token_v2(plan.decoded_path[PLAN_CANDIDATE_PATH],produced_candidate_path_token,
                        sizeof(produced_candidate_path_token))) goto cleanup;

    char *receipt=NULL;
    int receipt_len=asprintf(&receipt,
        "receipt_schema=%s\nrun_id=%s\nresult=complete\n"
        "raw_dev=%"PRIu64"\nraw_ino=%"PRIu64"\nraw_sha256=%s\n"
        "memory_dev=%"PRIu64"\nmemory_ino=%"PRIu64"\nmemory_sha256=%s\n"
        "phase_dev=%"PRIu64"\nphase_ino=%"PRIu64"\nphase_sha256=%s\n"
        "provenance_dev=%"PRIu64"\nprovenance_ino=%"PRIu64"\nprovenance_sha256=%s\n"
        "descriptor_dev=%"PRIu64"\ndescriptor_ino=%"PRIu64"\ndescriptor_sha256=%s\n"
        "launch_plan_dev=%"PRIu64"\nlaunch_plan_ino=%"PRIu64"\nlaunch_plan_sha256=%s\n"
        "identity_manifest_dev=%"PRIu64"\nidentity_manifest_ino=%"PRIu64"\nidentity_manifest_sha256=%s\n"
        "provenance_verify_receipt_dev=%"PRIu64"\nprovenance_verify_receipt_ino=%"PRIu64
        "\nprovenance_verify_receipt_sha256=%s\n"
        "candidate_provenance_path=%s\ncandidate_provenance_dev=%"PRIu64
        "\ncandidate_provenance_ino=%"PRIu64"\ncandidate_provenance_sha256=%s\n"
        "candidate_provenance_verify_receipt_path=%s\n"
        "candidate_provenance_verify_receipt_dev=%"PRIu64
        "\ncandidate_provenance_verify_receipt_ino=%"PRIu64
        "\ncandidate_provenance_verify_receipt_sha256=%s\n"
        "admitted_compiler_path=%s\nadmitted_compiler_dev=%"PRIu64
        "\nadmitted_compiler_ino=%"PRIu64"\nadmitted_compiler_sha256=%s\n"
        "produced_candidate_path=%s\nproduced_candidate_dev=%"PRIu64
        "\nproduced_candidate_ino=%"PRIu64"\nproduced_candidate_sha256=%s\n"
        "sampler_dev=%"PRIu64"\nsampler_ino=%"PRIu64"\nsampler_sha256=%s\n"
        "analyzer_dev=%"PRIu64"\nanalyzer_ino=%"PRIu64"\nanalyzer_sha256=%s\n"
        "measured_command_dev=%"PRIu64"\nmeasured_command_ino=%"PRIu64"\nmeasured_command_sha256=%s\n"
        "measured_script_dev=0\nmeasured_script_ino=0\nmeasured_script_sha256=none\n"
        "runner_dev=%"PRIu64"\nrunner_ino=%"PRIu64"\nrunner_sha256=%s\n"
        "candidate_builder_dev=%"PRIu64"\ncandidate_builder_ino=%"PRIu64"\ncandidate_builder_sha256=%s\n"
        "orchestration_shell_dev=%"PRIu64"\norchestration_shell_ino=%"PRIu64
        "\norchestration_shell_sha256=%s\n"
        "environment_sha256=%s\nargv_semantic_sha256=%s\nenvironment_semantic_sha256=%s\n"
        "boundary_sha256=%s\ndelta_sha256=%s\nsummary_sha256=%s\n"
        "sample_interval_ms=%"PRIu64"\nmax_gap_ms=%"PRIu64"\nmax_summed_rss_kib=%"PRIu64
        "\ncompiler_wall_ms=%"PRIu64"\nmax_sample_batches=%"PRIu64
        "\nmax_process_records=%"PRIu64"\nmax_tracked_processes=%"PRIu64
        "\nraw_evidence_max_bytes=%"PRIu64"\nterm_grace_ms=%"PRIu64
        "\nkill_reap_deadline_ms=%"PRIu64
        "\nclosure_reserve_bytes=%u\nclosure_reserve_records=%u\nphysical_sources=%zu"
        "\nphase_mode=%s\nobserved_max_start_gap_ns=%"PRIu64
        "\nobserved_max_batch_duration_ns=%"PRIu64
        "\nmemory_bytes=%"PRIu64"\nmemory_records=%"PRIu64
        "\nphase_bytes=%"PRIu64"\nphase_records=%"PRIu64
        "\ndescriptor_records=%"PRIu64"\nidentity_records=%"PRIu64
        "\nplan_records=%"PRIu64"\nprovenance_verify_records=%"PRIu64"\n",
        RECEIPT_SCHEMA_V2,run_id,raw_identity.dev,raw_identity.ino,raw_identity.sha256,
        memory_identity.dev,memory_identity.ino,memory_identity.sha256,
        phase_identity.dev,phase_identity.ino,phase_identity.sha256,
        provenance_identity.dev,provenance_identity.ino,provenance_identity.sha256,
        descriptor_identity.dev,descriptor_identity.ino,descriptor_identity.sha256,
        plan_identity.dev,plan_identity.ino,plan_identity.sha256,
        identity_manifest_identity.dev,identity_manifest_identity.ino,identity_manifest_identity.sha256,
        provenance_receipt_identity.dev,provenance_receipt_identity.ino,provenance_receipt_identity.sha256,
        candidate_provenance_path_token,candidate_provenance_identity.dev,
        candidate_provenance_identity.ino,candidate_provenance_identity.sha256,
        candidate_verify_receipt_path_token,candidate_verify_receipt_identity.dev,
        candidate_verify_receipt_identity.ino,candidate_verify_receipt_identity.sha256,
        admitted_compiler_path_token,raw.command.dev,raw.command.ino,raw.command.sha256,
        produced_candidate_path_token,candidate_identity.dev,candidate_identity.ino,
        candidate_identity.sha256,
        raw.sampler.dev,raw.sampler.ino,raw.sampler.sha256,
        analyzer_identity.dev,analyzer_identity.ino,analyzer_identity.sha256,
        raw.command.dev,raw.command.ino,raw.command.sha256,
        runner_identity.dev,runner_identity.ino,runner_identity.sha256,
        candidate_builder_identity.dev,candidate_builder_identity.ino,candidate_builder_identity.sha256,
        shell_identity.dev,shell_identity.ino,shell_identity.sha256,
        raw.environment_sha256,argv_semantic_sha256,environment_semantic_sha256,
        boundary_identity.sha256,delta_identity.sha256,summary_identity.sha256,
        raw.interval_ms,raw.max_gap_ms,raw.max_rss_kb,raw.max_runtime_ms,raw.max_batches,
        raw.max_records,raw.max_tracked,raw.max_raw_bytes,raw.term_grace_ms,raw.kill_grace_ms,
        CLOSURE_RESERVE_BYTES,CLOSURE_RESERVE_RECORDS,mem.source_count,
        ph.streaming?"streaming":"nonstreaming",raw.observed_max_start_gap_ns,
        raw.observed_max_batch_duration_ns,mem.bytes,mem.rows,ph.bytes,ph.rows,
        desc.input.records,identities.input.records,plan.input.records,prov_receipt.input.records);
    if(receipt_len<=0 || !receipt || (uint64_t)receipt_len>RECEIPT_MAX_BYTES) {
        free(receipt); goto cleanup;
    }
    uint64_t derived_records = 1 + 4*mem.source_count + 1 + 3*mem.source_count +
                               text_record_count(summary_text) + text_record_count(receipt);
    if(boundary_bytes+delta_bytes+summary_bytes+(uint64_t)receipt_len>DERIVED_MAX_TOTAL_BYTES ||
       derived_records>DERIVED_MAX_RECORDS || put_text_file_at(outdir,".receipt.pending",receipt) ||
       fsync(outdir) || fsync(parent)) { free(receipt); goto cleanup; }
    free(receipt);

    if(syscall(SYS_renameat2,outdir,".receipt.pending",outdir,"receipt.env",RENAME_NOREPLACE)!=0)
        goto cleanup;
    if(sync_committed_output_dir(outdir,parent)!=0) {
        if(syscall(SYS_renameat2,outdir,"receipt.env",outdir,".receipt.invalid",RENAME_NOREPLACE)!=0 &&
           unlinkat(outdir,"receipt.env",0)!=0) {
            fprintf(stderr,"could not quarantine failed Stage-3 receipt\n");
        }
        (void)fsync(outdir); (void)fsync(parent);
        goto cleanup;
    }
    if(close(outdir)!=0) { outdir=-1; goto cleanup; }
    outdir=-1;
    if(close(parent)!=0) { parent=-1; goto cleanup; }
    parent=-1;
    if(close(parent_guard)!=0) { parent_guard=-1; goto cleanup; }
    parent_guard=-1;
    output_created=0;
    result=0;

cleanup:
    if (result != 0 && output_created) {
        int cleanup_parent = parent_guard >= 0 ? parent_guard : parent;
        if (outdir >= 0) {
            (void)unlinkat(outdir,"receipt.env",0);
            (void)fsync(outdir);
            (void)close(outdir);
            outdir=-1;
        }
        if (cleanup_parent >= 0 && discard_output_dir(cleanup_parent,
                plan.decoded_path[PLAN_OUTPUT_PATH]
                    ? strrchr(plan.decoded_path[PLAN_OUTPUT_PATH],'/')+1 : "") != 0)
            fprintf(stderr,"could not durably discard failed Stage-3 output\n");
    }
    if(outdir>=0) close(outdir);
    if(parent>=0) close(parent);
    if(parent_guard>=0) close(parent_guard);
    if(raw_fd>=0)close(raw_fd);
    if(memory_fd>=0)close(memory_fd);
    if(phase_fd>=0)close(phase_fd);
    if(descriptor_fd>=0)close(descriptor_fd);
    if(provenance_fd>=0)close(provenance_fd);
    if(plan_fd>=0)close(plan_fd);
    if(identity_fd_open>=0)close(identity_fd_open);
    if(provenance_receipt_fd>=0)close(provenance_receipt_fd);
    if(candidate_fd>=0)close(candidate_fd);
    if(candidate_provenance_fd>=0)close(candidate_provenance_fd);
    if(candidate_verify_receipt_fd>=0)close(candidate_verify_receipt_fd);
    if(runner_fd>=0)close(runner_fd);
    if(candidate_builder_fd>=0)close(candidate_builder_fd);
    if(shell_fd>=0)close(shell_fd);
    close_plan_artifacts(artifacts,9);
    if(identity_parsed) free_identity_summary(&identities);
    free_provenance_receipt(&prov_receipt); free_provenance_receipt(&candidate_prov_receipt);
    free_descriptor_summary(&desc);
    free_memory_summary(&mem); free_phase_summary(&ph); free_launch_plan(&plan);
    return result;
}

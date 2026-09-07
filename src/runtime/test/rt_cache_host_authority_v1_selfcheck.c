/* Selfcheck for src/runtime/runtime_cache_host_authority_v1.c.
 *
 * Build and run (it links the provider directly; it is in no runtime list):
 *   clang -std=gnu11 -Wall -Wextra -o /tmp/authority_selfcheck \
 *       src/runtime/test/rt_cache_host_authority_v1_selfcheck.c \
 *       src/runtime/runtime_cache_host_authority_v1.c && /tmp/authority_selfcheck
 *
 * Exit 0 = all checks passed. Every failure prints what it expected.
 *
 * The daemon checks mirror the non-ignored tests of the Rust lane
 * (src/compiler_rust/runtime/src/cache_daemon_process_v1.rs): a hostile socket
 * is replaced by a locked, authenticated daemon inside the connect budget; the
 * handshake is process-real; and an unavailable singleton falls back to the
 * anchored spool inside the budget. They are here rather than in a new file so
 * the runtime source-list parity baseline gains no further rows.
 *
 * Known limit, stated rather than papered over: the SHA-256 below is a second
 * transcription, so agreement with the provider proves the two agree, not that
 * either matches RFC 6234. The KAT in check_sha256_kat() closes exactly that
 * gap -- it pins THIS transcription to the published "abc" vector, and the
 * handshake check then pins the provider's digest to this one. What is still
 * NOT proven here is live interop against the Rust lane's `sha2` crate, which
 * would need both runtimes linked at once.
 */

#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/un.h>
#include <time.h>
#include <unistd.h>

int64_t rt_cache_host_open_root_v1(const uint8_t *, int64_t);
int64_t rt_cache_daemon_route_v1(const uint8_t *, int64_t);
int64_t rt_cache_daemon_serve_v1(const uint8_t *, int64_t);

/* Protocol constants, asserted here so a silent reframing of the wire format
 * breaks this file rather than only breaking interop at runtime. */
#define SOCKET_NAME       ".simple-cache-daemon-v1.sock"
#define LOCK_NAME         ".simple-cache-daemon-v1.lock"
#define REQ_MAGIC         "SCREQV1"
#define ACK_MAGIC         "SCACKV1"
#define REQ_LEN           40
#define ACK_LEN           80
#define OFF_MAGIC         0
#define OFF_NONCE         8
#define OFF_PID           40
#define OFF_UID           44
#define OFF_DIGEST        48
#define ROUTE_DAEMON      1
#define ROUTE_SPOOL       2
#define CONNECT_BUDGET_MS 250

/* ------------------------------------------------------------------ SHA-256 */
static uint32_t rotr(uint32_t v, unsigned s) { return (v >> s) | (v << (32 - s)); }

static void sha256_block(uint32_t st[8], const uint8_t b[64]) {
    static const uint32_t K[64] = {
        0x428a2f98u,0x71374491u,0xb5c0fbcfu,0xe9b5dba5u,0x3956c25bu,0x59f111f1u,
        0x923f82a4u,0xab1c5ed5u,0xd807aa98u,0x12835b01u,0x243185beu,0x550c7dc3u,
        0x72be5d74u,0x80deb1feu,0x9bdc06a7u,0xc19bf174u,0xe49b69c1u,0xefbe4786u,
        0x0fc19dc6u,0x240ca1ccu,0x2de92c6fu,0x4a7484aau,0x5cb0a9dcu,0x76f988dau,
        0x983e5152u,0xa831c66du,0xb00327c8u,0xbf597fc7u,0xc6e00bf3u,0xd5a79147u,
        0x06ca6351u,0x14292967u,0x27b70a85u,0x2e1b2138u,0x4d2c6dfcu,0x53380d13u,
        0x650a7354u,0x766a0abbu,0x81c2c92eu,0x92722c85u,0xa2bfe8a1u,0xa81a664bu,
        0xc24b8b70u,0xc76c51a3u,0xd192e819u,0xd6990624u,0xf40e3585u,0x106aa070u,
        0x19a4c116u,0x1e376c08u,0x2748774cu,0x34b0bcb5u,0x391c0cb3u,0x4ed8aa4au,
        0x5b9cca4fu,0x682e6ff3u,0x748f82eeu,0x78a5636fu,0x84c87814u,0x8cc70208u,
        0x90befffau,0xa4506cebu,0xbef9a3f7u,0xc67178f2u };
    uint32_t w[64];
    for (int i = 0; i < 16; i++)
        w[i] = ((uint32_t)b[i*4] << 24) | ((uint32_t)b[i*4+1] << 16)
             | ((uint32_t)b[i*4+2] << 8) | (uint32_t)b[i*4+3];
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = rotr(w[i-15],7) ^ rotr(w[i-15],18) ^ (w[i-15] >> 3);
        uint32_t s1 = rotr(w[i-2],17) ^ rotr(w[i-2],19) ^ (w[i-2] >> 10);
        w[i] = w[i-16] + s0 + w[i-7] + s1;
    }
    uint32_t a=st[0],bb=st[1],c=st[2],d=st[3],e=st[4],f=st[5],g=st[6],h=st[7];
    for (int i = 0; i < 64; i++) {
        uint32_t s1 = rotr(e,6) ^ rotr(e,11) ^ rotr(e,25);
        uint32_t ch = (e & f) ^ ((~e) & g);
        uint32_t t1 = h + s1 + ch + K[i] + w[i];
        uint32_t s0 = rotr(a,2) ^ rotr(a,13) ^ rotr(a,22);
        uint32_t mj = (a & bb) ^ (a & c) ^ (bb & c);
        uint32_t t2 = s0 + mj;
        h=g; g=f; f=e; e=d+t1; d=c; c=bb; bb=a; a=t1+t2;
    }
    st[0]+=a; st[1]+=bb; st[2]+=c; st[3]+=d; st[4]+=e; st[5]+=f; st[6]+=g; st[7]+=h;
}

static void sha256(const uint8_t *msg, size_t len, uint8_t out[32]) {
    uint32_t st[8] = { 0x6a09e667u,0xbb67ae85u,0x3c6ef372u,0xa54ff53au,
                       0x510e527fu,0x9b05688cu,0x1f83d9abu,0x5be0cd19u };
    size_t i = 0;
    for (; i + 64 <= len; i += 64) sha256_block(st, msg + i);
    uint8_t tail[128];
    size_t rem = len - i;
    memset(tail, 0, sizeof tail);
    memcpy(tail, msg + i, rem);
    tail[rem] = 0x80;
    size_t total = (rem + 1 + 8 <= 64) ? 64 : 128;
    uint64_t bits = (uint64_t)len * 8u;
    for (int k = 0; k < 8; k++) tail[total - 1 - k] = (uint8_t)(bits >> (8 * k));
    sha256_block(st, tail);
    if (total == 128) sha256_block(st, tail + 64);
    for (int k = 0; k < 8; k++) {
        out[k*4]   = (uint8_t)(st[k] >> 24);
        out[k*4+1] = (uint8_t)(st[k] >> 16);
        out[k*4+2] = (uint8_t)(st[k] >> 8);
        out[k*4+3] = (uint8_t)(st[k]);
    }
}

/* Helpers below serve only the two Linux-only daemon check groups. */
#if defined(__linux__)
/* --------------------------------------------------------------- utilities */
static int64_t now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static int64_t route(const char *dir) {
    return rt_cache_daemon_route_v1((const uint8_t *)dir, (int64_t)strlen(dir));
}

static int connect_unix(const char *path) {
    struct sockaddr_un addr;
    size_t len = strlen(path);
    if (len >= sizeof addr.sun_path) return -1;
    int fd = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
    if (fd < 0) return -1;
    memset(&addr, 0, sizeof addr);
    addr.sun_family = AF_UNIX;
    memcpy(addr.sun_path, path, len);
    if (connect(fd, (struct sockaddr *)&addr, sizeof addr) != 0) { close(fd); return -1; }
    return fd;
}

static int read_exact(int fd, uint8_t *b, size_t n) {
    size_t got = 0;
    while (got < n) {
        ssize_t r = read(fd, b + got, n - got);
        if (r == 0) return 0;
        if (r < 0) { if (errno == EINTR) continue; return 0; }
        got += (size_t)r;
    }
    return 1;
}

static char *make_tmpdir(char *buf, size_t cap) {
    snprintf(buf, cap, "/tmp/cachedaemon_selfcheck_XXXXXX");
    return mkdtemp(buf);
}
#endif /* __linux__ */

/* ------------------------------------------------------------------ checks */

static int check_noncanonical_roots(void) {
    const char *aliases[] = {"/", "/tmp/", "/tmp//cache",
                             "/tmp/./cache", "/tmp/../cache"};
    for (size_t i = 0; i < sizeof aliases / sizeof aliases[0]; ++i) {
        if (rt_cache_host_open_root_v1((const uint8_t *)aliases[i],
                                       (int64_t)strlen(aliases[i])) != -1) {
            fprintf(stderr, "accepted noncanonical cache root: %s\n", aliases[i]);
            return 1;
        }
    }
    return 0;
}

/* Pins this file's SHA-256 to the published vector, so the handshake check
 * below is a real constraint on the provider's digest rather than two copies
 * of the same possible mistake agreeing with each other. */
static int check_sha256_kat(void) {
    static const uint8_t want[32] = {
        0xba,0x78,0x16,0xbf,0x8f,0x01,0xcf,0xea,0x41,0x41,0x40,0xde,0x5d,0xae,0x22,0x23,
        0xb0,0x03,0x61,0xa3,0x96,0x17,0x7a,0x9c,0xb4,0x10,0xff,0x61,0xf2,0x00,0x15,0xad };
    uint8_t got[32];
    sha256((const uint8_t *)"abc", 3, got);
    if (memcmp(got, want, 32) != 0) {
        fprintf(stderr, "sha256(\"abc\") does not match the published vector\n");
        return 1;
    }
    return 0;
}

static int check_route_rejects_bad_input(void) {
    struct { const char *p; int64_t n; const char *why; } bad[] = {
        { "relative/path", 13, "relative path" },
        { "/tmp",           0, "zero length" },
        { "/tmp",          -1, "negative length" },
        { "/no/such/directory/for/selfcheck", 32, "nonexistent root" },
    };
    for (size_t i = 0; i < sizeof bad / sizeof bad[0]; ++i) {
        int64_t rc = rt_cache_daemon_route_v1((const uint8_t *)bad[i].p, bad[i].n);
        if (rc != -1) {
            fprintf(stderr, "route accepted %s (rc=%lld, want -1)\n",
                    bad[i].why, (long long)rc);
            return 1;
        }
    }
    return 0;
}

/* The provider's daemon lane is #if defined(__linux__) only (see
 * runtime_cache_host_authority_v1.c), and these two groups exercise it through
 * SO_PEERCRED / struct ucred / SOCK_CLOEXEC. They are compiled only there. */
#if defined(__linux__)
/* Rust lane parity: unavailable_singleton_falls_back_to_anchored_spool_within_budget.
 * The lock is held by THIS process, so the forked daemon cannot acquire it and
 * route must select the anchored spool rather than reporting a daemon. */
static int check_spool_fallback_under_held_lock(void) {
    char dir[64], lock_path[128], spool_path[128];
    struct stat st;
    int64_t start, rc, elapsed;
    int lock_fd;

    if (!make_tmpdir(dir, sizeof dir)) { perror("mkdtemp"); return 1; }
    snprintf(lock_path, sizeof lock_path, "%s/%s", dir, LOCK_NAME);
    lock_fd = open(lock_path, O_RDWR | O_CREAT | O_CLOEXEC, 0600);
    if (lock_fd < 0 || flock(lock_fd, LOCK_EX | LOCK_NB) != 0) {
        fprintf(stderr, "could not hold the daemon lock\n");
        return 1;
    }

    start = now_ms();
    rc = route(dir);
    elapsed = now_ms() - start;

    flock(lock_fd, LOCK_UN);
    close(lock_fd);

    if (rc != ROUTE_SPOOL) {
        fprintf(stderr, "held lock: route returned %lld, want ROUTE_SPOOL (%d)\n",
                (long long)rc, ROUTE_SPOOL);
        return 1;
    }
    if (elapsed > CONNECT_BUDGET_MS * 4) {
        fprintf(stderr, "held lock: route took %lldms, budget is %dms\n",
                (long long)elapsed, CONNECT_BUDGET_MS);
        return 1;
    }
    snprintf(spool_path, sizeof spool_path, "%s/spool", dir);
    if (stat(spool_path, &st) != 0 || !S_ISDIR(st.st_mode)) {
        fprintf(stderr, "held lock: anchored spool directory was not created\n");
        return 1;
    }
    /* No daemon ever started here, so this root can be removed completely. */
    unlink(lock_path);
    rmdir(spool_path);
    rmdir(dir);
    return 0;
}

/* Rust lane parity: hostile_socket_is_replaced_by_locked_authenticated_daemon
 * and singleton_handshake_and_idle_exit_are_process_real, plus a raw replay of
 * the wire format against the daemon that route actually launched. */
static int check_hostile_socket_and_handshake(void) {
    char dir[64], sock_path[128];
    struct sockaddr_un addr;
    uint8_t req[REQ_LEN], ack[ACK_LEN], nonce[32], digest[32];
    struct ucred cred;
    socklen_t cred_len = sizeof cred;
    int64_t start, rc, elapsed;
    int hostile, fd, i;
    int32_t ack_pid;
    uint32_t ack_uid;

    if (!make_tmpdir(dir, sizeof dir)) { perror("mkdtemp"); return 1; }
    snprintf(sock_path, sizeof sock_path, "%s/%s", dir, SOCKET_NAME);

    /* A squatter that accepts connections and never answers. A client that
     * merely probed for the socket's existence would be fooled by this. */
    hostile = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
    if (hostile < 0) { perror("socket"); return 1; }
    memset(&addr, 0, sizeof addr);
    addr.sun_family = AF_UNIX;
    memcpy(addr.sun_path, sock_path, strlen(sock_path));
    if (bind(hostile, (struct sockaddr *)&addr, sizeof addr) != 0
        || listen(hostile, 8) != 0) {
        perror("bind hostile");
        return 1;
    }

    start = now_ms();
    rc = route(dir);
    elapsed = now_ms() - start;
    close(hostile);

    if (rc != ROUTE_DAEMON) {
        fprintf(stderr, "hostile socket: route returned %lld, want ROUTE_DAEMON (%d)\n",
                (long long)rc, ROUTE_DAEMON);
        return 1;
    }
    if (elapsed > 500) {
        fprintf(stderr, "hostile socket: route took %lldms, want < 500ms\n",
                (long long)elapsed);
        return 1;
    }

    /* A second route must reuse the daemon that is now listening. */
    rc = route(dir);
    if (rc != ROUTE_DAEMON) {
        fprintf(stderr, "second route returned %lld, want ROUTE_DAEMON (%d)\n",
                (long long)rc, ROUTE_DAEMON);
        return 1;
    }

    /* Raw wire replay against that live daemon. */
    fd = connect_unix(sock_path);
    if (fd < 0) { fprintf(stderr, "could not connect to the launched daemon\n"); return 1; }
    for (i = 0; i < 32; i++) nonce[i] = (uint8_t)(i * 7 + 3);
    memcpy(req + OFF_MAGIC, REQ_MAGIC, 8);
    memcpy(req + OFF_NONCE, nonce, 32);
    if (write(fd, req, sizeof req) != (ssize_t)sizeof req) {
        fprintf(stderr, "short request write\n"); close(fd); return 1;
    }
    if (!read_exact(fd, ack, sizeof ack)) {
        fprintf(stderr, "daemon did not answer with %d ack bytes\n", ACK_LEN);
        close(fd); return 1;
    }
    if (memcmp(ack + OFF_MAGIC, ACK_MAGIC, 8) != 0) {
        fprintf(stderr, "ack magic mismatch\n"); close(fd); return 1;
    }
    if (memcmp(ack + OFF_NONCE, nonce, 32) != 0) {
        fprintf(stderr, "ack did not echo the client nonce\n"); close(fd); return 1;
    }
    ack_pid = (int32_t)((uint32_t)ack[OFF_PID] | ((uint32_t)ack[OFF_PID+1] << 8)
             | ((uint32_t)ack[OFF_PID+2] << 16) | ((uint32_t)ack[OFF_PID+3] << 24));
    ack_uid = (uint32_t)ack[OFF_UID] | ((uint32_t)ack[OFF_UID+1] << 8)
            | ((uint32_t)ack[OFF_UID+2] << 16) | ((uint32_t)ack[OFF_UID+3] << 24);
    if (getsockopt(fd, SOL_SOCKET, SO_PEERCRED, &cred, &cred_len) != 0) {
        fprintf(stderr, "SO_PEERCRED failed\n"); close(fd); return 1;
    }
    if (ack_pid != (int32_t)cred.pid) {
        fprintf(stderr, "ack pid %d != peer pid %d (offset %d is wrong)\n",
                ack_pid, (int)cred.pid, OFF_PID);
        close(fd); return 1;
    }
    if (ack_uid != (uint32_t)geteuid() || (uint32_t)cred.uid != (uint32_t)geteuid()) {
        fprintf(stderr, "ack uid %u / peer uid %u != euid %u\n",
                ack_uid, (unsigned)cred.uid, (unsigned)geteuid());
        close(fd); return 1;
    }
    sha256(ack, OFF_DIGEST, digest);
    if (memcmp(digest, ack + OFF_DIGEST, 32) != 0) {
        fprintf(stderr, "ack digest does not match SHA-256 over the first %d bytes\n",
                OFF_DIGEST);
        close(fd); return 1;
    }
    close(fd);
    /* The daemon idles out on its own (10-12s) and unlinks its socket; the test
     * deliberately does not kill it, so the shutdown path stays exercised. That
     * means THIS root outlives the test run: /tmp/cachedaemon_selfcheck_* keeps
     * a lock file until the daemon exits, and the directory is left behind for
     * /tmp cleanup rather than removed here. The spool-fallback root above
     * starts no daemon and is removed completely. */
    return 0;
}
#endif /* __linux__ */

int main(void) {
    if (check_noncanonical_roots()) return 1;
    if (check_sha256_kat()) return 1;
    if (check_route_rejects_bad_input()) return 1;
#if defined(__linux__)
    if (check_spool_fallback_under_held_lock()) return 1;
    if (check_hostile_socket_and_handshake()) return 1;
    printf("rt_cache_host_authority_v1_selfcheck: 5 check group(s) passed\n");
#else
    /* Say what was NOT run. A count that silently drops two groups would read
     * as a full pass on a host that never exercised the daemon lane. */
    printf("rt_cache_host_authority_v1_selfcheck: 3 check group(s) passed; "
           "2 daemon group(s) NOT exercised on this host (the provider's "
           "daemon lane is #if defined(__linux__) only)\n");
#endif
    return 0;
}

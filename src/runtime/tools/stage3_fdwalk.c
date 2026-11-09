/* stage3_fdwalk — pinned native helper for the Stage-3 shared runner on hosts
 * without procfs magic links (Darwin). Two primitives, nothing else:
 *
 *   walk --dir-fd N --rel a/b/c
 *       Opens every component relative to the HELD directory descriptor N
 *       with openat(O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC) (leaf without
 *       O_DIRECTORY), fstat()s the leaf, and prints its identity
 *       (schema/kind/dev/ino/mode/size/nlink/sha256). No component is ever
 *       resolved as a path from the root: the prefix cannot be swapped
 *       between check and use (same contract as the Linux runner's
 *       /proc/self/fd/N/<leaf> walk).
 *
 *   exec (--exec-fd K | --dir-fd N --rel path) [--sha256 HEX] -- argv0 [arg ...]
 *       Executes the HELD executable descriptor. Linux: fexecve(). Darwin has
 *       no fexecve and cannot execute through /dev/fd, so the helper does
 *       verify-by-fd: fstat(fd) -> F_GETPATH(fd) -> lstat(path) must not be a
 *       symlink -> stat(path) must have the same st_dev/st_ino as the held fd
 *       -> execve(path), all in one native function with no interpreter in
 *       between. The residual window is the kernel namei inside execve()
 *       after our stat(); see RESIDUAL WINDOW below.
 *
 *   --selftest
 *       Runs the pure decision logic against the vector table shared with the
 *       pure-Simple twin std.common.stage3_fdwalk_policy (twin-vectors marker
 *       `stage3_fdwalk_v1`). The Simple spec pins both tables byte-identical.
 *
 * RESIDUAL WINDOW (Darwin exec). Between stat(path) and the execve() namei a
 * writer with permission on a directory component of `path` could rename a
 * different file into place. Why it is acceptable for the bootstrap lane and
 * where it is not:
 *   - the walked prefix was opened component-by-component with O_NOFOLLOW
 *     from a descriptor the CALLER already held, so no symlink was followed
 *     and the path F_GETPATH reports names the held vnode at check time;
 *   - the bootstrap tree is owned by the invoking uid; same-uid writers are
 *     already trusted on Darwin (runtime_process_owned.c, OWNED_DARWIN_PIN:
 *     "a same-UID process can still chmod and rewrite the snapshot");
 *   - a foreign-uid writer would need write permission on an ancestor
 *     directory of the executable, which the Stage-3 directory snapshot
 *     already rejects (every ancestor is lstat-bound and uid-checked).
 *   It is NOT equivalent to Linux fexecve(): an attacker who can write an
 *   ancestor directory wins the race with probability > 0. Where that threat
 *   model applies, use the private 0700 snapshot exec already implemented in
 *   runtime_sosix_darwin_image_private.h instead of this helper's exec.
 *
 * Pure-Simple twin: src/lib/common/stage3_fdwalk_policy.spl
 * Spec:             test/01_unit/lib/common/stage3_fdwalk_policy_spec.spl
 * Darwin spec:      test/01_unit/bootstrap/stage3_fdwalk_darwin_spec.shs
 * Gate:             scripts/check/check-stage3-fdwalk-helper.shs
 * Build: clang -std=c11 -Wall -Wextra stage3_fdwalk.c -o stage3_fdwalk   (never GCC)
 */
#define _DARWIN_C_SOURCE
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

extern char **environ;

/* Exit codes. Exact values are part of the runner contract. */
enum {
    FDWALK_OK = 0,
    FDWALK_USAGE = 64,
    FDWALK_INVALID_COMPONENT = 65,
    FDWALK_MISSING = 66,
    FDWALK_OPEN_FAILED = 67,
    FDWALK_SYMLINK = 68,
    FDWALK_NOT_REGULAR = 69,
    FDWALK_HASH_MISMATCH = 70,
    FDWALK_EXEC_REJECTED = 71,
    FDWALK_EXEC_FAILED = 126
};

/* ---- pure decision logic (twin: std.common.stage3_fdwalk_policy) -------- */

#define FDWALK_COMPONENT_MAX 255
#define FDWALK_RELATIVE_MAX 16384
#define FDWALK_PARTS_MAX 256

/* twin: fdwalk_component_ok */
static int fdwalk_component_ok(const char *part, size_t len) {
    if (len == 0 || len > FDWALK_COMPONENT_MAX) return 0;
    if (len == 1 && part[0] == '.') return 0;
    if (len == 2 && part[0] == '.' && part[1] == '.') return 0;
    for (size_t i = 0; i < len; i++) {
        char c = part[i];
        int ok = (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z') ||
                 (c >= '0' && c <= '9') || c == '_' || c == '.' || c == '-';
        if (!ok) return 0;
    }
    return 1;
}

/* twin: fdwalk_split_relative. Returns FDWALK_OK or FDWALK_INVALID_COMPONENT.
 * parts[] receive pointers into `rel` and lens[] their lengths. */
static int fdwalk_split_relative(const char *rel, const char *parts[],
                                 size_t lens[], size_t *count) {
    *count = 0;
    if (!rel || rel[0] == 0 || rel[0] == '/') return FDWALK_INVALID_COMPONENT;
    size_t total = strlen(rel);
    if (total > FDWALK_RELATIVE_MAX) return FDWALK_INVALID_COMPONENT;
    size_t start = 0;
    for (size_t i = 0; i <= total; i++) {
        if (rel[i] == '/' || rel[i] == 0) {
            if (*count >= FDWALK_PARTS_MAX) return FDWALK_INVALID_COMPONENT;
            if (!fdwalk_component_ok(rel + start, i - start))
                return FDWALK_INVALID_COMPONENT;
            parts[*count] = rel + start;
            lens[*count] = i - start;
            (*count)++;
            start = i + 1;
        }
    }
    return FDWALK_OK;
}

/* twin: fdwalk_exec_verdict. Verdict ordinals are the twin's enum order. */
enum {
    FDWALK_VERDICT_ADMIT = 0,
    FDWALK_VERDICT_NOT_REGULAR = 1,
    FDWALK_VERDICT_UNLINKED = 2,
    FDWALK_VERDICT_REPATH_MISSING = 3,
    FDWALK_VERDICT_REPATH_SYMLINK = 4,
    FDWALK_VERDICT_IDENTITY_MISMATCH = 5
};
static int fdwalk_exec_verdict(int held_regular, uint64_t held_nlink,
                               uint64_t held_dev, uint64_t held_ino,
                               int repath_present, int repath_symlink,
                               uint64_t repath_dev, uint64_t repath_ino) {
    if (!held_regular) return FDWALK_VERDICT_NOT_REGULAR;
    if (held_nlink == 0) return FDWALK_VERDICT_UNLINKED;
    if (!repath_present) return FDWALK_VERDICT_REPATH_MISSING;
    if (repath_symlink) return FDWALK_VERDICT_REPATH_SYMLINK;
    if (held_dev != repath_dev || held_ino != repath_ino)
        return FDWALK_VERDICT_IDENTITY_MISMATCH;
    return FDWALK_VERDICT_ADMIT;
}

/* ---- twin-vectors: stage3_fdwalk_v1 (byte-identical in the .spl twin) ---- */
/* component|<part>|<ok 0/1> ; verdict|reg|nlink|hdev|hino|present|symlink|rdev|rino|<verdict> */
static const char *const fdwalk_vectors[] = {
    "component|bin|1",
    "component|stage3-shared-runner.pl|1",
    "component|a.b_c-d|1",
    "component||0",
    "component|.|0",
    "component|..|0",
    "component|a b|0",
    "component|a/b|0",
    "component|a\\b|0",
    "component|-|1",
    "component|...|1",
    "relative|bin/simple|2",
    "relative|/bin/simple|0",
    "relative|bin//simple|0",
    "relative|bin/./simple|0",
    "relative|bin/../simple|0",
    "relative|simple|1",
    "relative||0",
    "verdict|1|1|7|42|1|0|7|42|0",
    "verdict|0|1|7|42|1|0|7|42|1",
    "verdict|1|0|7|42|1|0|7|42|2",
    "verdict|1|1|7|42|0|0|0|0|3",
    "verdict|1|1|7|42|1|1|7|42|4",
    "verdict|1|1|7|42|1|0|7|43|5",
    "verdict|1|1|7|42|1|0|8|42|5",
    "verdict|1|2|7|42|1|0|7|42|0",
};
/* ---- end twin-vectors ---- */

static int field(const char *row, int index, char *out, size_t cap) {
    const char *p = row;
    for (int i = 0; i < index; i++) {
        p = strchr(p, '|');
        if (!p) return 0;
        p++;
    }
    const char *end = strchr(p, '|');
    size_t len = end ? (size_t)(end - p) : strlen(p);
    if (len >= cap) return 0;
    memcpy(out, p, len);
    out[len] = 0;
    return 1;
}

static int selftest(void) {
    int failures = 0;
    size_t count = sizeof(fdwalk_vectors) / sizeof(fdwalk_vectors[0]);
    for (size_t i = 0; i < count; i++) {
        const char *row = fdwalk_vectors[i];
        char kind[16], a[64], f[12][24];
        if (!field(row, 0, kind, sizeof kind)) { failures++; continue; }
        if (!strcmp(kind, "component")) {
            if (!field(row, 1, a, sizeof a) || !field(row, 2, f[0], sizeof f[0])) { failures++; continue; }
            int got = fdwalk_component_ok(a, strlen(a));
            if (got != atoi(f[0])) { printf("selftest: FAIL %s got=%d\n", row, got); failures++; }
        } else if (!strcmp(kind, "relative")) {
            if (!field(row, 1, a, sizeof a) || !field(row, 2, f[0], sizeof f[0])) { failures++; continue; }
            const char *parts[FDWALK_PARTS_MAX]; size_t lens[FDWALK_PARTS_MAX]; size_t n;
            int rc = fdwalk_split_relative(a, parts, lens, &n);
            size_t got = rc == FDWALK_OK ? n : 0;
            if (got != (size_t)atoi(f[0])) { printf("selftest: FAIL %s got=%zu\n", row, got); failures++; }
        } else if (!strcmp(kind, "verdict")) {
            for (int k = 0; k < 9; k++)
                if (!field(row, 1 + k, f[k], sizeof f[k])) { failures++; goto next; }
            int got = fdwalk_exec_verdict(atoi(f[0]), strtoull(f[1], NULL, 10),
                strtoull(f[2], NULL, 10), strtoull(f[3], NULL, 10), atoi(f[4]),
                atoi(f[5]), strtoull(f[6], NULL, 10), strtoull(f[7], NULL, 10));
            if (got != atoi(f[8])) { printf("selftest: FAIL %s got=%d\n", row, got); failures++; }
        } else {
            failures++;
        }
    next:;
    }
    printf("selftest: %zu vector(s), %d failure(s)\n", count, failures);
    return failures ? 1 : 0;
}

/* ---- streaming SHA-256 (self-contained; no CommonCrypto/OpenSSL) --------- */
typedef struct { uint32_t h[8]; uint8_t buf[64]; size_t buf_len; uint64_t total; } Sha256;
static const uint32_t sha256_k[64] = {
    0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
    0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
    0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
    0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
    0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
    0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
    0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
    0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2 };
static uint32_t rotr(uint32_t v, unsigned s) { return (v >> s) | (v << (32 - s)); }
static void sha256_block(uint32_t st[8], const uint8_t b[64]) {
    uint32_t w[64];
    for (int i = 0; i < 16; i++)
        w[i] = ((uint32_t)b[i*4] << 24) | ((uint32_t)b[i*4+1] << 16) | ((uint32_t)b[i*4+2] << 8) | b[i*4+3];
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = rotr(w[i-15], 7) ^ rotr(w[i-15], 18) ^ (w[i-15] >> 3);
        uint32_t s1 = rotr(w[i-2], 17) ^ rotr(w[i-2], 19) ^ (w[i-2] >> 10);
        w[i] = w[i-16] + s0 + w[i-7] + s1;
    }
    uint32_t a=st[0],bb=st[1],c=st[2],d=st[3],e=st[4],f=st[5],g=st[6],h=st[7];
    for (int i = 0; i < 64; i++) {
        uint32_t t1 = h + (rotr(e,6)^rotr(e,11)^rotr(e,25)) + ((e&f)^(~e&g)) + sha256_k[i] + w[i];
        uint32_t t2 = (rotr(a,2)^rotr(a,13)^rotr(a,22)) + ((a&bb)^(a&c)^(bb&c));
        h=g; g=f; f=e; e=d+t1; d=c; c=bb; bb=a; a=t1+t2;
    }
    st[0]+=a; st[1]+=bb; st[2]+=c; st[3]+=d; st[4]+=e; st[5]+=f; st[6]+=g; st[7]+=h;
}
static void sha256_init(Sha256 *s) {
    static const uint32_t iv[8] = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
    memcpy(s->h, iv, sizeof iv); s->buf_len = 0; s->total = 0;
}
static void sha256_update(Sha256 *s, const uint8_t *p, size_t n) {
    s->total += n;
    while (n) {
        size_t take = 64 - s->buf_len; if (take > n) take = n;
        memcpy(s->buf + s->buf_len, p, take); s->buf_len += take; p += take; n -= take;
        if (s->buf_len == 64) { sha256_block(s->h, s->buf); s->buf_len = 0; }
    }
}
static void sha256_final(Sha256 *s, char hex[65]) {
    uint64_t bits = s->total * 8; uint8_t pad = 0x80;
    sha256_update(s, &pad, 1);
    uint8_t zero = 0;
    while (s->buf_len != 56) sha256_update(s, &zero, 1);
    uint8_t len[8]; for (int i = 0; i < 8; i++) len[i] = (uint8_t)(bits >> (56 - 8*i));
    sha256_update(s, len, 8);
    static const char *digits = "0123456789abcdef";
    for (int i = 0; i < 8; i++) for (int j = 0; j < 4; j++) {
        uint8_t byte = (uint8_t)(s->h[i] >> (24 - 8*j));
        hex[i*8 + j*2] = digits[byte >> 4]; hex[i*8 + j*2 + 1] = digits[byte & 15];
    }
    hex[64] = 0;
}
static int hash_fd(int fd, char hex[65]) {
    Sha256 s; sha256_init(&s); uint8_t buf[65536];
    if (lseek(fd, 0, SEEK_SET) == (off_t)-1) return -1;
    for (;;) {
        ssize_t n = read(fd, buf, sizeof buf);
        if (n < 0) { if (errno == EINTR) continue; return -1; }
        if (n == 0) break;
        sha256_update(&s, buf, (size_t)n);
    }
    if (lseek(fd, 0, SEEK_SET) == (off_t)-1) return -1;
    sha256_final(&s, hex);
    return 0;
}

/* ---- fd-relative walk ---------------------------------------------------- */

static int usage(void) {
    fputs("usage: stage3_fdwalk walk --dir-fd N --rel REL\n"
          "       stage3_fdwalk exec (--exec-fd K | --dir-fd N --rel REL) [--sha256 HEX] -- ARGV0 [ARG ...]\n"
          "       stage3_fdwalk --selftest\n", stderr);
    return FDWALK_USAGE;
}

static int parse_fd(const char *text, int *out) {
    if (!text || !*text) return 0;
    long v = 0;
    for (const char *p = text; *p; p++) {
        if (*p < '0' || *p > '9' || v > 100000) return 0;
        v = v * 10 + (*p - '0');
    }
    *out = (int)v;
    return 1;
}

/* Walks `rel` from `dir_fd`; returns the leaf descriptor (>= 0) or a negative
 * FDWALK_* code. Every component except the last must be a directory. */
static int walk_from(int dir_fd, const char *rel) {
    const char *parts[FDWALK_PARTS_MAX]; size_t lens[FDWALK_PARTS_MAX]; size_t count;
    if (fdwalk_split_relative(rel, parts, lens, &count) != FDWALK_OK)
        return -FDWALK_INVALID_COMPONENT;
    struct stat st;
    if (fstat(dir_fd, &st) != 0 || !S_ISDIR(st.st_mode)) return -FDWALK_OPEN_FAILED;
    int current = fcntl(dir_fd, F_DUPFD_CLOEXEC, 3);
    if (current < 0) return -FDWALK_OPEN_FAILED;
    for (size_t i = 0; i < count; i++) {
        char name[FDWALK_COMPONENT_MAX + 1];
        memcpy(name, parts[i], lens[i]); name[lens[i]] = 0;
        int flags = O_RDONLY | O_NOFOLLOW | O_CLOEXEC;
        if (i + 1 < count) flags |= O_DIRECTORY;
        int next = openat(current, name, flags);
        if (next < 0) {
            int err = errno;
            close(current);
            if (err == ENOENT) return -FDWALK_MISSING;
            /* O_NOFOLLOW on a symlink: ELOOP (Linux, Darwin); some BSDs EMLINK */
            if (err == ELOOP || err == EMLINK) return -FDWALK_SYMLINK;
            return -FDWALK_OPEN_FAILED;
        }
        close(current);
        current = next;
    }
    return current;
}

static int print_identity(int fd) {
    struct stat st;
    if (fstat(fd, &st) != 0) return FDWALK_OPEN_FAILED;
    const char *kind = S_ISREG(st.st_mode) ? "regular" : S_ISDIR(st.st_mode) ? "directory" : "other";
    printf("schema=simple-stage3-fdwalk-v1\nkind=%s\ndev=%llu\nino=%llu\nmode=%o\nsize=%lld\nnlink=%llu\n",
           kind, (unsigned long long)st.st_dev, (unsigned long long)st.st_ino,
           (unsigned)(st.st_mode & 07777), (long long)st.st_size,
           (unsigned long long)st.st_nlink);
    if (S_ISREG(st.st_mode)) {
        char hex[65];
        if (hash_fd(fd, hex) != 0) return FDWALK_OPEN_FAILED;
        printf("sha256=%s\n", hex);
    }
    return fflush(stdout) == 0 ? FDWALK_OK : FDWALK_OPEN_FAILED;
}

/* ---- exec by held descriptor --------------------------------------------- */

static int exec_held(int fd, char **argv) {
    struct stat held;
    if (fstat(fd, &held) != 0) return FDWALK_OPEN_FAILED;
    if (!S_ISREG(held.st_mode)) return FDWALK_NOT_REGULAR;
#if defined(__APPLE__)
    /* verify-by-fd: the held vnode's current path, re-checked immediately
     * before the exec. Residual window documented in the file header. */
    char path[PATH_MAX];
    if (fcntl(fd, F_GETPATH, path) == -1) return FDWALK_EXEC_REJECTED;
    struct stat link_st, re_st;
    int repath_present = 1, repath_symlink = 0;
    if (lstat(path, &link_st) != 0) repath_present = 0;
    else if (S_ISLNK(link_st.st_mode)) repath_symlink = 1;
    if (repath_present && !repath_symlink && stat(path, &re_st) != 0) repath_present = 0;
    int verdict = fdwalk_exec_verdict(1, (uint64_t)held.st_nlink,
        (uint64_t)held.st_dev, (uint64_t)held.st_ino, repath_present, repath_symlink,
        repath_present ? (uint64_t)re_st.st_dev : 0, repath_present ? (uint64_t)re_st.st_ino : 0);
    if (verdict != FDWALK_VERDICT_ADMIT) {
        fprintf(stderr, "stage3_fdwalk: exec rejected: verdict=%d\n", verdict);
        return FDWALK_EXEC_REJECTED;
    }
    fcntl(fd, F_SETFD, FD_CLOEXEC);
    execve(path, argv, environ);
    return FDWALK_EXEC_FAILED;
#else
    int verdict = fdwalk_exec_verdict(1, (uint64_t)held.st_nlink, (uint64_t)held.st_dev,
        (uint64_t)held.st_ino, 1, 0, (uint64_t)held.st_dev, (uint64_t)held.st_ino);
    if (verdict != FDWALK_VERDICT_ADMIT) return FDWALK_EXEC_REJECTED;
    fexecve(fd, argv, environ);
    return FDWALK_EXEC_FAILED;
#endif
}

static int hex_sha_ok(const char *hex) {
    if (!hex || strlen(hex) != 64) return 0;
    for (const char *p = hex; *p; p++)
        if (!((*p >= '0' && *p <= '9') || (*p >= 'a' && *p <= 'f'))) return 0;
    return 1;
}

int main(int argc, char **argv) {
    if (argc == 2 && !strcmp(argv[1], "--selftest")) return selftest();
    if (argc < 2) return usage();
    const char *command = argv[1];
    int dir_fd = -1, exec_fd = -1; const char *rel = NULL, *sha = NULL; int i = 2;
    for (; i < argc; i++) {
        if (!strcmp(argv[i], "--")) { i++; break; }
        if (!strcmp(argv[i], "--dir-fd") && i + 1 < argc) { if (!parse_fd(argv[++i], &dir_fd)) return usage(); }
        else if (!strcmp(argv[i], "--exec-fd") && i + 1 < argc) { if (!parse_fd(argv[++i], &exec_fd)) return usage(); }
        else if (!strcmp(argv[i], "--rel") && i + 1 < argc) rel = argv[++i];
        else if (!strcmp(argv[i], "--sha256") && i + 1 < argc) sha = argv[++i];
        else return usage();
    }
    if (sha && !hex_sha_ok(sha)) return usage();
    if (!strcmp(command, "walk")) {
        if (dir_fd < 0 || !rel || i != argc) return usage();
        int fd = walk_from(dir_fd, rel);
        if (fd < 0) return -fd;
        int rc = print_identity(fd);
        close(fd);
        return rc;
    }
    if (!strcmp(command, "exec")) {
        if (i >= argc) return usage();
        int fd;
        if (exec_fd >= 0) { if (dir_fd >= 0 || rel) return usage(); fd = fcntl(exec_fd, F_DUPFD_CLOEXEC, 3); if (fd < 0) return FDWALK_OPEN_FAILED; }
        else { if (dir_fd < 0 || !rel) return usage(); fd = walk_from(dir_fd, rel); if (fd < 0) return -fd; }
        if (sha) {
            char hex[65];
            if (hash_fd(fd, hex) != 0) return FDWALK_OPEN_FAILED;
            if (strcmp(hex, sha) != 0) { fputs("stage3_fdwalk: executable hash mismatch\n", stderr); return FDWALK_HASH_MISMATCH; }
        }
        int rc = exec_held(fd, argv + i);
        fprintf(stderr, "stage3_fdwalk: exec failed: %s\n", strerror(errno));
        return rc;
    }
    return usage();
}

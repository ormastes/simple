/* Levelled vector provider: exhaustive parity of one DSO (one admitted level)
 * against a scalar oracle, through the real wire ABI (query -> apply).
 *   vector_level_parity_selftest <provider.{so,dylib,dll}> [quick]
 * Covers, for bitmap AND/OR and HTTP FIND_BYTE/FIND_CRLF:
 *   - every length 0..2*64+3 (bitmap: words, HTTP: bytes)
 *   - misaligned starts (bitmap: every word offset in a 64-byte block for the
 *     output, independent left/right offsets; HTTP: every byte offset 0..63)
 *   - spans ending exactly at a PROT_NONE / PAGE_NOACCESS guard page, so any
 *     read or write past the span faults instead of passing silently
 *   - every hit position, a later second hit (first one must win), distractor
 *     backgrounds, CRLF across every 64-byte block edge, CR at the last span
 *     byte with LF just outside (must not match), CR CR LF across an edge
 *   - max span: 1 GiB reserved, only the first pages committed (an over-read
 *     faults), hits near the start; MAX+1 must be RANGE_INVALID
 * A level-0 DSO must refuse every in-range call with FEATURE_UNAVAILABLE and
 * leave outputs untouched. "quick" trims offsets for slow emulators. */
#define _GNU_SOURCE 1
#include "../simple_vector_kernel_abi_v1.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _WIN32
#include <windows.h>
#define LOAD(p) ((void *)LoadLibraryA(p))
#define SYM(l, n) ((void *)GetProcAddress((HMODULE)(l), n))
#else
#include <dlfcn.h>
#include <sys/mman.h>
#include <unistd.h>
#define LOAD(p) dlopen(p, RTLD_NOW | RTLD_LOCAL)
#define SYM(l, n) dlsym(l, n)
#endif

#define FAIL(...) do { fprintf(stderr, "FAIL line=%d level=%d: ", __LINE__, level); \
    fprintf(stderr, __VA_ARGS__); fputc('\n', stderr); exit(1); } while (0)
#define MAX_LEN (2u * 64u + 3u)

static simple_vector_apply_fn_v1 apply;
static int64_t handle;
static int level;
static unsigned long long cases;

static uint32_t call(uint32_t op, const void *a, uint64_t n, const void *b, void *out, uint64_t arg, int64_t *found) {
    uint8_t q[64] = {0}, r[24];
    simple_vector_wr32(q, 64); simple_vector_wr32(q + 4, op);
    simple_vector_wr64(q + 8, n ? (uintptr_t)a : 0); simple_vector_wr64(q + 16, n);
    if (op <= 2) {
        simple_vector_wr64(q + 24, n ? (uintptr_t)b : 0); simple_vector_wr64(q + 32, n);
        simple_vector_wr64(q + 40, n ? (uintptr_t)out : 0); simple_vector_wr64(q + 48, n);
    }
    simple_vector_wr64(q + 56, arg);
    if (apply(handle, (int64_t)(uintptr_t)q, (int64_t)(uintptr_t)r) != 0) FAIL("apply transport error");
    if (found) *found = (int64_t)simple_vector_rd64(r + 16);
    ++cases;
    return simple_vector_rd32(r + 4);
}

/* Region of `usable` bytes immediately followed by an inaccessible page;
 * with commit < usable only the first `commit` bytes are readable. */
static size_t page_size(void) {
#ifdef _WIN32
    SYSTEM_INFO si; GetSystemInfo(&si); return si.dwPageSize;
#else
    return (size_t)sysconf(_SC_PAGESIZE);
#endif
}
static uint8_t *guarded(size_t usable, size_t commit) {
    const size_t pg = page_size();
    usable = (usable + pg - 1) / pg * pg;
    commit = (commit + pg - 1) / pg * pg;
#ifdef _WIN32
    uint8_t *p = VirtualAlloc(NULL, usable + pg, MEM_RESERVE, PAGE_NOACCESS);
    if (!p || !VirtualAlloc(p, commit, MEM_COMMIT, PAGE_READWRITE)) return NULL;
#else
    uint8_t *p = mmap(NULL, usable + pg, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (p == MAP_FAILED || mprotect(p, commit, PROT_READ | PROT_WRITE) != 0) return NULL;
#endif
    return p;
}

/* ---- CPUID oracle: x86-64 microarchitecture level, decoded independently of
 * the dispatcher (named features, not its bit masks). -1 = not x86-64. ---- */
#if defined(__x86_64__) && (defined(__GNUC__) || defined(__clang__))
#include <cpuid.h>
static int cpuid_level(void) {
    unsigned a, b, c1 = 0, d1 = 0, b7 = 0, c7, d7, ce = 0, de;
    if (!__get_cpuid(1, &a, &b, &c1, &d1)) return 0;
    if (__get_cpuid_max(0, 0) >= 7) __cpuid_count(7, 0, a, b7, c7, d7);
    if (__get_cpuid(0x80000001u, &a, &b, &ce, &de) == 0) ce = 0;
#define HAS(reg, bit) (((reg) >> (bit)) & 1u)
    const int sse3 = HAS(c1, 0), ssse3 = HAS(c1, 9), fma = HAS(c1, 12), cx16 = HAS(c1, 13),
        sse41 = HAS(c1, 19), sse42 = HAS(c1, 20), movbe = HAS(c1, 22), popcnt = HAS(c1, 23),
        xsave = HAS(c1, 26), osxsave = HAS(c1, 27), avx = HAS(c1, 28), f16c = HAS(c1, 29),
        bmi1 = HAS(b7, 3), avx2 = HAS(b7, 5), bmi2 = HAS(b7, 8), avx512f = HAS(b7, 16),
        avx512dq = HAS(b7, 17), avx512cd = HAS(b7, 28), avx512bw = HAS(b7, 30), avx512vl = HAS(b7, 31),
        lahf = HAS(ce, 0), lzcnt = HAS(ce, 5);
#undef HAS
    if (!(sse3 && ssse3 && cx16 && sse41 && sse42 && popcnt && lahf)) return 1;
    if (!(fma && movbe && xsave && osxsave && avx && f16c && bmi1 && avx2 && bmi2 && lzcnt)) return 2;
    unsigned lo, hi;
    __asm__ volatile("xgetbv" : "=a"(lo), "=d"(hi) : "c"(0));
    if ((lo & 0x6u) != 0x6u) return 2;
    if (!(avx512f && avx512dq && avx512cd && avx512bw && avx512vl)) return 3;
#if defined(__APPLE__)
    return 3; /* XCR0 ZMM state is lazy on macOS: no independent oracle for L4 */
#else
    return (lo & 0xe6u) == 0xe6u ? 4 : 3;
#endif
}
#else
static int cpuid_level(void) { return -1; }
#endif

/* ---- scalar oracle ---- */
static int64_t oracle_find(const uint8_t *p, size_t n, int crlf, uint8_t needle) {
    for (size_t i = 0; i < n; i++)
        if (crlf ? (i + 1 < n && p[i] == '\r' && p[i + 1] == '\n') : p[i] == needle) return (int64_t)i;
    return -1;
}

static uint32_t want_ok(void) { return level > 0 ? SIMPLE_VECTOR_OK : SIMPLE_VECTOR_FEATURE_UNAVAILABLE; }

/* ---- bitmap ---- */
static void bitmap_case(uint32_t op, const uint32_t *a, const uint32_t *b, uint32_t *o, size_t n, int canaries) {
    if (canaries) o[-1] = 0xdeadbeefu;
    for (size_t i = 0; i < n; i++) o[i] = 0xcdcdcdcdu;
    if (canaries) o[n] = 0xfeedfaceu;
    const uint32_t st = call(op, a, n * 4, b, o, 0, NULL);
    if (st != want_ok()) FAIL("bitmap op=%u n=%zu status=%u", op, n, st);
    for (size_t i = 0; i < n; i++) {
        const uint32_t e = level > 0 ? (op == 1 ? a[i] & b[i] : a[i] | b[i]) : 0xcdcdcdcdu;
        if (o[i] != e) FAIL("bitmap op=%u n=%zu i=%zu got=%08x want=%08x", op, n, i, o[i], e);
    }
    if (canaries && (o[-1] != 0xdeadbeefu || o[n] != 0xfeedfaceu)) FAIL("bitmap op=%u n=%zu wrote outside span", op, n);
}

static void bitmap_suite(int quick) {
    const size_t cap = 64 + MAX_LEN + 64;
    uint32_t *a = malloc(4 * cap), *b = malloc(4 * cap), *o = malloc(4 * cap);
    if (!a || !b || !o) FAIL("oom");
    for (size_t i = 0; i < cap; i++) { a[i] = (uint32_t)(i * 2654435761u) ^ 0x0f0f0f0fu; b[i] = (uint32_t)(i * 40503u) ^ 0xa5a55a5au; }
    static const size_t in_off_full[] = {0, 1, 7, 15}, in_off_quick[] = {0, 15};
    const size_t *in_off = quick ? in_off_quick : in_off_full;
    const size_t n_in = quick ? 2 : 4, out_step = quick ? 5 : 1;
    for (size_t n = 0; n <= MAX_LEN; n++)
        for (uint32_t op = 1; op <= 2; op++)
            for (size_t ia = 0; ia < n_in; ia++)
                for (size_t ib = 0; ib < n_in; ib++)
                    for (size_t oo = 0; oo < 16; oo += out_step)
                        /* +16 keeps o[-1] inside the allocation; a,b,o never overlap */
                        bitmap_case(op, a + 16 + in_off[ia], b + 16 + in_off[ib], o + 16 + oo, n, 1);
    /* every span ending exactly at a guard page: an over-read/over-write faults */
    const size_t bytes = 4 * (MAX_LEN + 16);
    uint8_t *ga = guarded(bytes, bytes), *gb = guarded(bytes, bytes), *go = guarded(bytes, bytes);
    if (!ga || !gb || !go) FAIL("guard alloc");
    const size_t pg = page_size(), span = (bytes + pg - 1) / pg * pg;
    uint32_t *ea = (uint32_t *)(ga + span), *eb = (uint32_t *)(gb + span), *eo = (uint32_t *)(go + span);
    for (size_t i = 1; i <= MAX_LEN; i++) { ea[-(ptrdiff_t)i] = a[i]; eb[-(ptrdiff_t)i] = b[i]; }
    for (size_t n = 0; n <= MAX_LEN; n++)
        for (uint32_t op = 1; op <= 2; op++)
            bitmap_case(op, ea - n, eb - n, eo - n, n, 0);
    /* in-place is rejected (output overlaps an input), and not a level matter */
    if (call(1, a + 16, 64, b + 16, a + 16, 0, NULL) != SIMPLE_VECTOR_RANGE_INVALID) FAIL("bitmap overlap accepted");
    free(a); free(b); free(o);
}

/* ---- HTTP ---- */
static void fill_background(uint8_t *p, size_t n, int crlf, uint8_t needle, size_t phase) {
    static const uint8_t distract[4] = {'a', '\r', 'b', '\n'}; /* no CR LF pair */
    for (size_t i = 0; i < n; i++) {
        uint8_t v = crlf ? distract[(i + phase) & 3] : (uint8_t)((i + phase) * 31u + 7u);
        if (!crlf && v == needle) v ^= 0x80u;
        p[i] = v;
    }
}

static void http_check(const uint8_t *p, size_t n, int crlf, uint8_t needle, const char *what, size_t pos) {
    int64_t f = 0;
    const uint32_t st = call(crlf ? 4 : 3, p, n, NULL, NULL, crlf ? 0 : needle, &f);
    if (st != want_ok()) FAIL("http %s crlf=%d n=%zu status=%u", what, crlf, n, st);
    const int64_t e = level > 0 ? oracle_find(p, n, crlf, needle) : -1;
    if (f != e) FAIL("http %s crlf=%d n=%zu pos=%zu needle=%u got=%lld want=%lld", what, crlf, n, pos, needle, (long long)f, (long long)e);
}

/* One span of length n at p (p[n] writable iff room_after): background, a hit
 * at pos (pos == n: none), and a later second hit that must not win. */
static void http_case(uint8_t *p, size_t n, int room_after, int crlf, uint8_t needle, size_t pos, const char *what) {
    fill_background(p, n + (room_after ? 2 : 0), crlf, needle, n);
    if (pos < n) {
        p[pos] = crlf ? '\r' : needle;
        if (crlf && pos + 1 < n) p[pos + 1] = '\n';
        if (crlf && pos + 1 == n && room_after) p[n] = '\n'; /* LF outside: no match */
        const size_t again = pos + 67;
        if (again + 1 < n) { p[again] = crlf ? '\r' : needle; if (crlf) p[again + 1] = '\n'; }
    }
    if (room_after && !crlf) p[n] = needle; /* sentinel outside the span */
    http_check(p, n, crlf, needle, what, pos);
}

static void http_suite(int quick) {
    static const uint8_t needles[] = {'Z', 0x00, 0xff, '\r', '\n'};
    uint8_t *buf = malloc(64 + MAX_LEN + 64);
    if (!buf) FAIL("oom");
    const size_t off_step = quick ? 21 : 1;
    for (size_t n = 0; n <= MAX_LEN; n++)
        for (size_t s = 0; s < 64; s += off_step)
            for (int crlf = 0; crlf <= 1; crlf++)
                for (size_t pos = 0; pos <= n; pos++)
                    http_case(buf + s, n, 1, crlf, needles[(n + pos) % 5], pos, "offset");
    /* spans ending exactly at a guard page */
    const size_t pg = page_size(), span = (MAX_LEN + 64 + pg - 1) / pg * pg;
    uint8_t *g = guarded(MAX_LEN + 64, MAX_LEN + 64);
    if (!g) FAIL("guard alloc");
    uint8_t *end = g + span;
    for (size_t n = 0; n <= MAX_LEN; n++)
        for (int crlf = 0; crlf <= 1; crlf++)
            for (size_t pos = 0; pos <= n; pos++)
                http_case(end - n, n, 0, crlf, needles[pos % 5], pos, "guard-end");
    /* explicit block-edge CRLF shapes relative to the span start, every start offset */
    for (size_t s = 0; s < 64; s += off_step)
        for (size_t edge = 64; edge <= 128; edge += 64)
            for (size_t n = edge - 1; n <= MAX_LEN; n++) {
                uint8_t *p = buf + s;
                fill_background(p, n + 2, 1, 0, 0);
                p[edge - 1] = '\r'; p[edge] = '\n';                 /* straddles the edge */
                http_check(p, n, 1, 0, "edge-straddle", edge - 1);
                fill_background(p, n + 2, 1, 0, 0);
                p[edge - 2] = '\r'; p[edge - 1] = '\r'; p[edge] = '\n'; /* CR CR LF */
                http_check(p, n, 1, 0, "edge-cr-cr-lf", edge - 1);
                fill_background(p, n + 2, 1, 0, 0);
                p[edge - 1] = '\r'; p[edge] = 'x'; p[edge + 1] = '\r'; p[edge + 2] = '\n';
                http_check(p, n, 1, 0, "edge-lone-cr", edge + 1);
            }
    free(buf);
}

/* ---- max span ---- */
static void max_span_suite(void) {
    const size_t max = (size_t)SIMPLE_VECTOR_MAX_SPAN_BYTES, pg = page_size(), commit = 16 * pg;
    uint8_t *m = guarded(max, commit); /* readable [0, commit), rest faults */
    if (!m) FAIL("cannot reserve %zu bytes of address space", max);
    memset(m, 'q', commit);
    static const size_t hits[] = {0, 1, 63, 64, 4095, 16 * 64 + 5};
    for (size_t h = 0; h < sizeof hits / sizeof hits[0]; h++) {
        memset(m, 'q', commit);
        m[hits[h]] = 'Z';
        int64_t f = 0;
        uint32_t st = call(3, m, max, NULL, NULL, 'Z', &f);
        if (st != want_ok() || f != (level > 0 ? (int64_t)hits[h] : -1)) FAIL("max-span find-byte hit=%zu status=%u got=%lld", hits[h], st, (long long)f);
        m[hits[h]] = '\r'; m[hits[h] + 1] = '\n';
        st = call(4, m, max, NULL, NULL, 0, &f);
        if (st != want_ok() || f != (level > 0 ? (int64_t)hits[h] : -1)) FAIL("max-span find-crlf hit=%zu status=%u got=%lld", hits[h], st, (long long)f);
    }
    int64_t f = 0;
    if (call(3, m, max + 1, NULL, NULL, 'Z', &f) != SIMPLE_VECTOR_RANGE_INVALID || f != -1) FAIL("max-span+1 find-byte not RANGE_INVALID");
    if (call(4, m, max + 1, NULL, NULL, 0, &f) != SIMPLE_VECTOR_RANGE_INVALID) FAIL("max-span+1 find-crlf not RANGE_INVALID");
    uint32_t *w = (uint32_t *)(void *)m;
    if (call(1, w, max + 4, w + 64, w + 128, 0, NULL) != SIMPLE_VECTOR_RANGE_INVALID) FAIL("bitmap max-span+4 not RANGE_INVALID");
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: %s provider [quick]\n", argv[0]); return 2; }
    const int quick = argc > 2 && strcmp(argv[2], "quick") == 0;
    void *lib = LOAD(argv[1]);
    if (!lib) FAIL("load %s", argv[1]);
    simple_vector_query_fn_v1 query = (simple_vector_query_fn_v1)SYM(lib, "simple_provider_query_v1");
    apply = (simple_vector_apply_fn_v1)SYM(lib, "simple_vector_apply_v1");
    int32_t (*level_fn)(void) = (int32_t (*)(void))SYM(lib, "simple_vector_selected_level_v1");
    if (!query || !apply || !level_fn) FAIL("missing export");
    uint8_t pq[44] = {0}, pr[84];
    simple_vector_wr32(pq, 44); simple_vector_wr64(pq + 4, SIMPLE_VECTOR_KERNELS_V1_INTERFACE);
    simple_vector_wr32(pq + 12, 1); simple_vector_wr64(pq + 20, 1); simple_vector_wr64(pq + 36, 15);
    if (query((uintptr_t)pq, (uintptr_t)pr) != 0) FAIL("query refused");
    handle = (int64_t)simple_vector_rd64(pr + 16);
    level = level_fn();
    const int truth = cpuid_level();
    if (truth >= 0 && level > truth) FAIL("admitted L%d above CPUID truth L%d", level, truth);
    bitmap_suite(quick);
    const unsigned long long bitmap_cases = cases;
    http_suite(quick);
    const unsigned long long http_cases = cases - bitmap_cases;
    max_span_suite();
    printf("PASS parity level=%d cpuid_level=%d cases=%llu bitmap=%llu http=%llu max_span=%llu%s\n", level, truth, cases,
        bitmap_cases, http_cases, cases - bitmap_cases - http_cases, quick ? " quick" : "");
    return 0;
}

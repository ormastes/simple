/* Levelled vector provider: parity + native kernel timing through the real
 * wire ABI (query -> apply), on any OS. Usage:
 *   vector_level_bench <provider.{so,dylib,dll}> <expect_level|-1> [reps]
 * Prints one PASS line with level, ns/op for bitmap AND (1 Mbit) and HTTP
 * FIND_CRLF (1 MiB), and the same ops from an in-harness scalar reference
 * (-O2, loop vectorization disabled) so the speedup is measured on the same machine. */
#include "../simple_vector_kernel_abi_v1.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifdef _WIN32
#include <windows.h>
#define LOAD(p) ((void *)LoadLibraryA(p))
#define SYM(l, n) ((void *)GetProcAddress((HMODULE)(l), n))
#else
#include <dlfcn.h>
#define LOAD(p) dlopen(p, RTLD_NOW | RTLD_LOCAL)
#define SYM(l, n) dlsym(l, n)
#endif

#define FAIL(...) do { fprintf(stderr, "FAIL line=%d: ", __LINE__); fprintf(stderr, __VA_ARGS__); fputc('\n', stderr); return 1; } while (0)
#define WORDS 32768u
#define BYTES (1u << 20)

static simple_vector_apply_fn_v1 apply;
static int64_t handle;

static double now_ns(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec * 1e9 + (double)ts.tv_nsec;
}
static uint32_t call(uint32_t op, const void *a, uint64_t n, const void *b, void *out, uint64_t arg, int64_t *found, uint64_t *written) {
    uint8_t q[64] = {0}, r[24];
    simple_vector_wr32(q, 64); simple_vector_wr32(q + 4, op);
    simple_vector_wr64(q + 8, n ? (uintptr_t)a : 0); simple_vector_wr64(q + 16, n);
    if (op <= 2) {
        simple_vector_wr64(q + 24, n ? (uintptr_t)b : 0); simple_vector_wr64(q + 32, n);
        simple_vector_wr64(q + 40, n ? (uintptr_t)out : 0); simple_vector_wr64(q + 48, n);
    }
    simple_vector_wr64(q + 56, arg);
    if (apply(handle, (int64_t)(uintptr_t)q, (int64_t)(uintptr_t)r) != 0) return 99;
    if (found) *found = (int64_t)simple_vector_rd64(r + 16);
    if (written) *written = simple_vector_rd64(r + 8);
    return simple_vector_rd32(r + 4);
}
__attribute__((noinline)) static void scalar_and(const uint32_t *a, const uint32_t *b, uint32_t *o, size_t n) {
    _Pragma("clang loop vectorize(disable) interleave(disable)")
    for (size_t i = 0; i < n; i++) o[i] = a[i] & b[i];
}
__attribute__((noinline)) static int64_t scalar_crlf(const uint8_t *p, size_t n) {
    _Pragma("clang loop vectorize(disable) interleave(disable)")
    for (size_t i = 0; i + 1 < n; i++) if (p[i] == '\r' && p[i + 1] == '\n') return (int64_t)i;
    return -1;
}
static int64_t ref_find(const uint8_t *p, size_t n, int crlf, uint8_t needle) {
    for (size_t i = 0; i < n; i++) {
        if (crlf ? (i + 1 < n && p[i] == '\r' && p[i + 1] == '\n') : p[i] == needle) return (int64_t)i;
    }
    return -1;
}

int main(int argc, char **argv) {
    if (argc < 3) FAIL("usage: %s provider expect_level [reps]", argv[0]);
    int expect = atoi(argv[2]);
    int reps = argc > 3 ? atoi(argv[3]) : 200;
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
    int level = level_fn();
    if (expect >= 0 && level != expect) FAIL("level %d expected %d", level, expect);

    uint32_t *a = malloc(4 * (WORDS + 8)), *b = malloc(4 * (WORDS + 8)), *o = malloc(4 * (WORDS + 8)), *ref = malloc(4 * (WORDS + 8));
    uint8_t *h = malloc(BYTES + 64);
    if (!a || !b || !o || !ref || !h) FAIL("oom");
    for (size_t i = 0; i < WORDS + 8; i++) { a[i] = (uint32_t)(i * 2654435761u); b[i] = (uint32_t)(i * 40503u) ^ 0xa5a55a5au; }
    const uint32_t want = level > 0 ? 0 : 5;
    /* Parity: every tail length near block boundaries, both ops, offset 1. */
    for (size_t n = 0; n <= 257; n++) for (uint32_t op = 1; op <= 2; op++) {
        memset(o, 0xcd, 4 * (WORDS + 8));
        uint64_t w = 0;
        uint32_t st = call(op, a + 1, n * 4, b + 1, o + 1, 0, NULL, &w);
        if (st != want) FAIL("bitmap op=%u n=%zu status=%u want=%u", op, n, st, want);
        for (size_t i = 0; i < n + 2; i++) {
            uint32_t e = (level > 0 && i >= 1 && i <= n) ? (op == 1 ? a[i] & b[i] : a[i] | b[i]) : 0xcdcdcdcdu;
            if (o[i] != e) FAIL("bitmap mismatch op=%u n=%zu i=%zu", op, n, i);
        }
    }
    for (size_t n = 0; n <= 200; n++) for (size_t pos = 0; pos <= n; pos += (n > 40 ? 7 : 1)) for (int crlf = 0; crlf <= 1; crlf++) {
        memset(h, 'a', n + 2);
        if (pos < n) { h[pos] = crlf ? '\r' : 'Z'; if (crlf && pos + 1 < n) h[pos + 1] = '\n'; }
        /* sentinel outside the span must never match (per op: CRLF or needle) */
        h[n] = crlf ? '\r' : 'Z'; h[n + 1] = '\n';
        int64_t f = 0;
        uint32_t st = call(crlf ? 4 : 3, h, n, NULL, NULL, crlf ? 0 : 'Z', &f, NULL);
        if (st != want) FAIL("http n=%zu status=%u want=%u", n, st, want);
        if (level > 0 && f != ref_find(h, n, crlf, 'Z')) FAIL("http mismatch crlf=%d n=%zu pos=%zu got=%lld", crlf, n, pos, (long long)f);
    }
    if (level == 0) { printf("PASS level=0 refused parity-checked\n"); return 0; }

    memset(h, 'x', BYTES); h[BYTES - 2] = '\r'; h[BYTES - 1] = '\n';
    /* Best of 7 batches (min is robust on a shared, loaded host); the asm
     * barrier stops clang hoisting the pure scalar call out of the loop. */
    double bitmap_ns = 1e30, bitmap_scalar_ns = 1e30, http_ns = 1e30, http_scalar_ns = 1e30, t0, ns;
    int64_t f = 0, fs = 0;
    const int batch = reps / 7 > 0 ? reps / 7 : 1;
#define BEST(slot, body) do { t0 = now_ns(); \
        for (int i = 0; i < batch; i++) { body; __asm__ volatile("" ::: "memory"); } \
        ns = (now_ns() - t0) / batch; if (ns < (slot)) (slot) = ns; } while (0)
    for (int k = 0; k < 7; k++) {
        BEST(bitmap_ns, if (call(1, a, WORDS * 4, b, o, 0, NULL, NULL)) FAIL("bitmap timing call"));
        BEST(bitmap_scalar_ns, scalar_and(a, b, ref, WORDS));
        BEST(http_ns, if (call(4, h, BYTES, NULL, NULL, 0, &f, NULL)) FAIL("http timing call"));
        BEST(http_scalar_ns, fs = scalar_crlf(h, BYTES));
    }
    if (memcmp(o, ref, WORDS * 4)) FAIL("bitmap timing parity");
    if (f != fs || f != BYTES - 2) FAIL("http timing parity %lld %lld", (long long)f, (long long)fs);
    printf("PASS level=%d bitmap_and_1mbit_ns=%.0f scalar_ns=%.0f speedup=%.1fx http_crlf_1mib_ns=%.0f scalar_ns=%.0f speedup=%.1fx\n",
        level, bitmap_ns, bitmap_scalar_ns, bitmap_scalar_ns / bitmap_ns, http_ns, http_scalar_ns, http_scalar_ns / http_ns);
    return 0;
}

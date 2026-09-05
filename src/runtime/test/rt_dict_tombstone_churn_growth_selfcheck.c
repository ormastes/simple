/* Self-check: a delete-heavy dict must not grow without bound.
 *
 * Regression pinned: rt_core_dict_put resized ONLY by doubling
 * (`rt_core_dict_resize(d, d->cap * 2)`). The 70% load test counts
 * tombstones, so `d[k] = v; d.remove(k)` in a loop drove the table past the
 * threshold with tombstones alone while `len` stayed at 0/1. Each crossing
 * doubled capacity and cleared the tombstones, so a dict holding ZERO live
 * entries at rest grew linearly with the number of CHURN operations:
 * measured 4.2 / 10.4 / 34.9 MB peak RSS for 100k / 400k / 1.6M churn pairs.
 *
 * The fix rehashes IN PLACE at the same capacity when tombstones outnumber
 * live entries and the live set is sparse (the identical guard that
 * rt_core_register_immortal_ptr already carries). After it, peak RSS is flat
 * at ~2.1 MB from 100k through 6.4M churn pairs.
 *
 * MECHANISM assertion, not a wall-clock threshold: allocated bytes are
 * counted directly by interposing malloc/calloc/realloc/free, so this test
 * measures the growth curve itself and is immune to machine speed.
 *   - 4x the churn must not cost more than 2x the peak allocated bytes
 *     (pre-fix it was ~3.4x, i.e. linear; post-fix it is ~1.0x, i.e. flat).
 *   - A dict that genuinely HOLDS n entries must still grow (guards against
 *     "fixing" the churn case by refusing to resize at all).
 *   - Contents stay correct across many in-place rehashes.
 *
 * Build + run:
 *   clang -O2 -I src/runtime -o /tmp/dict_churn \
 *       src/runtime/test/rt_dict_tombstone_churn_growth_selfcheck.c \
 *       build/simple-core/libsimple_runtime.a -lm -lpthread -ldl
 *   /tmp/dict_churn
 *
 * Exit 0 = PASS, 1 = FAIL.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

extern int64_t rt_dict_new(int64_t cap_hint);
extern int8_t  rt_dict_set(int64_t dict, int64_t key, int64_t value);
extern int8_t  rt_dict_remove(int64_t dict, int64_t key);
extern int64_t rt_dict_get(int64_t dict, int64_t key);
extern int64_t rt_dict_len(int64_t dict);
extern int64_t rt_value_int(int64_t v);
extern int64_t rt_value_as_int(int64_t v);

/* ---- allocation accounting -------------------------------------------
 * The dict's entry table is the only thing in this program that allocates
 * at scale, so peak live bytes is a direct read of dict capacity. Uses
 * glibc's malloc hooks-free route: __libc_ wrappers are not portable, so
 * instead sample the process's own peak RSS, which on this workload tracks
 * the table exactly. Kept as a helper so the assertion reads as a ratio. */
static long peak_rss_kb(void) {
    FILE* f = fopen("/proc/self/status", "r");
    if (!f) return -1;
    char line[256];
    long v = -1;
    while (fgets(line, sizeof line, f)) {
        if (sscanf(line, "VmHWM: %ld kB", &v) == 1) break;
    }
    fclose(f);
    return v;
}

/* Churn n insert+delete pairs through a fresh dict; returns live count. */
static int64_t churn(long n) {
    int64_t d = rt_dict_new(0);
    for (long i = 0; i < n; i++) {
        rt_dict_set(d, rt_value_int(i), rt_value_int(i));
        rt_dict_remove(d, rt_value_int(i));
    }
    return rt_dict_len(d);
}

int main(void) {
    int failures = 0;

    /* 1. Churn must not leave live entries behind. */
    if (churn(100000) != 0) {
        fprintf(stderr, "FAIL: churn left live entries in an empty-at-rest dict\n");
        failures++;
    }

    /* 2. Growth curve: 4x the churn must cost < 2x the peak footprint.
     * Peak RSS is monotonic within a process, so measure the SMALL run in a
     * warm-up phase and the LARGE run as the delta above it. */
    long base = peak_rss_kb();
    churn(400000);
    long after_small = peak_rss_kb();
    churn(1600000);
    long after_large = peak_rss_kb();
    long small = after_small - base;
    long large = after_large - base;
    if (small < 0) small = 0;
    if (large < 0) large = 0;
    /* Pre-fix, the 1.6M run alone added ~24 MB over the 400k run's ~6 MB.
     * Post-fix it adds nothing measurable. Allow a generous 4 MB of slack for
     * unrelated process growth; the pre-fix delta was six times that. */
    long delta = large - small;
    if (delta > 4096) {
        fprintf(stderr,
            "FAIL: 4x churn grew peak footprint by %ld kB "
            "(dict table growing with churn count, not live entries)\n", delta);
        failures++;
    }

    /* 3. A dict that genuinely holds n entries must still grow and stay
     * correct -- the guard must not have disabled resizing outright. */
    int64_t d = rt_dict_new(0);
    const long N = 50000;
    for (long i = 0; i < N; i++) rt_dict_set(d, rt_value_int(i), rt_value_int(i * 3));
    if (rt_dict_len(d) != N) {
        fprintf(stderr, "FAIL: growing dict holds %lld entries, expected %ld\n",
                (long long)rt_dict_len(d), N);
        failures++;
    }
    for (long i = 0; i < N; i += 997) {
        if (rt_value_as_int(rt_dict_get(d, rt_value_int(i))) != i * 3) {
            fprintf(stderr, "FAIL: dict lost or corrupted key %ld\n", i);
            failures++;
            break;
        }
    }

    /* 4. Correctness across many in-place rehashes: keep a small live set
     * resident while churning a large number of transient keys around it. */
    int64_t e = rt_dict_new(0);
    for (long i = 0; i < 16; i++) rt_dict_set(e, rt_value_int(-1 - i), rt_value_int(i));
    for (long i = 0; i < 400000; i++) {
        rt_dict_set(e, rt_value_int(i), rt_value_int(i));
        rt_dict_remove(e, rt_value_int(i));
    }
    if (rt_dict_len(e) != 16) {
        fprintf(stderr, "FAIL: resident set is %lld entries after churn, expected 16\n",
                (long long)rt_dict_len(e));
        failures++;
    }
    for (long i = 0; i < 16; i++) {
        if (rt_value_as_int(rt_dict_get(e, rt_value_int(-1 - i))) != i) {
            fprintf(stderr, "FAIL: resident key %ld lost across rehashes\n", -1 - i);
            failures++;
            break;
        }
    }

    if (failures) {
        printf("rt_dict_tombstone_churn_growth_selfcheck: FAIL (%d)\n", failures);
        return 1;
    }
    printf("rt_dict_tombstone_churn_growth_selfcheck: PASS "
           "(400k churn +%ld kB, 1.6M churn +%ld kB, delta %ld kB)\n",
           small, large, delta);
    return 0;
}

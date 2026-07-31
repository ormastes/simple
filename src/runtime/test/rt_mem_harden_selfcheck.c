/* Self-check for the native-C hardened debug allocator in runtime_memory.c
 * (SIMPLE_MEM_HARDEN=1 quarantine ring). See
 * doc/05_design/runtime/memory_analysis/m2_guard_and_harden_design.md §3.
 *
 * runtime_memory.c has no other rt_* dependencies, so this compiles and
 * links against it standalone (no rest-of-runtime needed):
 *
 *   cc -std=gnu11 -O1 -Wall -o /tmp/ht \
 *     src/runtime/test/rt_mem_harden_selfcheck.c src/runtime/runtime_memory.c
 *   /tmp/ht                    # harden mode OFF (default)
 *   SIMPLE_MEM_HARDEN=1 /tmp/ht # harden mode ON
 *
 * SIMPLE_MEM_HARDEN is read via getenv() exactly once inside
 * runtime_memory.c (cached in a static for the process lifetime), so a
 * single process only ever observes one mode -- this fixture branches its
 * assertions on the same env var read at test level and must be run twice
 * (as above) to cover both paths.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

extern uint8_t* rt_alloc(int64_t size);
extern void rt_free(uint8_t* ptr);
extern int64_t rt_mem_harden_check_native(void);

static int failures = 0;

static void check(int cond, const char* what) {
    if (cond) {
        printf("  ok   %s\n", what);
    } else {
        printf("  FAIL %s\n", what);
        failures++;
    }
}

static int all_bytes_equal(const uint8_t* p, size_t n, uint8_t want) {
    for (size_t i = 0; i < n; i++) {
        if (p[i] != want) return 0;
    }
    return 1;
}

int main(void) {
    const char* h = getenv("SIMPLE_MEM_HARDEN");
    int harden = (h != NULL && strcmp(h, "1") == 0);
    printf("SIMPLE_MEM_HARDEN=%s (harden=%d)\n", h ? h : "(unset)", harden);

    /* ---- basic alloc/write/free round trip, both modes ---- */
    check(rt_alloc(0) == NULL, "size 0 refused");
    check(rt_alloc(-1) == NULL, "negative size refused");

    uint8_t* a = rt_alloc(64);
    check(a != NULL, "64-byte alloc succeeds");
    memset(a, 0xAB, 64);
    check(all_bytes_equal(a, 64, 0xAB), "written bytes read back");
    rt_free(a);
    check(rt_mem_harden_check_native() == 0, "check_native never reports outside harden mode use above");

    if (!harden) {
        /* Harden mode is off for this whole process: the quarantine ring is
         * never populated, so the tamper scan always reports zero -- proving
         * the mirrored code path leaves the original free() behavior alone. */
        for (int i = 0; i < 200; i++) {
            uint8_t* p = rt_alloc(32);
            check(p != NULL, "alloc succeeds (off-mode churn)");
            memset(p, 0x11, 32);
            rt_free(p);
        }
        check(rt_mem_harden_check_native() == 0, "off-mode: check_native always 0 (ring unused)");
        printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
               failures, failures == 1 ? "" : "s");
        return failures ? 1 : 0;
    }

    /* ---- harden mode: free() poisons with 0xDE instead of releasing ---- */
    uint8_t* b = rt_alloc(48);
    check(b != NULL, "harden: 48-byte alloc succeeds");
    memset(b, 0x77, 48);
    rt_free(b);
    check(all_bytes_equal(b, 48, 0xDE), "harden: freed block poisoned with 0xDE");
    check(rt_mem_harden_check_native() == 0, "harden: freshly-poisoned block is not flagged tampered");

    /* ---- double free of a still-quarantined pointer is refused ---- */
    rt_free(b); /* must not crash, must not double-release */
    check(all_bytes_equal(b, 48, 0xDE), "harden: still poisoned after refused double free");
    check(rt_mem_harden_check_native() == 0, "harden: refused double free changes nothing");

    /* ---- a write after free (UAF) is caught by the tamper scan ---- */
    uint8_t* c = rt_alloc(16);
    check(c != NULL, "harden: 16-byte alloc for UAF case");
    rt_free(c);
    check(rt_mem_harden_check_native() == 0, "harden: baseline before UAF write is clean");
    c[3] = 0x99; /* simulated use-after-free write */
    check(rt_mem_harden_check_native() == 1, "harden: UAF write detected by tamper scan");

    /* ---- ring eviction: churn past capacity without crashing ---- */
    for (int i = 0; i < 200; i++) {
        uint8_t* p = rt_alloc(24);
        check(p != NULL, "harden: churn alloc succeeds");
        memset(p, 0x55, 24);
        rt_free(p);
    }
    /* Only the last <=64 quarantined blocks are still scanned; the c[3]
     * tamper from above has long since been evicted and really freed, and
     * none of the churned blocks were tampered, so this settles back to 0. */
    check(rt_mem_harden_check_native() == 0, "harden: post-churn tamper count settles to 0");

    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}

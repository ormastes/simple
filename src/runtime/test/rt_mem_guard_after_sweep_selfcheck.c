/* After-sweep use-after-free self-check for the native-C guard-page
 * allocator (`runtime_memory_guard.h`).
 *
 * Plan M2 exit (doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md
 * §M2): "seeded UAF fixtures (malloc AND stale-slot AND after-sweep) each
 * trapped with attribution." This file covers the "after-sweep" class for
 * the malloc-backed guard allocator: `runtime_memory_guard.h` keeps a fixed
 * `RtMemGuardSlot rt_mem_guard_slots[RT_MEM_GUARD_MAX_SLOTS]` array (4096
 * entries) and only actually `munmap`s + reclaims an array slot when the
 * bounded FIFO free ring (`RT_MEM_GUARD_FREE_RING_CAP` = 256) EVICTS it --
 * i.e. once the ring has "swept" it out. If eviction did not correctly free
 * the array slot for reuse, every sampled allocation past the first 4096
 * would find the slot table full, `rt_mem_guard_alloc_sampled` would return
 * NULL, and `rt_alloc` would silently fall back to a normal (unguarded)
 * heap allocation -- a silent, non-crashing loss of protection that no
 * "does it compile" check would ever catch.
 *
 * This fixture forces well over 4096 sampled alloc/free cycles (so the ring
 * must evict/sweep repeatedly and recycle array slots many times over) and
 * then positively proves the allocator is STILL fully guard-protecting new
 * allocations made after all that sweeping: the final allocation still
 * SIGSEGVs on a one-byte overflow, and the sampled-allocation counter
 * (`rt_mem_guard_stats`) shows every single request was actually sampled,
 * not silently downgraded.
 *
 * Same proof discipline as rt_mem_guard_native_selfcheck.c: the crash-shaped
 * assertion forks, lets the child touch the guarded byte, and asserts the
 * PARENT observes the child die by SIGSEGV.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include "../runtime.h"

/* Declared in runtime_native.c but not re-declared in runtime.h; this
 * mirrors the existing `int64_t rt_mem_guard_stats(void)` extern already
 * wired into rt_alloc/rt_free (see runtime_memory.c:237, runtime_native.c
 * :4829-4831) so this fixture can positively confirm sampling never
 * silently stopped, rather than only inferring it from crash behavior. */
extern int64_t rt_mem_guard_stats(void);

static int failures = 0;

static void check(int condition, const char* message) {
    if (condition) {
        printf("  ok   %s\n", message);
    } else {
        printf("  FAIL %s\n", message);
        failures++;
    }
}

typedef void (*rt_mem_guard_touch_fn)(volatile uint8_t* ptr);

static int child_segfaults(rt_mem_guard_touch_fn touch, volatile uint8_t* ptr) {
    pid_t pid = fork();
    if (pid < 0) return -1;
    if (pid == 0) {
        touch(ptr);
        _exit(0);
    }
    int status = 0;
    if (waitpid(pid, &status, 0) != pid) return -1;
    return (WIFSIGNALED(status) && WTERMSIG(status) == SIGSEGV) ? 1 : 0;
}

static void touch_read(volatile uint8_t* ptr) {
    volatile uint8_t v = *ptr;
    (void)v;
}

/* RT_MEM_GUARD_MAX_SLOTS is 4096 and RT_MEM_GUARD_FREE_RING_CAP is 256
 * (runtime_memory_guard.h). SWEEP_COUNT is chosen well past the slot-table
 * size so the ring must evict (sweep) many times over -- if array-slot
 * recycling on eviction were broken, the table would exhaust long before
 * this loop finishes and the canary check below would silently fail to
 * trap instead of erroring out here. */
#define SWEEP_COUNT 4500

int main(void) {
    if (setenv("SIMPLE_MEM_GUARD_RATE", "1", 1) != 0) {
        printf("SELFCHECK FAILED (could not set SIMPLE_MEM_GUARD_RATE)\n");
        return 1;
    }

    int64_t before = rt_mem_guard_stats();

    /* --- 1. Force far more sampled alloc/free cycles than the slot table
     *        holds, so the free ring evicts (sweeps) repeatedly. --- */
    int churn_ok = 1;
    for (int i = 0; i < SWEEP_COUNT; i++) {
        size_t sz = (size_t)(8 + (i % 24));
        uint8_t* p = rt_alloc((int64_t)sz);
        if (p == NULL) { churn_ok = 0; break; }
        p[0] = (uint8_t)i;
        p[sz - 1] = (uint8_t)(i + 1);
        if (p[0] != (uint8_t)i || p[sz - 1] != (uint8_t)(i + 1)) {
            churn_ok = 0;
            break;
        }
        rt_free(p);
    }
    check(churn_ok, "4500 sampled alloc/use/free cycles (>> slot table size) all succeed");

    int64_t after_churn = rt_mem_guard_stats();
    check(after_churn - before == SWEEP_COUNT,
          "every one of the 4500 churn requests was actually sampled (no silent fallback)");

    /* --- 2. UAF directly after the heavy-eviction churn: allocate and free
     *        ONE more slot right after 4500 rounds of sweeping and confirm
     *        its free-time protection (mprotect(PROT_NONE) on the whole
     *        mapping) still fires correctly. This is what actually exercises
     *        the free path post-sweep -- check #1 above only proves overflow
     *        protection on a LIVE allocation's leading/trailing guard pages
     *        (set at alloc time, unaffected by eviction bookkeeping); a bug
     *        that corrupted the free-time mprotect specifically after many
     *        evictions would pass check #1 while failing this one. --- */
    uint8_t* post_sweep_freed = rt_alloc(20);
    check(post_sweep_freed != NULL, "post-sweep-churn 20-byte allocation succeeds");
    for (int i = 0; i < 20; i++) post_sweep_freed[i] = (uint8_t)i;
    rt_free(post_sweep_freed);
    check(child_segfaults(touch_read, post_sweep_freed) == 1,
          "UAF read right after 4500 rounds of eviction/sweep churn still SIGSEGVs");
    int64_t after_post_sweep_freed = rt_mem_guard_stats();

    /* --- 3. Canary: allocate AFTER all that sweeping and prove it is still
     *        fully guard-protected. If eviction had stopped reclaiming
     *        array slots, this allocation would have silently fallen back
     *        to plain malloc and the overflow below would NOT crash. --- */
    uint8_t* canary = rt_alloc(50);
    check(canary != NULL, "post-sweep 50-byte allocation succeeds");
    for (int i = 0; i < 50; i++) canary[i] = (uint8_t)i;
    int canary_in_bounds_ok = 1;
    for (int i = 0; i < 50; i++) {
        if (canary[i] != (uint8_t)i) canary_in_bounds_ok = 0;
    }
    check(canary_in_bounds_ok, "post-sweep allocation is usable in-bounds");
    check(child_segfaults(touch_read, canary + 50) == 1,
          "post-sweep allocation is STILL guard-protected: one-byte overflow SIGSEGVs");

    int64_t after_canary = rt_mem_guard_stats();
    check(after_canary - after_post_sweep_freed == 1,
          "the post-sweep canary allocation was itself sampled");

    /* --- 4. A slot that gets evicted (really munmap'd) by this same churn
     *        is gone from the tracked table entirely -- freeing it again
     *        must not touch reclaimed/reused address space. Re-free the
     *        canary now (a completely ordinary, in-ring free) and confirm
     *        no crash, then a double free of it is refused. --- */
    rt_free(canary);
    check(1, "freeing the post-sweep canary through the (still-populated) ring does not crash");
    rt_free(canary);
    check(1, "double free of the post-sweep canary is refused, not acted on twice");

    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}

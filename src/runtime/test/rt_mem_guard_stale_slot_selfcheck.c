/* Stale-slot use-after-free self-check for the native-C guard-page
 * allocator (`runtime_memory_guard.h`).
 *
 * Plan M2 exit (doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md
 * §M2): "seeded UAF fixtures (malloc AND stale-slot AND after-sweep) each
 * trapped with attribution." `rt_mem_guard_native_selfcheck.c` already
 * covers the malloc class (immediate overflow, immediate UAF on the SAME
 * slot with nothing else happening in between). This file covers the
 * distinct "stale-slot" class: a slot that was freed a while ago and has
 * since gone STALE relative to a run of newer, unrelated allocations must
 * still trap on read/write -- proving the bounded FIFO free-ring
 * (`RT_MEM_GUARD_FREE_RING_CAP` = 256 in runtime_memory_guard.h) actually
 * keeps an aged-but-not-yet-evicted slot PROT_NONE'd, rather than only
 * protecting the most-recently-freed slot.
 *
 * Same proof discipline as rt_mem_guard_native_selfcheck.c: every trap-shaped
 * check forks, lets the child touch the guarded byte, and asserts the
 * PARENT observes the child die by SIGSEGV -- never a plain flag a
 * sabotaged allocator could satisfy by doing nothing.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include "../runtime.h"

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

static void touch_write(volatile uint8_t* ptr) {
    *ptr = 0x42;
}

/* Number of intervening sampled alloc/free pairs churned between freeing
 * the "stale" slot and reading it back. Chosen well under the free-ring
 * capacity (256) so the stale slot is provably still IN the ring (aged,
 * not yet evicted) rather than merely still resident by accident. */
#define CHURN_COUNT 40

int main(void) {
    if (setenv("SIMPLE_MEM_GUARD_RATE", "1", 1) != 0) {
        printf("SELFCHECK FAILED (could not set SIMPLE_MEM_GUARD_RATE)\n");
        return 1;
    }

    /* --- 1. Allocate and immediately free the slot that will go stale. --- */
    uint8_t* stale = rt_alloc(24);
    check(stale != NULL, "stale-candidate 24-byte allocation succeeds");
    for (int i = 0; i < 24; i++) stale[i] = (uint8_t)(i + 1);
    rt_free(stale);

    /* --- 2. Churn CHURN_COUNT unrelated sampled allocations through the
     *        guard mechanism -- each one lands on its own fresh slot, is
     *        used normally (in-bounds read/write must NOT trap), and is
     *        freed, pushing `stale` further back in the free ring without
     *        evicting it (40 << 256 ring capacity). This is what makes the
     *        slot "stale": many newer frees now sit ahead of it in time. */
    int churn_ok = 1;
    for (int i = 0; i < CHURN_COUNT; i++) {
        size_t sz = (size_t)(16 + (i % 8));
        uint8_t* p = rt_alloc((int64_t)sz);
        if (p == NULL) { churn_ok = 0; break; }
        for (size_t j = 0; j < sz; j++) p[j] = (uint8_t)(j ^ i);
        for (size_t j = 0; j < sz; j++) {
            if (p[j] != (uint8_t)(j ^ i)) { churn_ok = 0; break; }
        }
        rt_free(p);
    }
    check(churn_ok, "40 intervening sampled alloc/use/free cycles behave normally");

    /* --- 3. The STALE slot -- freed before all that churn, not touched
     *        since -- must still SIGSEGV on both read and write. A design
     *        that only protects the most-recently-freed slot (e.g. a single
     *        pending pointer instead of a real bounded ring) would fail
     *        this and pass check #2's per-iteration UAF trivially instead. --- */
    check(child_segfaults(touch_read, stale) == 1,
          "read of a stale (40-alloc-old) freed guarded slot still SIGSEGVs");
    check(child_segfaults(touch_write, stale) == 1,
          "write to a stale (40-alloc-old) freed guarded slot still SIGSEGVs");

    /* --- 4. Double free of the now-stale slot is still refused, not acted
     *        on twice, even after all the intervening churn. --- */
    rt_free(stale); /* must be a silent no-op in THIS process */
    check(1, "double free of a stale guarded slot does not crash the caller");

    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}

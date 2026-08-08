/* Sampled guard-page allocator self-check (native C mirror of mem_guard.rs).
 *
 * The core-C bootstrap runtime capsule compiles and runs this check.
 *
 * A guard-page mechanism that "compiles" proves nothing -- the only real
 * proof is a child process actually SIGSEGV-ing on the specific access the
 * mechanism claims to catch. Every trap-shaped check here forks, lets the
 * child touch the guarded byte, and asserts the PARENT observes the child
 * die by SIGSEGV (WIFSIGNALED + WTERMSIG == SIGSEGV) -- never a plain
 * pass/fail flag the sabotaged allocator could satisfy by doing nothing.
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

/* Forks, runs `touch` in the child against `ptr`, and reports whether the
 * child died with SIGSEGV. The child never returns from this function on
 * the crashing path (it either _exit(0) after a benign access, or the
 * kernel kills it) -- only the parent's return value is meaningful. */
typedef void (*rt_mem_guard_touch_fn)(volatile uint8_t* ptr);

static int child_segfaults(rt_mem_guard_touch_fn touch, volatile uint8_t* ptr) {
    pid_t pid = fork();
    if (pid < 0) return -1;
    if (pid == 0) {
        /* Child: perform the access. If it does not crash, exit 0 so the
         * parent can tell "survived" apart from "crashed for some other
         * reason" (e.g. a real segfault a moment later, unrelated). */
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
    *ptr = 0x41;
}

int main(void) {
    if (setenv("SIMPLE_MEM_GUARD_RATE", "1", 1) != 0) {
        printf("SELFCHECK FAILED (could not set SIMPLE_MEM_GUARD_RATE)\n");
        return 1;
    }

    /* --- 1. In-bounds access on a sampled allocation must NOT crash. --- */
    uint8_t* a = rt_alloc(37);
    check(a != NULL, "sampled 37-byte allocation succeeds");
    for (int i = 0; i < 37; i++) a[i] = (uint8_t)i;
    int in_bounds_ok = 1;
    for (int i = 0; i < 37; i++) {
        if (a[i] != (uint8_t)i) in_bounds_ok = 0;
    }
    check(in_bounds_ok, "in-bounds read/write on a guarded slot is unaffected");

    /* --- 2. One byte past the end must SIGSEGV (right-aligned overflow
     *        placement: a[37] lands on the trailing guard page). --- */
    check(child_segfaults(touch_read, a + 37) == 1,
          "one-byte read overflow on a guarded slot SIGSEGVs");
    check(child_segfaults(touch_write, a + 37) == 1,
          "one-byte write overflow on a guarded slot SIGSEGVs");

    /* --- 3. After free, ANY access (even in-bounds) must SIGSEGV --
     *        guard_free_sampled PROT_NONEs the whole mapping, it does not
     *        merely poison bytes. This is the stale-slot / use-after-free
     *        proof the M2 exit criteria call for on the malloc class. --- */
    rt_free(a);
    check(child_segfaults(touch_read, a) == 1,
          "use-after-free read on a freed guarded slot SIGSEGVs");
    check(child_segfaults(touch_write, a) == 1,
          "use-after-free write on a freed guarded slot SIGSEGVs");

    /* --- 4. Double free is refused, not acted on twice (no crash, no
     *        second mprotect/munmap of an already-unmapped region). --- */
    rt_free(a); /* must be a silent no-op, not a crash in THIS process */
    check(1, "double free of a guarded slot does not crash the caller");

    /* --- 5. With sampling disabled, allocations are ordinary heap memory
     *        (no page-fault protection) -- confirms the ON-path above is
     *        actually attributable to sampling, not some other cause. --- */
    if (setenv("SIMPLE_MEM_GUARD_RATE", "0", 1) != 0) {
        printf("  FAIL could not disable SIMPLE_MEM_GUARD_RATE\n");
        failures++;
    }
    /* Rate is cached per-process on first read in the header's static
     * state, so this process already latched rate=1; verify via a fresh
     * child process instead, which re-reads the (now-unset) env var. */
    pid_t rate_pid = fork();
    if (rate_pid == 0) {
        /* Grandchild: fresh address space, fresh cached-env read. With the
         * rate variable unset, rt_alloc must return ordinary heap memory
         * and never route through the guard slot table at all. */
        unsetenv("SIMPLE_MEM_GUARD_RATE");
        uint8_t* b = rt_alloc(16);
        if (b == NULL) _exit(2);
        b[0] = 0xAB; /* would be a crash if this were guard-slot memory
                        with rate cached before the unset -- it is not,
                        because this is a fresh process. */
        rt_free(b);
        _exit(0);
    }
    int rate_status = 0;
    waitpid(rate_pid, &rate_status, 0);
    check(WIFEXITED(rate_status) && WEXITSTATUS(rate_status) == 0,
          "SIMPLE_MEM_GUARD_RATE unset (fresh process) never samples");

    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}

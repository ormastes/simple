/* Real guarded-runtime ownership regression: each expected fault is bounded
 * to a child touching exactly one byte; the parent requires SIGSEGV. */
#include "runtime.h"
#include <assert.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>
extern int32_t rt_transient_raw_promote(uintptr_t);
extern int64_t rt_mem_guard_stats(void);
static void expect_reclaimed(volatile unsigned char *p) {
    pid_t child = fork();
    assert(child >= 0);
    if (child == 0) { volatile unsigned char v = *p; (void)v; _exit(0); }
    int status = 0;
    assert(waitpid(child, &status, 0) == child);
    assert(WIFSIGNALED(status) && WTERMSIG(status) == SIGSEGV);
}
int main(void) {
    struct rlimit no_core = {0, 0};
    assert(setrlimit(RLIMIT_CORE, &no_core) == 0);
    assert(setenv("SIMPLE_MEM_GUARD_RATE", "1", 1) == 0);
    assert(rt_transient_array_scope_begin());
    unsigned char *erased = rt_alloc(8);
    assert(erased != NULL);
    rt_free(erased);
    assert(!rt_transient_raw_owner_query(erased, NULL, NULL));
    assert(rt_transient_array_scope_end());
    expect_reclaimed(erased);
    assert(rt_transient_array_scope_begin());
    unsigned char *owned = rt_alloc(8);
    unsigned char *promoted = rt_alloc(8);
    assert(owned && promoted);
    *promoted = 91;
    assert(rt_transient_raw_promote((uintptr_t)promoted) == 1);
    assert(rt_transient_array_scope_pause());
    unsigned char *borrowed = rt_alloc(8);
    assert(borrowed);
    *borrowed = 92;
    assert(rt_transient_array_scope_end());
    assert(*promoted == 91 && *borrowed == 92);
    assert(!rt_transient_raw_owner_query(owned, NULL, NULL));
    assert(!rt_transient_raw_owner_query(promoted, NULL, NULL));
    assert(!rt_transient_raw_owner_query(borrowed, NULL, NULL));
    expect_reclaimed(owned);
    rt_free(promoted);
    rt_free(borrowed);
    expect_reclaimed(promoted);
    expect_reclaimed(borrowed);
    assert(rt_mem_guard_stats() >= 4);
    assert(rt_transient_array_scope_begin());
    assert(!rt_transient_array_scope_begin());
    assert(rt_transient_array_scope_end());
    assert(!rt_transient_array_scope_end());
    puts("PASS guarded owned reclaim, tombstone clear, promotion, paused borrowed, explicit free");
    return 0;
}

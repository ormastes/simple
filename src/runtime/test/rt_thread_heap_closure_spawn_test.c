/* Isolated-thread spawn must run a registered heap closure (clang + lld; never GCC):
 * clang -O2 -flto -fuse-ld=lld \
 *   src/runtime/test/rt_thread_heap_closure_spawn_test.c \
 *   src/runtime/runtime_memtrack.c -o rt_thread_heap_closure_spawn_test.exe
 *
 * bug: seed_jit_spawned_thread_never_runs_join_segv_2026-11-09 (C twin of
 * PR #8082). A native Simple closure value is a TAG_HEAP-tagged
 * RtCoreClosure {kind, func_ptr=boxed `(closure, tagged) -> tagged`, ...}:
 * word 0 is the kind/scope header, not an entry. spl_worker_callable used to
 * read word 0 as the entry, so spawn failed (header < 4096) or jumped into
 * the header. The runtime_native.c closure API is modelled here with the
 * same layout and registry contract (rt_closure_func_ptr answers 0 for any
 * word that is not a registered closure). */
#ifdef NDEBUG
#error Assertions must remain enabled
#endif
#include <assert.h>
#include "../runtime_thread.c"

typedef struct {
    uint8_t kind;
    uint8_t reserved[3];
    uint32_t transient_scope_id;
    int64_t func_ptr;
    int64_t capture_count;
    int64_t captures[1];
} TestClosure;

/* Tagged-int boxing used by the join path (runtime_value contract). */
int64_t rt_value_int(int64_t v) { return v << 3; }
int64_t rt_value_unbox_int(int64_t v) { return v >> 3; }

static TestClosure registered;
static int64_t retains, releases;

static TestClosure* test_closure(int64_t value) {
    if (((uint64_t)value & TAG_MASK) != TAG_HEAP) return NULL;
    TestClosure* c = (TestClosure*)(uintptr_t)((uint64_t)value & ~(uint64_t)TAG_MASK);
    return c == &registered ? c : NULL;
}
int64_t rt_closure_func_ptr(int64_t closure) {
    TestClosure* c = test_closure(closure);
    return c ? c->func_ptr : 0;
}
int64_t rt_closure_retain(int64_t closure) {
    if (!test_closure(closure)) return 0;
    __atomic_add_fetch(&retains, 1, __ATOMIC_SEQ_CST);
    return 1;
}
int64_t rt_closure_release(int64_t closure) {
    if (!test_closure(closure)) return 0;
    __atomic_add_fetch(&releases, 1, __ATOMIC_SEQ_CST);
    return 1;
}

/* Boxed entry: the tagged closure is the hidden first argument and worker
 * arguments stay tagged. */
static int64_t boxed_add_capture(int64_t closure, int64_t tagged) {
    TestClosure* c = test_closure(closure);
    if (!c) return -1;
    return ((((tagged >> 3) + c->captures[0])) << 3);
}
static int64_t boxed_add2(int64_t closure, int64_t a, int64_t b) {
    TestClosure* c = test_closure(closure);
    if (!c) return -1;
    return (((a >> 3) + (b >> 3) + c->captures[0]) << 3);
}

int main(void) {
    registered.kind = 0x06;
    registered.transient_scope_id = 0;
    registered.func_ptr = (int64_t)(intptr_t)&boxed_add_capture;
    registered.capture_count = 1;
    registered.captures[0] = 100;
    int64_t closure = (int64_t)((uint64_t)(uintptr_t)&registered | TAG_HEAP);

    int64_t h = rt_thread_spawn_isolated(closure, 5 << 3);
    if (h == 0) {
        fputs("FAIL: spawn rejected a registered heap closure (word 0 read as entry)\n", stderr);
        return 1;
    }
    int64_t r = rt_thread_join(h);
    rt_thread_free(h);
    if (r != (105 << 3)) {
        fprintf(stderr, "FAIL: closure result %lld, want %lld\n", (long long)r, (long long)(105 << 3));
        return 1;
    }

    registered.func_ptr = (int64_t)(intptr_t)&boxed_add2;
    h = rt_thread_spawn_isolated_with_args(closure, 2 << 3, 3 << 3);
    assert(h != 0);
    r = rt_thread_join(h);
    rt_thread_free(h);
    if (r != (105 << 3)) {
        fprintf(stderr, "FAIL: 2-arg closure result %lld\n", (long long)r);
        return 1;
    }
    /* The closure is pinned for the worker and released exactly once each. */
    if (retains != 2 || releases != 2) {
        fprintf(stderr, "FAIL: pins retains=%lld releases=%lld\n", (long long)retains, (long long)releases);
        return 1;
    }
    puts("PASS rt_thread_heap_closure_spawn_test");
    return 0;
}

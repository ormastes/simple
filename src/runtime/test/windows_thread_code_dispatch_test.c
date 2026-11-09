/* Native Windows regression (clang + lld; never GCC):
 * clang -O2 -flto -fuse-ld=lld \
 *   src/runtime/test/windows_thread_code_dispatch_test.c \
 *   src/runtime/runtime_memtrack.c -o windows_thread_code_dispatch_test.exe
 * Include the real owner to exercise its private address classifier too.
 * Whole-program optimization removes unrelated pool entrypoints; no runtime
 * dependency stubs or replacement implementations are linked. */
#ifdef NDEBUG
#error Assertions must remain enabled
#endif
#ifndef _WIN32
#error This regression exercises Windows VirtualQuery and CreateThread
#endif
#include <assert.h>
#include "../runtime_thread.c"

/* No registered runtime closures in this regression: the registry answers
 * "not a closure" for every word (runtime_native.c contract), so dispatch
 * falls through to the raw-address / record paths under test. */
int64_t rt_closure_func_ptr(int64_t closure) { (void)closure; return 0; }
int64_t rt_closure_retain(int64_t closure) { (void)closure; return 0; }
int64_t rt_closure_release(int64_t closure) { (void)closure; return 0; }

static int64_t __attribute__((aligned(16))) raw_worker(int64_t data) {
    return data + 8;
}

static int64_t closure_worker(int64_t env, int64_t data) {
    return ((int64_t *)(intptr_t)env)[1] + data;
}

int main(void) {
    int64_t raw = (int64_t)(intptr_t)&raw_worker;
    static int64_t closure[2];
    closure[0] = (int64_t)(intptr_t)&closure_worker;
    closure[1] = 10;
    assert((raw & TAG_MASK) == 0);
    if (!rt_native_address_is_code(raw)) {
        fputs("FAIL: raw worker address classified as closure data\n", stderr);
        return 1;
    }
    assert(!rt_native_address_is_code((int64_t)(intptr_t)closure));
    assert(!rt_native_address_is_code(0));
    assert(!rt_native_address_is_code(1));
    void *page = VirtualAlloc(NULL, 4096, MEM_COMMIT | MEM_RESERVE, PAGE_READWRITE);
    assert(page);
    assert(!rt_native_address_is_code((int64_t)(intptr_t)page));
    DWORD previous;
    assert(VirtualProtect(page, 4096, PAGE_EXECUTE_READ, &previous));
    assert(rt_native_address_is_code((int64_t)(intptr_t)page));
    assert(VirtualProtect(page, 4096, PAGE_EXECUTE_READ | PAGE_GUARD, &previous));
    assert(!rt_native_address_is_code((int64_t)(intptr_t)page));
    assert(VirtualProtect(page, 4096, PAGE_NOACCESS, &previous));
    assert(!rt_native_address_is_code((int64_t)(intptr_t)page));
    assert(VirtualFree(page, 0, MEM_RELEASE));
    assert(!rt_native_address_is_code((int64_t)(intptr_t)page));
    /* The spawner states the closure-word kind (RT_WORKER_CLOSURE_*). */
    int64_t h = rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_ADDRESS, raw, 34);
    assert(h);
    assert(rt_thread_join(h) == 42);
    rt_thread_free(h);
    h = rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_ADDRESS, (int64_t)(intptr_t)closure, 32);
    assert(h);
    assert(rt_thread_join(h) == 42);
    rt_thread_free(h);
    /* Simple-facing entry: an int-tagged code word is a raw-ABI worker. */
    h = rt_thread_spawn_isolated(raw << 3, 34 << 3);
    assert(h);
    assert(rt_thread_join(h) == 42);
    rt_thread_free(h);
    /* A record word naming no committed memory is rejected, never read. */
    assert(rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_ADDRESS, INT64_C(0x0000123000000000), 1) == 0);
    h = rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_ADDRESS, (int64_t)(intptr_t)closure, 32);
    assert(h);
    assert(rt_thread_join(h) == 42);
    rt_thread_free(h);
    puts("windows_thread_code_dispatch: PASS");
    return 0;
}

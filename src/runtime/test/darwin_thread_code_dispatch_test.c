/* Native macOS/Darwin regression:
 * clang -O2 -std=gnu11 -Wall -Wextra -Werror -I src/runtime -I src/runtime/platform \
 *   src/runtime/test/darwin_thread_code_dispatch_test.c \
 *   src/runtime/runtime_memtrack.c -lpthread \
 *   -o darwin_thread_code_dispatch_test
 * Include the real owner to exercise its private address classifier too. */
#if !defined(__APPLE__)
#include <stdio.h>
int main(void) {
    puts("SKIP: darwin_thread_code_dispatch_test requires macOS/Darwin");
    return 77;
}
#else
#ifdef NDEBUG
#error Assertions must remain enabled
#endif
#include <assert.h>
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <unistd.h>
#include "../runtime_thread.c"

/* Darwin executable links require concrete providers for the optional weak
 * hooks normally supplied by the Rust packing runtime and thread_pool.spl. */
void simple_note_user_threads_started(void) {}
void worker_loop_entry(int64_t pool_id) {
    fprintf(stderr, "FAIL: unexpected Simple worker_loop_entry(%lld)\n", (long long)pool_id);
    abort();
}

/* No registered runtime closures in this regression: the registry answers
 * "not a closure" for every word (runtime_native.c contract), so dispatch
 * falls through to the raw-address / record paths under test. */
#ifndef SIMPLE_TEST_CORE_RUNTIME /* c-runtime test kind: the real registry owner links */
int64_t rt_closure_func_ptr(int64_t closure) { (void)closure; return 0; }
int64_t rt_closure_retain(int64_t closure) { (void)closure; return 0; }
int64_t rt_closure_release(int64_t closure) { (void)closure; return 0; }
#endif

static int64_t __attribute__((aligned(16))) raw_worker(int64_t data) {
    return data + 8;
}

static int64_t closure_worker(int64_t env, int64_t data) {
    return ((int64_t *)(intptr_t)env)[1] + data;
}

/* Initialized static data lives in __DATA,__data; uninitialized closure below
 * lives in __DATA,__bss. Neither has VM_PROT_EXECUTE. */
static int64_t static_data_record[2] = { 1, 2 };

static void *map_exec_pages(size_t bytes) {
    void *p = mmap(NULL, bytes, PROT_READ | PROT_EXEC, MAP_PRIVATE | MAP_ANON, -1, 0);
#ifdef MAP_JIT
    if (p == MAP_FAILED) {
        p = mmap(NULL, bytes, PROT_READ | PROT_WRITE | PROT_EXEC,
                 MAP_PRIVATE | MAP_ANON | MAP_JIT, -1, 0);
    }
#endif
    return p;
}

int main(void) {
    int64_t raw = (int64_t)(intptr_t)&raw_worker;
    static int64_t closure[2];
    closure[0] = (int64_t)(intptr_t)&closure_worker;
    closure[1] = 10;
    assert((raw & TAG_MASK) == 0);
    assert(((int64_t)(intptr_t)closure & TAG_MASK) == 0);

    if (!rt_native_address_is_code(raw)) {
        fputs("FAIL: raw worker address classified as non-code\n", stderr);
        return 1;
    }
    if (rt_native_address_is_code((int64_t)(intptr_t)static_data_record)) {
        fputs("FAIL: initialized static __DATA address classified as code\n", stderr);
        return 1;
    }
    if (rt_native_address_is_code((int64_t)(intptr_t)closure)) {
        fputs("FAIL: static closure record in __DATA/__bss classified as code\n", stderr);
        return 1;
    }
    if (rt_native_address_is_code((int64_t)(intptr_t)closure | (int64_t)TAG_HEAP)) {
        fputs("FAIL: TAG_HEAP static closure address classified as code\n", stderr);
        return 1;
    }

    /* dyld shared cache code vs data live inside nested VM submaps; the probe
     * must recurse into submaps rather than stopping at top-level protection. */
    void *shared_code = dlsym(RTLD_DEFAULT, "puts");
    void *shared_data = dlsym(RTLD_DEFAULT, "__stdoutp");
    assert(shared_code != NULL);
    assert(shared_data != NULL);
    if (!rt_native_address_is_code((int64_t)(intptr_t)&puts)) {
        fputs("FAIL: shared-cache &puts classified as non-code\n", stderr);
        return 1;
    }
    if (!rt_native_address_is_code((int64_t)(intptr_t)shared_code)) {
        fputs("FAIL: shared-cache dlsym(puts) classified as non-code\n", stderr);
        return 1;
    }
    if (rt_native_address_is_code((int64_t)(intptr_t)&stdout)) {
        fputs("FAIL: shared-cache &stdout classified as code\n", stderr);
        return 1;
    }
    if (rt_native_address_is_code((int64_t)(intptr_t)shared_data)) {
        fputs("FAIL: shared-cache dlsym(__stdoutp) classified as code\n", stderr);
        return 1;
    }

#if defined(__aarch64__)
    /* Top-byte TBI tag is stripped before probing Mach VM regions. */
    int64_t tagged_raw = (int64_t)(((uint64_t)raw) | (UINT64_C(0x42) << 56));
    int64_t tagged_shared_code = (int64_t)(((uint64_t)(uintptr_t)shared_code) | (UINT64_C(0x42) << 56));
    int64_t tagged_data = (int64_t)(((uint64_t)(uintptr_t)static_data_record) | (UINT64_C(0x42) << 56));
    int64_t tagged_sentinel = (int64_t)((UINT64_C(0x42) << 56) | 1ULL);
    assert(rt_native_address_is_code(tagged_raw));
    assert(rt_native_address_is_code(tagged_shared_code));
    assert(!rt_native_address_is_code(tagged_data));
    assert(!rt_native_address_is_code(tagged_sentinel));
#endif

    /* Small sentinel values must be rejected. */
    assert(!rt_native_address_is_code(0));
    assert(!rt_native_address_is_code(1));
    assert(!rt_native_address_is_code(4095));

    long page_size_l = sysconf(_SC_PAGESIZE);
    assert(page_size_l > 0);
    size_t page_size = (size_t)page_size_l;

    /* RW-only mmap page must not be classified as code. */
    void *rw_page = mmap(NULL, page_size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
    assert(rw_page != MAP_FAILED);
    assert(!rt_native_address_is_code((int64_t)(intptr_t)rw_page));

    /* Executable mmap page (PROT_READ | PROT_EXEC, or MAP_JIT fallback) must be classified as code. */
    void *rx_page = map_exec_pages(page_size);
    assert(rx_page != MAP_FAILED);
    assert(rt_native_address_is_code((int64_t)(intptr_t)rx_page));

    /* Removing execute permission (PROT_NONE) and unmapping on rx_page flips classification to false. */
    assert(mprotect(rx_page, page_size, PROT_NONE) == 0);
    assert(!rt_native_address_is_code((int64_t)(intptr_t)rx_page));
    assert(munmap(rx_page, page_size) == 0);
    assert(!rt_native_address_is_code((int64_t)(intptr_t)rx_page));

    /* Guard optional RW->RX transition (may be refused under Hardened Runtime). */
    if (mprotect(rw_page, page_size, PROT_READ | PROT_EXEC) == 0) {
        assert(rt_native_address_is_code((int64_t)(intptr_t)rw_page));
        assert(mprotect(rw_page, page_size, PROT_NONE) == 0);
        assert(!rt_native_address_is_code((int64_t)(intptr_t)rw_page));
    }
    assert(munmap(rw_page, page_size) == 0);
    assert(!rt_native_address_is_code((int64_t)(intptr_t)rw_page));

    /* Deterministic gap-advance check: unmap page 0 while page 1 stays RX so
     * mach_vm_region_recurse advances addr to page 1; page 0 must still fail. */
    void *two_pages = map_exec_pages(2 * page_size);
    assert(two_pages != MAP_FAILED);
    char *page0 = (char *)two_pages;
    char *page1 = page0 + page_size;
    assert(rt_native_address_is_code((int64_t)(intptr_t)page0));
    assert(rt_native_address_is_code((int64_t)(intptr_t)page1));
    assert(munmap(page0, page_size) == 0);
    assert(!rt_native_address_is_code((int64_t)(intptr_t)page0));
    assert(rt_native_address_is_code((int64_t)(intptr_t)page1));
    assert(munmap(page1, page_size) == 0);
    assert(!rt_native_address_is_code((int64_t)(intptr_t)page1));

    /* Direct raw-address dispatch. */
    int64_t h = rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_ADDRESS, raw, 34);
    assert(h);
    assert(rt_thread_join(h) == 42);
    rt_thread_free(h);

    /* Direct static closure-record dispatch (ADDRESS kind). */
    h = rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_ADDRESS, (int64_t)(intptr_t)closure, 32);
    assert(h);
    assert(rt_thread_join(h) == 42);
    rt_thread_free(h);

    /* Simple-facing VALUE entry: bare code address fast path. */
    h = rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_VALUE, raw, 34);
    assert(h);
    assert(rt_thread_join(h) == 42);
    rt_thread_free(h);

    /* Simple-facing VALUE entry: TAG_HEAP static closure record (exercises both probe sites). */
    h = rt_thread_spawn_isolated_kind(RT_WORKER_CLOSURE_VALUE,
                                      (int64_t)(intptr_t)closure | (int64_t)TAG_HEAP, 32);
    assert(h);
    assert(rt_thread_join(h) == 42);
    rt_thread_free(h);

    /* Simple-facing entry: an int-tagged code word is a raw-ABI worker. */
    h = rt_thread_spawn_isolated(raw << 3, 34 << 3);
    assert(h);
    assert(rt_thread_join(h) == 42);
    rt_thread_free(h);

    puts("darwin_thread_code_dispatch: PASS");
    return 0;
}
#endif

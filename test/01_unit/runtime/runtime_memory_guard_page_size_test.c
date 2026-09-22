/* Standalone header contract: layout arithmetic, cached discovery, native VM.
 * cc -std=gnu11 -O2 -Wall -Wextra -Werror -Wno-unused-function FILE -o TEST */
#include <assert.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/wait.h>
#include <signal.h>

static long test_page;
static unsigned queries;
static long guard_sysconf(int name) {
    assert(name == _SC_PAGESIZE);
    queries++;
    return test_page;
}
#define sysconf guard_sysconf
#include "../../../src/runtime/runtime_memory_guard.h"
#undef sysconf

static void layout(size_t page) {
    assert(rt_mem_guard_mapping_size(1, page) == page * 3);
    assert(rt_mem_guard_mapping_size(37, page) == page * 3);
    assert(rt_mem_guard_mapping_size(page, page) == page * 3);
    assert(rt_mem_guard_mapping_size(page + 1, page) == page * 4);
    size_t capacity = ((size_t)PTRDIFF_MAX / page - 2) * page;
    assert(rt_mem_guard_mapping_size(capacity, page) == capacity + 2 * page);
    assert(rt_mem_guard_mapping_size(capacity + 1, page) == 0);
    assert(rt_mem_guard_mapping_size(SIZE_MAX, page) == 0);
    assert(rt_mem_guard_mapping_size(SIZE_MAX - page, page) == 0);
    for (size_t size = 1; size <= 2 * page + 1; size++) {
        size_t length = rt_mem_guard_mapping_size(size, page);
        size_t trailing = length - page;
        assert(length % page == 0 && trailing % page == 0);
        assert(trailing - size >= page && trailing - size < 2 * page);
    }
}

static void traps(uint8_t *ptr) {
    pid_t pid = fork();
    assert(pid >= 0);
    if (pid == 0) {
        *(volatile uint8_t *)ptr = 7;
        _exit(0);
    }
    int status;
    assert(waitpid(pid, &status, 0) == pid);
    assert(WIFSIGNALED(status));
#if defined(__APPLE__)
    assert(WTERMSIG(status) == SIGSEGV || WTERMSIG(status) == SIGBUS);
#else
    assert(WTERMSIG(status) == SIGSEGV);
#endif
}

int main(void) {
    layout(4096);
    layout(16384);
    assert(rt_mem_guard_mapping_size(0, 4096) == 0);
    assert(rt_mem_guard_mapping_size(1, 0) == 0);
    assert(rt_mem_guard_mapping_size(1, SIZE_MAX) == 0);
    test_page = -1;
    assert(rt_mem_guard_page_size() == 0);
    assert(rt_mem_guard_page_size() == 0 && queries == 1);
    assert(rt_mem_guard_alloc_sampled(37) == NULL);
    atomic_store(&rt_mem_guard_page_size_cached, 0);
    test_page = sysconf(_SC_PAGESIZE);
    assert(test_page > 0);
    assert(rt_mem_guard_page_size() == (size_t)test_page);
    assert(rt_mem_guard_page_size() == (size_t)test_page && queries == 2);
    assert(rt_mem_guard_alloc_sampled(SIZE_MAX) == NULL);
    uint8_t *ptr = rt_mem_guard_alloc_sampled(37);
    assert(ptr != NULL && rt_mem_guard_is_slot(ptr));
    RtMemGuardSlot *slot = rt_mem_guard_find(ptr);
    assert(slot->map_len == 3 * (size_t)test_page);
    assert((uintptr_t)(ptr + 37) % (size_t)test_page == 0);
    ptr[0] = 1; ptr[36] = 2;
    assert(ptr[0] + ptr[36] == 3);
    traps(ptr + 37);
    assert(rt_mem_guard_free_sampled(ptr) == 1);
    traps(ptr);
    assert(rt_mem_guard_free_sampled(ptr) == 0);
    /* Exercise the FIFO boundary so eviction uses the original map length. */
    for (unsigned i = 0; i < RT_MEM_GUARD_FREE_RING_CAP; i++) {
        uint8_t *next = rt_mem_guard_alloc_sampled(37);
        assert(next && rt_mem_guard_free_sampled(next));
    }
    assert(!rt_mem_guard_is_slot(ptr));
    assert(rt_mem_guard_stats_native() == RT_MEM_GUARD_FREE_RING_CAP + 1);
    assert(queries == 2);
    printf("PASS: 4KiB/16KiB boundaries, overflow, cached discovery, native guards and FIFO; host page=%ld\n", test_page);
}

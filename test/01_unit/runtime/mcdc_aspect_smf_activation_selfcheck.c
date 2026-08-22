#define _GNU_SOURCE
#include <assert.h>
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/mman.h>
#include <time.h>
#include <unistd.h>
#include "../../../src/runtime/runtime_mcdc_v1.h"

#define ITERATIONS 1000000u

static uint64_t allocation_count;
void *__real_malloc(size_t);
void *__real_calloc(size_t, size_t);
void *__real_realloc(void *, size_t);
void __real_free(void *);
void *__wrap_malloc(size_t n) { ++allocation_count; return __real_malloc(n); }
void *__wrap_calloc(size_t n, size_t s) { ++allocation_count; return __real_calloc(n, s); }
void *__wrap_realloc(void *p, size_t n) { ++allocation_count; return __real_realloc(p, n); }
void __wrap_free(void *p) { __real_free(p); }

/* runtime_coverage_core.c's report wrapper dependency is not exercised here. */
int64_t rt_string_new(const uint8_t *bytes, uint64_t len) {
    (void)bytes; (void)len;
    return 0;
}

static uint64_t elapsed_ns(struct timespec a, struct timespec b) {
    return (uint64_t)(b.tv_sec - a.tv_sec) * UINT64_C(1000000000) +
           (uint64_t)(b.tv_nsec - a.tv_nsec);
}

int main(void) {
    struct timespec begin, end;
    struct rusage usage;
    volatile uint64_t address_sink = 0;
    volatile int32_t status_sink = 0;

    const uint64_t collector = rt_mcdc_compiled_target_address_v1();
    assert(collector != 0);
    const uint64_t handle = rt_mcdc_dynamic_register_target_v1(collector, 991);
    assert(handle > 1);
    assert(rt_mcdc_dynamic_unregister_target_v1(handle, 991) == 0);

    /* Synthetic retained-SMF code shape: jmp rel32 to an in-mapping absolute
     * import thunk. This exercises the same relocation formula and W^X
     * transition as the Simple loader without requiring a Simple executable. */
    const long page_size = sysconf(_SC_PAGESIZE);
    assert(page_size > 0);
    uint8_t *mapped = mmap(NULL, (size_t)page_size, PROT_READ | PROT_WRITE,
                           MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    assert(mapped != MAP_FAILED);
    mapped[0] = 0xE9; /* jmp rel32 */
    const size_t thunk_offset = 5;
    mapped[thunk_offset + 0] = 0x49; /* movabs r11, imm64 */
    mapped[thunk_offset + 1] = 0xBB;
    memcpy(mapped + thunk_offset + 2, &collector, sizeof(collector));
    mapped[thunk_offset + 10] = 0x41; /* jmp r11 */
    mapped[thunk_offset + 11] = 0xFF;
    mapped[thunk_offset + 12] = 0xE3;
    const intptr_t displacement =
        (intptr_t)(mapped + thunk_offset) - (intptr_t)(mapped + 5);
    assert(displacement >= INT32_MIN && displacement <= INT32_MAX);
    const int32_t rel32 = (int32_t)displacement;
    memcpy(mapped + 1, &rel32, sizeof(rel32));
    assert(mprotect(mapped, (size_t)page_size, PROT_READ | PROT_EXEC) == 0);
    SimpleMcdcDynamicTargetV1 relocated = NULL;
    uintptr_t mapped_raw = (uintptr_t)mapped;
    memcpy(&relocated, &mapped_raw, sizeof(relocated));
    assert(relocated != NULL);
    assert(relocated(1, 1, 1, 1, 0, 0) ==
           rt_mcdc_record_compiled_vector_v1(1, 1, 1, 1, 0, 0));
    assert(munmap(mapped, (size_t)page_size) == 0);

    allocation_count = 0;
    assert(clock_gettime(CLOCK_MONOTONIC, &begin) == 0);
    for (unsigned i = 0; i < ITERATIONS; ++i)
        address_sink ^= rt_mcdc_compiled_target_address_v1();
    assert(clock_gettime(CLOCK_MONOTONIC, &end) == 0);
    const uint64_t resolve_ns = elapsed_ns(begin, end);

    assert(clock_gettime(CLOCK_MONOTONIC, &begin) == 0);
    for (unsigned i = 0; i < ITERATIONS; ++i)
        status_sink |= rt_mcdc_dynamic_vector_patchpoint_v1(1, 1, 1, 1, 1, 1);
    assert(clock_gettime(CLOCK_MONOTONIC, &end) == 0);
    const uint64_t idle_ns = elapsed_ns(begin, end);
    assert(status_sink == 0);
    assert(allocation_count == 0);
    assert(getrusage(RUSAGE_SELF, &usage) == 0);
    printf("PASS smf_relocated_call=1 iterations=%u resolve_mean_ns=%" PRIu64
           " disarmed_mean_ns=%" PRIu64 " maxrss_kib=%ld heap_allocations=%" PRIu64
           " sink=%" PRIu64 "\n",
           ITERATIONS, resolve_ns / ITERATIONS, idle_ns / ITERATIONS,
           usage.ru_maxrss, allocation_count, address_sink);
    return 0;
}

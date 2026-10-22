#include "runtime_alloc_observer.h"
#if defined(SIMPLE_ALLOC_OBSERVER_V1) && SIMPLE_ALLOC_OBSERVER_V1
#include <errno.h>
#include <limits.h>
/* These anchors fail the link if either canonical owner was not instrumented. */
extern const volatile int rt_alloc_observer_memory_owner_v1;
extern const volatile int rt_alloc_observer_native_owner_v1;
typedef struct {
    uint64_t total, baseline;
    unsigned baseline_valid, invalid;
} RtAllocObserverV1;
/* Only startup-linked executables are admitted. No late dlopen TLS resolution. */
static _Thread_local RtAllocObserverV1 observer
    __attribute__((tls_model("initial-exec")));

static int owners_admitted_v1(void) {
    /* Volatile reads keep both owner relocations in every retained measurement
     * closure, even when coverage() is removed by function-section GC. */
    return rt_alloc_observer_memory_owner_v1 == 1 &&
           rt_alloc_observer_native_owner_v1 == 1;
}

void rt_alloc_observer_success_v1(void) {
    if (observer.total == UINT64_MAX) observer.invalid = 1;
    else observer.total++;
}
void rt_alloc_probe_reset_v1(void) {
    observer.baseline = observer.total;
    observer.baseline_valid = owners_admitted_v1();
}
int64_t rt_alloc_probe_count_v1(void) {
    if (!owners_admitted_v1() || observer.invalid || !observer.baseline_valid) return -1;
    uint64_t delta = observer.total - observer.baseline;
    /* Signed 61-bit immediate payload: snapshots must never require boxing. */
    if (delta > ((UINT64_C(1) << 60) - 1)) return -1;
    return (int64_t)delta;
}
int64_t rt_alloc_probe_coverage_v1(void) {
    if (rt_alloc_observer_memory_owner_v1 != 1 ||
        rt_alloc_observer_native_owner_v1 != 1) return 0;
    return RT_ALLOC_PROBE_COVERAGE_V1;
}
void* rt_observed_malloc_v1(size_t size) {
    void* result = malloc(size);
    int saved_errno = errno;
    if (result) rt_alloc_observer_success_v1();
    errno = saved_errno;
    return result;
}
void* rt_observed_calloc_v1(size_t count, size_t size) {
    void* result = calloc(count, size);
    int saved_errno = errno;
    if (result) rt_alloc_observer_success_v1();
    errno = saved_errno;
    return result;
}
void* rt_observed_realloc_v1(void* ptr, size_t size) {
    void* result = realloc(ptr, size);
    int saved_errno = errno;
    if (result) rt_alloc_observer_success_v1();
    errno = saved_errno;
    return result;
}
#else
void rt_alloc_probe_reset_v1(void) {}
int64_t rt_alloc_probe_count_v1(void) { return -1; }
int64_t rt_alloc_probe_coverage_v1(void) { return 0; }
#endif

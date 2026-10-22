/* Focused native diagnostic, not compiled-Simple interval qualification.
 * Include the implementation only to test private overflow state; no public setter.
 * Link canonical instrumented runtime_native/runtime_memory objects with gc-sections.
 */
#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <stdlib.h>
#include "../../../src/runtime/runtime_alloc_observer.c"
extern void* rt_alloc(int64_t);
extern void rt_free(void*);
extern int8_t rt_transient_array_scope_begin(void);
extern int8_t rt_transient_array_scope_end(void);
extern int64_t rt_value_int(int64_t);
extern int64_t rt_value_float(double);

int main(void) {
#if defined(SIMPLE_ALLOC_OBSERVER_V1) && SIMPLE_ALLOC_OBSERVER_V1
    assert(rt_alloc_probe_coverage_v1() == RT_ALLOC_PROBE_COVERAGE_V1);
    assert(rt_alloc_probe_count_v1() == -1);
    rt_alloc_probe_reset_v1();
    errno = EDOM;
    void* p = rt_observed_malloc_v1(16);
    assert(p && errno == EDOM && rt_alloc_probe_count_v1() == 1);
    void* q = rt_observed_calloc_v1(4, 8);
    assert(q && ((uint8_t*)q)[0] == 0 && rt_alloc_probe_count_v1() == 2);
    p = rt_observed_realloc_v1(p, 32);
    assert(p && rt_alloc_probe_count_v1() == 3);
    free(p); free(q);
    assert(rt_alloc_probe_count_v1() == 3);
    rt_alloc_probe_reset_v1();
    volatile size_t impossible = SIZE_MAX;
    assert(rt_observed_calloc_v1(impossible, impossible) == NULL);
    assert(rt_alloc_probe_count_v1() == 0);
    p = rt_observed_malloc_v1(0);
    assert(rt_alloc_probe_count_v1() == (p != NULL));
    free(p);
    rt_alloc_probe_reset_v1();
    p = rt_observed_realloc_v1(NULL, 0);
    assert(rt_alloc_probe_count_v1() == (p != NULL));
    free(p);
    rt_alloc_probe_reset_v1();
    p = rt_alloc(32);
    assert(p && rt_alloc_probe_count_v1() > 0);
    rt_free(p);
    /* Native float and epoch-nanosecond boxing must remain observable. */
    assert(rt_transient_array_scope_begin());
    rt_alloc_probe_reset_v1();
    (void)rt_value_int(INT64_C(1792500000000000000));
    (void)rt_value_float(1.5);
    assert(rt_alloc_probe_count_v1() >= 2);
    assert(rt_transient_array_scope_end());
    observer.total = UINT64_MAX;
    rt_alloc_probe_reset_v1();
    rt_alloc_observer_success_v1();
    assert(rt_alloc_probe_count_v1() == -1);
    rt_alloc_probe_reset_v1();
    assert(rt_alloc_probe_count_v1() == -1);
#else
    rt_alloc_probe_reset_v1();
    assert(rt_alloc_probe_coverage_v1() == 0);
    assert(rt_alloc_probe_count_v1() == -1);
#endif
    return 0;
}

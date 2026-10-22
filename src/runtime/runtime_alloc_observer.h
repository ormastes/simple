#ifndef SIMPLE_RUNTIME_ALLOC_OBSERVER_H
#define SIMPLE_RUNTIME_ALLOC_OBSERVER_H
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

/* Version 1: malloc/calloc/realloc + sampled guard mmap; not whole-process coverage. */
#define RT_ALLOC_PROBE_COVERAGE_V1 INT64_C(65551)
int64_t rt_alloc_probe_coverage_v1(void);
void rt_alloc_probe_reset_v1(void);
int64_t rt_alloc_probe_count_v1(void);
#if defined(SIMPLE_ALLOC_OBSERVER_V1) && SIMPLE_ALLOC_OBSERVER_V1
#if !defined(__linux__) || !defined(__GNUC__) || !defined(SIMPLE_RUNTIME_MEMORY_OWNER)
#error "allocation observer v1 requires startup-linked Linux GNU C and canonical memory owner"
#endif
#define RT_ALLOC_OBSERVER_LOCAL __attribute__((visibility("hidden")))
RT_ALLOC_OBSERVER_LOCAL void rt_alloc_observer_success_v1(void);
RT_ALLOC_OBSERVER_LOCAL void* rt_observed_malloc_v1(size_t size);
RT_ALLOC_OBSERVER_LOCAL void* rt_observed_calloc_v1(size_t count, size_t size);
RT_ALLOC_OBSERVER_LOCAL void* rt_observed_realloc_v1(void* ptr, size_t size);
#else
/* No branch, call, TLS or state in disabled allocation paths. */
#define rt_observed_malloc_v1 malloc
#define rt_observed_calloc_v1 calloc
#define rt_observed_realloc_v1 realloc
#define rt_alloc_observer_success_v1() ((void)0)
#endif
#endif

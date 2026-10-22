/* Caller-first definitions must fail strict profile linking, even under GC. */
#include <stdint.h>
#include <stdlib.h>
#if defined(CONFLICT_ALLOCATOR)
void* rt_alloc(int64_t bytes) { return malloc((size_t)bytes); }
#else
int64_t rt_alloc_probe_count_v1(void) { return 0; }
#endif

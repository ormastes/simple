/* Deliberately omit coverage(): reset/count must retain owner admission. */
#include <assert.h>
#include "../../../src/runtime/runtime_alloc_observer.h"
extern void* rt_alloc(int64_t);
extern void rt_free(void*);

int main(void) {
    rt_alloc_probe_reset_v1();
    void* p = rt_alloc(32);
    assert(p);
#if defined(SIMPLE_ALLOC_OBSERVER_V1) && SIMPLE_ALLOC_OBSERVER_V1
    assert(rt_alloc_probe_count_v1() > 0);
#else
    assert(rt_alloc_probe_count_v1() == -1);
#endif
    rt_free(p);
    return 0;
}

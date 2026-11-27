/* Exercise either real native session owner through its public scalar ABI. */
#include "runtime.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if defined(__GLIBC__)
#include <malloc.h>
#if __GLIBC_PREREQ(2, 33)
#define HAS_MALLINFO2 1
#endif
static unsigned trim_calls;
int __real_malloc_trim(size_t);
int __wrap_malloc_trim(size_t pad) {
    assert(pad == 0);
    trim_calls++;
    return __real_malloc_trim(pad);
}
#endif
extern uint32_t rt_session_heap_begin(void);
extern int8_t rt_session_heap_end(uint32_t);
extern uint32_t rt_session_heap_id(void);

int main(void) {
    SplArray *survivor = rt_array_new(4);
    assert(survivor && rt_array_push(survivor, rt_value_int(123)));
    assert(!rt_session_heap_end(0));
    uint32_t session = rt_session_heap_begin();
    assert(session && !rt_session_heap_begin());
    assert(!rt_session_heap_end(session + 1));
    assert(rt_transient_array_scope_begin());
    assert(!rt_session_heap_end(session));
    assert(rt_session_heap_id() == session);
    assert(rt_transient_array_scope_pause());
    assert(!rt_session_heap_end(session));
    assert(rt_transient_array_scope_end());
#if defined(__GLIBC__)
    assert(trim_calls == 0);
#endif
#if defined(HAS_MALLINFO2)
    struct mallinfo2 before = mallinfo2();
#endif
    for (int i = 0; i < 8192; i++) {
        SplArray *owned = rt_array_new(1024);
        assert(owned);
        /* Touch every backing page; zeroed allocation alone may stay lazy. */
        int64_t value = rt_value_int(i);
        for (int j = 0; j < 1024; j++) assert(rt_array_push(owned, value));
    }
    unsigned char *pin = malloc(32);
    assert(pin);
    memset(pin, 71, 32);
#if defined(HAS_MALLINFO2)
    struct mallinfo2 allocated = mallinfo2();
    assert(allocated.uordblks > before.uordblks + 32 * 1024 * 1024);
#endif
    assert(rt_session_heap_end(session));
    assert(!rt_session_heap_id());
    assert(!rt_session_heap_end(session));
    assert(rt_array_get(survivor, 0) == rt_value_int(123));
    for (int i = 0; i < 32; i++) assert(pin[i] == 71);
#if defined(__GLIBC__)
    assert(trim_calls == 1);
#endif
#if defined(HAS_MALLINFO2)
    struct mallinfo2 reclaimed = mallinfo2();
    assert(reclaimed.uordblks < allocated.uordblks - 32 * 1024 * 1024);
    printf("allocator live bytes: before=%zu allocated=%zu reclaimed=%zu\n",
           before.uordblks, allocated.uordblks, reclaimed.uordblks);
#endif
    uint32_t next = rt_session_heap_begin();
    assert(next && next != session);
    assert(!rt_session_heap_end(session));
    assert(rt_session_heap_end(next));
#if defined(__GLIBC__)
    assert(trim_calls == 2);
#endif
    assert(rt_array_get(survivor, 0) == rt_value_int(123));
    free(pin);
    puts("PASS session reclamation, live survivors, active scope guards, repeat end");
    return 0;
}

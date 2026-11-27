/* Actual Rust runtime archive ABI: large module retirement trims only after cleanup. */
#include "runtime.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#if defined(__GLIBC__)
#include <malloc.h>
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
static void expect_trims(unsigned expected) {
#if defined(__GLIBC__)
    if (trim_calls != expected)
        fprintf(stderr, "trim calls: actual=%u expected=%u\n", trim_calls, expected);
    assert(trim_calls == expected);
#else
    (void)expected;
#endif
}
int main(void) {
    SplArray *unrelated = rt_array_new(4);
    assert(unrelated && rt_array_push(unrelated, rt_value_int(123)));
    assert(!rt_transient_array_scope_end());
    expect_trims(0);
    uint32_t session = rt_session_heap_begin();
    assert(session);
    assert(rt_transient_array_scope_begin());
    SplArray *tiny = rt_array_new(4);
    assert(tiny && rt_array_push(tiny, rt_value_int(7)));
    assert(rt_transient_array_scope_end());
    expect_trims(0);
    assert(rt_transient_array_scope_begin());
    SplArray *promoted = rt_array_new(4);
    assert(promoted && rt_array_push(promoted, rt_value_int(456)));
    /* Rust array ABI returns a tagged RuntimeValue in the pointer-sized word. */
    for (int i = 0; i < 4096; i++) {
        SplArray *owned = rt_array_new(1024);
        assert(owned);
        for (int j = 0; j < 1024; j++)
            assert(rt_array_push(owned, rt_value_int(i)));
    }
    assert(rt_transient_array_scope_pause());
    assert(rt_transient_heap_promote((int64_t)(uintptr_t)promoted));
    assert(!rt_session_heap_end(session));
    expect_trims(0);
    assert(rt_transient_array_scope_end());
    expect_trims(1);
    assert(rt_session_heap_id() == session);
    assert(rt_array_get(promoted, 0) == rt_value_int(456));
    assert(rt_array_get(unrelated, 0) == rt_value_int(123));
    assert(!rt_transient_array_scope_end());
    expect_trims(1);
    assert(rt_session_heap_end(session));
    expect_trims(2);
    assert(!rt_session_heap_end(session));
    assert(!rt_transient_array_scope_end());
    expect_trims(2);
    /* Promotion into an active session transfers ownership to that session;
       promoted is retired at session end and must not be dereferenced here. */
    assert(rt_array_get(unrelated, 0) == rt_value_int(123));
    puts("PASS module reclamation: tiny scope, large scope, live session, promoted/unrelated roots, refused ends");
    return 0;
}

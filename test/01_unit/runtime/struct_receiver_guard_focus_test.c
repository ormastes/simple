#include "runtime.h"

#include <assert.h>
#include <stdint.h>

int main(void) {
    int64_t* receiver = (int64_t*)rt_struct_alloc(16);
    assert(receiver != NULL);
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)receiver, 0, 8) == 1);
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)receiver | 1, 8, 8) == 1);
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)receiver, 9, 8) == 0);
    assert(rt_struct_receiver_valid(INT64_C(0x1800000007), 0, 8) == 0);
    assert(rt_struct_receiver_valid(0, 0, 8) == 0);

    uintptr_t old_receiver = (uintptr_t)receiver;
    receiver = (int64_t*)rt_realloc(receiver, 24);
    assert(receiver != NULL);
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)receiver, 16, 8) == 1);
    if ((uintptr_t)receiver != old_receiver) {
        assert(rt_struct_receiver_valid((int64_t)old_receiver, 0, 8) == 0);
    }

    rt_free(receiver);
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)receiver, 0, 8) == 0);
    return 0;
}

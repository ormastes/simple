#include "runtime.h"

#include <assert.h>
#include <stdint.h>

/* The bootstrap runtime has no rt_realloc implementation.  Keep this focused
 * test linked only with runtime_memory.c so it proves the exact ABI used by
 * Stage2: a tagged struct receiver validates, the declared bound is enforced,
 * and freeing revokes the registry entry. */
int main(void) {
    uint8_t* raw = rt_struct_alloc(16);
    assert(raw != NULL);

    int64_t tagged = (int64_t)((uintptr_t)raw | (uintptr_t)1);
    assert(rt_struct_receiver_valid(tagged, 0, 8) == 1);
    assert(rt_struct_receiver_valid(tagged, 8, 8) == 1);
    assert(rt_struct_receiver_valid(tagged, 9, 8) == 0);

    rt_free(raw);
    assert(rt_struct_receiver_valid(tagged, 0, 8) == 0);
    return 0;
}

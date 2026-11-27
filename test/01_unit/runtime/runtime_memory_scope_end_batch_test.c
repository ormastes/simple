/* Scope-end reclaim of transient raw allocations (runtime_memory.c).
 *
 * Ownership pins: owned allocations are freed exactly once and leave the
 * struct registry; promoted and paused (borrowed) allocations survive with
 * their contents; an explicit free followed by a same-size reallocation is
 * reclaimed once; a new scope can begin afterwards.
 *
 * Cost pin: the reclaim must take the struct-registry write lock once per
 * batch, not once per allocation (that per-free lock was ~2/3 of scope-end
 * time on aarch64: 166 ms -> 57 ms for 1M allocations in rawbench).
 *
 * Build (ASan catches a double free or use-after-free):
 *   clang -fsanitize=address -g -DSIMPLE_RUNTIME_MEMORY_TESTING -I src/runtime \
 *     test/01_unit/runtime/runtime_memory_scope_end_batch_test.c \
 *     src/runtime/runtime_memory.c -lpthread
 */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>

void* rt_struct_alloc(int64_t size);
uint8_t* rt_alloc(int64_t size);
void rt_free(void* ptr);
int8_t rt_struct_receiver_valid(int64_t receiver, int64_t byte_offset, int64_t access_width);
int32_t rt_transient_raw_scope_begin(void);
int32_t rt_transient_raw_scope_pause(void);
int32_t rt_transient_raw_scope_end(void);
int32_t rt_transient_raw_promote(uintptr_t ptr);
int64_t spl_struct_registry_write_locks_v1(void);

enum { OWNED = 6000 };

static int64_t* owned_structs[OWNED];

int main(void) {
    assert(rt_transient_raw_scope_begin() == 1);
    for (int i = 0; i < OWNED; i++) {
        owned_structs[i] = (int64_t*)rt_struct_alloc(16 + 8 * (i % 5));
        assert(owned_structs[i] != NULL);
        owned_structs[i][0] = i;
        assert(rt_alloc(8 + 8 * (i % 7)) != NULL);
    }
    /* Explicit free, then a same-size allocation that may reuse the address. */
    int64_t* freed = (int64_t*)rt_struct_alloc(24);
    rt_free(freed);
    int64_t* reused = (int64_t*)rt_struct_alloc(24);
    assert(reused != NULL);
    reused[0] = -1;

    int64_t* promoted = (int64_t*)rt_struct_alloc(32);
    assert(promoted != NULL);
    promoted[0] = 0x5eed;
    assert(rt_transient_raw_promote((uintptr_t)promoted) == 1);

    assert(rt_transient_raw_scope_pause() == 1);
    int64_t* borrowed = (int64_t*)rt_struct_alloc(32);
    assert(borrowed != NULL);
    borrowed[0] = 0xb0b;

    const int64_t locks_before = spl_struct_registry_write_locks_v1();
    assert(rt_transient_raw_scope_end() == 1);
    const int64_t reclaim_locks = spl_struct_registry_write_locks_v1() - locks_before;

    for (int i = 0; i < OWNED; i++) {
        assert(rt_struct_receiver_valid((int64_t)(uintptr_t)owned_structs[i], 0, 8) == 0);
    }
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)reused, 0, 8) == 0);
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)promoted, 0, 8) == 1);
    assert(promoted[0] == 0x5eed);
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)borrowed, 0, 8) == 1);
    assert(borrowed[0] == 0xb0b);

    /* 2*OWNED+2 owned allocations reclaimed; per-allocation locking took one
     * lock each. Batched reclaim takes one per batch. */
    printf("reclaim_locks=%lld owned_allocations=%d\n", (long long)reclaim_locks, 2 * OWNED + 2);
    assert(reclaim_locks <= (2 * OWNED + 2) / 256 + 2);

    rt_free(promoted);
    rt_free(borrowed);
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)promoted, 0, 8) == 0);

    /* The table is reusable: an empty scope and a small owned scope. */
    assert(rt_transient_raw_scope_begin() == 1);
    assert(rt_transient_raw_scope_end() == 1);
    assert(rt_transient_raw_scope_begin() == 1);
    int64_t* again = (int64_t*)rt_struct_alloc(16);
    assert(again != NULL);
    assert(rt_transient_raw_scope_end() == 1);
    assert(rt_struct_receiver_valid((int64_t)(uintptr_t)again, 0, 8) == 0);
    printf("PASS runtime_memory_scope_end_batch_test\n");
    return 0;
}

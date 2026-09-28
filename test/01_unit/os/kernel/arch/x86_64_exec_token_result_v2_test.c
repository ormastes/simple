/* Included after the production token lifecycle slice by the test runner.
 * No ring transition or privileged CR3 read is executed here. */
#include <assert.h>
#include <limits.h>

int main(void) {
    int64_t out = 123;
    assert(rt_x86_exec_token_take_result_v2(1, 2, 0x3000, &out) == 0);
    assert(out == 123);
    assert(rt_x86_exec_token_install(0, 2, 0x3000) == 0);
    assert(rt_x86_exec_token_install(1, 0, 0x3000) == 0);
    assert(rt_x86_exec_token_install(1, 2, 0xfff) == 0);

    const int64_t statuses[] = {0, -16, -22, -4096, INT64_MIN, INT64_MAX};
    for (unsigned i = 0; i < sizeof(statuses) / sizeof(statuses[0]); ++i) {
        assert(rt_x86_exec_token_install(1, 2, 0x3007) == 1);
        assert(rt_x86_exec_token_install(4, 5, 0x6000) == 0);
        _x86_exec_token_complete_result(statuses[i]);
        /* A completed result still owns the slot until it is consumed. */
        assert(rt_x86_exec_token_install(4, 5, 0x6000) == 0);
        out = 123;
        assert(rt_x86_exec_token_take_result_v2(9, 2, 0x3000, &out) == 0);
        assert(rt_x86_exec_token_take_result_v2(1, 9, 0x3000, &out) == 0);
        assert(rt_x86_exec_token_take_result_v2(1, 2, 0x4000, &out) == 0);
        assert(rt_x86_exec_token_take_result_v2(1, 2, 0x3000, 0) == 0);
        assert(out == 123);
        assert(rt_x86_exec_token_take_result_v2(1, 2, 0x300f, &out) == 1);
        assert(out == statuses[i]);
        out = 123;
        assert(rt_x86_exec_token_take_result_v2(1, 2, 0x3000, &out) == 0);
        assert(out == 123);
    }

    /* v1 remains callable and consumes the same slot, including its legacy
     * sentinel ambiguity. v1/v2 cannot each deliver the same completion. */
    assert(rt_x86_exec_token_install(1, 2, 0x3000) == 1);
    _x86_exec_token_complete_result(-4096);
    assert(rt_x86_exec_token_take_result(9, 2, 0x3000) == -4096);
    assert(rt_x86_exec_token_install(4, 5, 0x6000) == 0);
    assert(rt_x86_exec_token_take_result(1, 2, 0x3000) == -4096);
    assert(rt_x86_exec_token_take_result_v2(1, 2, 0x3000, &out) == 0);
    assert(rt_x86_exec_token_install(4, 5, 0x6000) == 1);
    assert(rt_x86_exec_token_cancel(4, 9, 0x6000) == 0);
    assert(rt_x86_exec_token_cancel(4, 5, 0x6000) == 1);
    assert(rt_x86_exec_token_take_result_v2(4, 5, 0x6000, &out) == 0);

    /* Exercise the bounded owner slot and exact raw-read function used by
     * Simple. No host-only free hides the target's bump-allocator behavior. */
    uint64_t first_slot = 0;
    for (unsigned i = 0; i < sizeof(statuses) / sizeof(statuses[0]); ++i) {
        uint64_t slot = rt_x86_exec_token_result_slot_acquire_v2();
        assert(slot != 0);
        if (i == 0) first_slot = slot;
        assert(slot == first_slot);
        assert(rt_x86_exec_token_result_slot_acquire_v2() == 0);
        assert(rt_x86_exec_token_result_slot_release_v2(0) == 0);
        assert(rt_x86_exec_token_result_slot_release_v2(slot + 8) == 0);
        assert(rt_x86_exec_token_result_slot_acquire_v2() == 0);
        assert(rt_x86_exec_token_install(1, 2, 0x3000) == 1);
        _x86_exec_token_complete_result(statuses[i]);
        assert(rt_x86_exec_token_take_result_v2(
            1, 2, 0x3000, (int64_t *)(uintptr_t)slot) == 1);
        assert((int64_t)rt_volatile_read_u64(slot) == statuses[i]);
        assert(rt_x86_exec_token_result_slot_release_v2(slot) == 1);
        assert(rt_x86_exec_token_result_slot_release_v2(slot) == 0);
    }
    return 0;
}

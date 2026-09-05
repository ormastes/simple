#include <assert.h>
#include <stdint.h>
#include "../../../../../examples/09_embedded/simple_os/arch/arm32/boot/arm32_user_transition_contract.h"

/* Queue-completion simulator: exercises bounded short-fill accumulation and
 * malformed completion rejection without touching host MMIO. */
static int simulate(const uint32_t *lengths, uint32_t count)
{
    uint32_t received = 0;
    if (count > 16u) return 0;
    for (uint32_t i = 0; i < count && received < 16u; ++i) {
        uint32_t next = 0;
        if (!arm32_rng_accumulate_len_v16(received, lengths[i], &next))
            return 0;
        received = next;
    }
    return received == 16u;
}

int main(void)
{
    const uint32_t one[] = {16};
    const uint32_t short_fill[] = {3, 1, 4, 2, 6};
    const uint32_t zero[] = {8, 0, 8};
    const uint32_t overrun[] = {15, 2};
    const uint32_t incomplete[] = {7, 8};
    uint32_t too_many[17];
    for (uint32_t i = 0; i < 17; ++i) too_many[i] = 1;
    assert(simulate(one, 1));
    assert(simulate(short_fill, 5));
    assert(!simulate(zero, 3));
    assert(!simulate(overrun, 2));
    assert(!simulate(incomplete, 2));
    assert(!simulate(too_many, 17));
    return 0;
}

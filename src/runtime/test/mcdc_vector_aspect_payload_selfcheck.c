#include <assert.h>
#include <stdint.h>

static uint64_t seen[6];

int32_t rt_mcdc_record_compiled_vector_v1(uint64_t decision_id,
                                          uint32_t condition_count,
                                          uint64_t source_digest,
                                          uint64_t evaluated_mask,
                                          uint64_t true_mask,
                                          uint8_t outcome) {
    seen[0] = decision_id;
    seen[1] = condition_count;
    seen[2] = source_digest;
    seen[3] = evaluated_mask;
    seen[4] = true_mask;
    seen[5] = outcome;
    return 27;
}

#include "../aspect/mcdc_vector_aspect_v1.c"

int main(void) {
    assert(rt_mcdc_aspect_vector_v1__abi_u64_u32_u64_u64_u64_u8_i32_v1 == 1u);
    assert(rt_mcdc_aspect_vector_v1(11, 5, 13, 7, 3, 1) == 27);
    assert(seen[0] == 11 && seen[1] == 5 && seen[2] == 13);
    assert(seen[3] == 7 && seen[4] == 3 && seen[5] == 1);
    return 0;
}

#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

extern uint64_t starfive_dtb_policy_select(uint64_t, uint64_t, uint64_t);
extern uint64_t starfive_dtb_policy_select_coverage(uint64_t, uint64_t, uint64_t);
extern void starfive_dtb_policy_coverage_reset(void);
extern uint64_t starfive_dtb_policy_coverage_mask(void);
extern uint64_t starfive_dtb_policy_coverage_required(void);
extern uint64_t starfive_dtb_policy_coverage_decisions(void);

int main(void) {
    static const uint64_t vectors[][4] = {
        {0, 0, 0, 0},
        {0, UINT64_C(0xd00dfeed), 0, 0},
        {0, 0, UINT64_C(0xd00dfeed), UINT64_C(0x42200000)},
        {0, UINT64_C(0xd00dfeed), UINT64_C(0xd00dfeed), UINT64_C(0x42200000)},
        {UINT64_C(0x12345000), 0, 0, 0},
        {UINT64_C(0x12345000), 0, UINT64_C(0xd00dfeed), UINT64_C(0x42200000)},
        {UINT64_C(0x12345000), UINT64_C(0xd00dfeed), 0, UINT64_C(0x12345000)},
        {UINT64_C(0x12345000), UINT64_C(0xd00dfeed), UINT64_C(0xd00dfeed), UINT64_C(0x12345000)},
    };
    starfive_dtb_policy_coverage_reset();
    for (unsigned i = 0; i < sizeof vectors / sizeof vectors[0]; ++i) {
        uint64_t selected = starfive_dtb_policy_select_coverage(
            vectors[i][0], vectors[i][1], vectors[i][2]);
        if (selected != vectors[i][3]) return 1;
    }
    if (starfive_dtb_policy_coverage_decisions() != 3) return 2;
    if (starfive_dtb_policy_coverage_required() != UINT64_C(63)) return 3;
    if (starfive_dtb_policy_coverage_mask() != UINT64_C(63)) return 4;
    puts("starfive_dtb_mixed_link=PASS branch_outcomes=6/6");
    return 0;
}

#ifndef SIMPLEOS_ARM64_USER_MAP_CONTRACT_H
#define SIMPLEOS_ARM64_USER_MAP_CONTRACT_H
#include <stdint.h>

enum arm64_user_map_reason_v1 {
    ARM64_USER_MAP_OK = 0, ARM64_USER_MAP_UNKNOWN_ROOT = 1,
    ARM64_USER_MAP_ZERO_ROOT = 2, ARM64_USER_MAP_VA_UNALIGNED = 3,
    ARM64_USER_MAP_PA_UNALIGNED = 4, ARM64_USER_MAP_L1_EXHAUSTED = 5,
    ARM64_USER_MAP_L2_EXHAUSTED = 6, ARM64_USER_MAP_L3_EXHAUSTED = 7
};

static uint32_t arm64_user_map_precondition_reason(int root_known, uint64_t root,
                                                   uint64_t va, uint64_t pa)
{
    if (!root_known) return ARM64_USER_MAP_UNKNOWN_ROOT;
    if (!root) return ARM64_USER_MAP_ZERO_ROOT;
    if (va & 4095ULL) return ARM64_USER_MAP_VA_UNALIGNED;
    if (pa & 4095ULL) return ARM64_USER_MAP_PA_UNALIGNED;
    return ARM64_USER_MAP_OK;
}
#endif

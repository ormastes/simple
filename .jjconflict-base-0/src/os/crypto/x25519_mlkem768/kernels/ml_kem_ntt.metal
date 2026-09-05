#include <metal_stdlib>

using namespace metal;

// Fixed FIPS 203 ML-KEM NTT constants.  The host ABI supplies only the
// polynomial count at buffer(2), so this immutable table is deliberately part
// of the digest-pinned shader rather than caller-controlled device memory.
constant int kModulus = 3329;
constant int kZetas[128] = {
    1, 1729, 2580, 3289, 2642, 630, 1897, 848, 1062, 1919, 193, 797,
    2786, 3260, 569, 1746, 296, 2447, 1339, 1476, 3046, 56, 2240, 1333,
    1426, 2094, 535, 2882, 2393, 2879, 1974, 821, 289, 331, 3253, 1756,
    1197, 2304, 2277, 2055, 650, 1977, 2513, 632, 2865, 33, 1320, 1915,
    2319, 1435, 807, 452, 1438, 2868, 1534, 2402, 2647, 2617, 1481, 648,
    2474, 3110, 1227, 910, 17, 2761, 583, 2649, 1637, 723, 2288, 1100,
    1409, 2662, 3281, 233, 756, 2156, 3015, 3050, 1703, 1651, 2789, 1789,
    1847, 952, 1461, 2687, 939, 2308, 2437, 2388, 733, 2337, 268, 641,
    1584, 2298, 2037, 3220, 375, 2549, 2090, 1645, 1063, 319, 2773, 757,
    2099, 561, 2466, 2594, 2804, 1092, 403, 1026, 1143, 2150, 2775, 886,
    1722, 1212, 1874, 1029, 2110, 2935, 885, 2154
};

inline int modq(int value) {
    int residue = value % kModulus;
    return residue < 0 ? residue + kModulus : residue;
}

kernel void x25519_mlkem768_ntt_forward_metal(
        device const int *input [[buffer(0)]],
        device int *output [[buffer(1)]],
        constant uint &polynomial_count [[buffer(2)]],
        uint tid [[thread_position_in_threadgroup]],
        uint polynomial [[threadgroup_position_in_grid]]) {
    if (polynomial >= polynomial_count || tid >= 256) return;

    threadgroup int stage_a[256];
    threadgroup int stage_b[256];
    uint base = polynomial * 256;
    stage_a[tid] = modq(input[base + tid]);
    threadgroup_barrier(mem_flags::mem_threadgroup);

    bool current_is_a = true;
    for (uint stage = 0; stage < 7; stage += 1) {
        uint len = 128 >> stage;
        if (tid < 128) {
            uint group = tid / len;
            uint lower_index = group * (len << 1) + (tid % len);
            uint upper_index = lower_index + len;
            int lower = current_is_a ? stage_a[lower_index] : stage_b[lower_index];
            int upper = current_is_a ? stage_a[upper_index] : stage_b[upper_index];
            int product = modq(kZetas[(1 << stage) + group] * upper);
            if (current_is_a) {
                stage_b[lower_index] = modq(lower + product);
                stage_b[upper_index] = modq(lower - product);
            } else {
                stage_a[lower_index] = modq(lower + product);
                stage_a[upper_index] = modq(lower - product);
            }
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
        current_is_a = !current_is_a;
    }
    output[base + tid] = current_is_a ? stage_a[tid] : stage_b[tid];
}

kernel void x25519_mlkem768_ntt_inverse_metal(
        device const int *input [[buffer(0)]],
        device int *output [[buffer(1)]],
        constant uint &polynomial_count [[buffer(2)]],
        uint tid [[thread_position_in_threadgroup]],
        uint polynomial [[threadgroup_position_in_grid]]) {
    if (polynomial >= polynomial_count || tid >= 256) return;

    threadgroup int stage_a[256];
    threadgroup int stage_b[256];
    uint base = polynomial * 256;
    stage_a[tid] = modq(input[base + tid]);
    threadgroup_barrier(mem_flags::mem_threadgroup);

    bool current_is_a = true;
    for (uint stage = 0; stage < 7; stage += 1) {
        uint len = 2 << stage;
        if (tid < 128) {
            uint group = tid / len;
            uint lower_index = group * (len << 1) + (tid % len);
            uint upper_index = lower_index + len;
            int lower = current_is_a ? stage_a[lower_index] : stage_b[lower_index];
            int upper = current_is_a ? stage_a[upper_index] : stage_b[upper_index];
            int next_lower = modq(lower + upper);
            int next_upper = modq(kZetas[(127 >> stage) - group] *
                modq(upper - lower));
            if (current_is_a) {
                stage_b[lower_index] = next_lower;
                stage_b[upper_index] = next_upper;
            } else {
                stage_a[lower_index] = next_lower;
                stage_a[upper_index] = next_upper;
            }
        }
        threadgroup_barrier(mem_flags::mem_threadgroup);
        current_is_a = !current_is_a;
    }
    int value = current_is_a ? stage_a[tid] : stage_b[tid];
    output[base + tid] = modq(value * 3303);
}

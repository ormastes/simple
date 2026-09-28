#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern int64_t spl_wffi_call_i32_i64_u32_u32_f64_bits(int64_t fptr,
    int64_t arg0, int64_t arg1, int64_t arg2, int64_t arg3_bits);

static double expected_scale;

static int32_t resize_probe(int64_t handle, uint32_t width,
                            uint32_t height, double scale) {
    if (handle != 73 || width != 800u || height != 600u || scale != expected_scale)
        return -7;
    return 0;
}

static int64_t bits_of(double value) {
    int64_t bits;
    memcpy(&bits, &value, sizeof(bits));
    return bits;
}

int main(void) {
    expected_scale = 1.0;
    if (spl_wffi_call_i32_i64_u32_u32_f64_bits(
            (int64_t)(uintptr_t)&resize_probe, 73, 800, 600, bits_of(1.0)) != 0)
        return 1;
    expected_scale = 1.25;
    if (spl_wffi_call_i32_i64_u32_u32_f64_bits(
            (int64_t)(uintptr_t)&resize_probe, 73, 800, 600, bits_of(1.25)) != 0)
        return 2;
    if (spl_wffi_call_i32_i64_u32_u32_f64_bits(
            (int64_t)(uintptr_t)&resize_probe, 73, 800, 601, bits_of(1.25)) != -7)
        return 3;
    if (spl_wffi_call_i32_i64_u32_u32_f64_bits(0, 73, 800, 600, bits_of(1.0)) != -1)
        return 4;
    if (spl_wffi_call_i32_i64_u32_u32_f64_bits(
            (int64_t)(uintptr_t)&resize_probe, 73, -1, 600, bits_of(1.0)) != -1)
        return 5;
    puts("mixed-abi-bridge: PASS");
    return 0;
}

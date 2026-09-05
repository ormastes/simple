#include <math.h>
#include <stdint.h>
#include <string.h>

#include "runtime_any_ops.h"
#include "runtime_string_ffi.h"

static uint8_t copied_text[32];
static uint64_t copied_len;
int64_t rt_string_new(const uint8_t *data, uint64_t len) {
    copied_len = len;
    if (len > sizeof(copied_text)) return 0;
    if (data && len != 0) memcpy(copied_text, data, (size_t)len);
    return 77;
}

static int is_float(int64_t value) { return (value & 7) == 2; }
int8_t rt_value_is_float(int64_t value) { return is_float(value); }
int64_t rt_value_int(int64_t value) { return value << 3; }
int64_t rt_value_as_int(int64_t value) { return value >> 3; }
int64_t rt_value_float(double value) {
    uint64_t bits;
    memcpy(&bits, &value, sizeof(bits));
    return (int64_t)((bits & ~UINT64_C(7)) | UINT64_C(2));
}
double rt_value_as_float(int64_t value) {
    uint64_t bits = (uint64_t)value & ~UINT64_C(7);
    double result;
    memcpy(&result, &bits, sizeof(result));
    return result;
}

int main(void) {
    int64_t eight = rt_value_int(8), three = rt_value_int(3);
    if (rt_value_as_int(rt_any_sub(eight, three)) != 5) return 1;
    if (rt_value_as_int(rt_any_mul(eight, three)) != 24) return 2;
    if (rt_value_as_int(rt_any_div(eight, three)) != 2) return 3;
    if (rt_value_as_int(rt_any_mod(eight, three)) != 2) return 4;
    if (rt_value_as_int(rt_any_div(eight, rt_value_int(0))) != 0) return 5;
    if (rt_any_lt(three, eight) != 1 || rt_any_ge(three, eight) != 0) return 7;
    int64_t half = rt_value_float(0.5), two = rt_value_float(2.0);
    if (fabs(rt_value_as_float(rt_any_mul(half, two)) - 1.0) > 1e-12) return 8;
    if (rt_any_le(half, two) != 1 || rt_any_gt(half, two) != 0) return 9;
    char foreign[] = "hello";
    if (rt_cstring_to_text((int64_t)(uintptr_t)foreign) != 77) return 10;
    if (copied_len != 5 || memcmp(copied_text, "hello", 5) != 0) return 11;
    foreign[0] = 'X';
    if (copied_text[0] != 'h') return 12;
    if (rt_cstring_to_text(0) != 77 || copied_len != 0) return 13;
    return 0;
}

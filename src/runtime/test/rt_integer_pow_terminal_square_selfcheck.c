/* Link with runtime_core_intrinsics.c; run with signed-overflow sanitization. */
#include <assert.h>
#include <stdint.h>
#include <stdio.h>

extern int64_t __simple_pow(int64_t base, int64_t exp);

int main(void) {
    assert(__simple_pow(INT64_MAX, 1) == INT64_MAX);
    assert(__simple_pow(INT64_MIN, 1) == INT64_MIN);
    assert(__simple_pow(INT64_C(3037000500), 1) == INT64_C(3037000500));
    assert(__simple_pow(2, 62) == INT64_C(4611686018427387904));
    assert(__simple_pow(-2, 63) == INT64_MIN);
    assert(__simple_pow(3, 20) == INT64_C(3486784401));
    assert(__simple_pow(-3, 3) == -27);
    assert(__simple_pow(-3, 4) == 81);
    assert(__simple_pow(0, 0) == 1);
    assert(__simple_pow(INT64_MAX, 0) == 1);
    assert(__simple_pow(0, 9) == 0);
    assert(__simple_pow(7, -1) == 0);
    assert(__simple_pow(7, INT64_MIN) == 0);
    assert(__simple_pow(-1, INT64_MAX) == -1);
    puts("PASS: 14 integer power terminal-square controls");
    return 0;
}

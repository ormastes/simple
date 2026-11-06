/* Exercise the selected real provider only in the defined signed-i64 domain. */
#include <assert.h>
#include <stdint.h>
int64_t __simple_pow(int64_t base, int64_t exp);
int main(void) {
    assert(__simple_pow(INT64_MAX, 1) == INT64_MAX);
    assert(__simple_pow(INT64_MIN, 1) == INT64_MIN);
    assert(__simple_pow(INT64_MAX, 0) == 1);
    assert(__simple_pow(INT64_MIN, 0) == 1);
    assert(__simple_pow(0, 0) == 1);
    assert(__simple_pow(2, -1) == 0);
    assert(__simple_pow(INT64_MIN, INT64_MIN) == 0);
    assert(__simple_pow(2, 62) == INT64_C(4611686018427387904));
    assert(__simple_pow(-2, 63) == INT64_MIN);
    assert(__simple_pow(-3, 3) == -27);
    assert(__simple_pow(-3, 4) == 81);
    assert(__simple_pow(0, INT64_MAX) == 0);
    assert(__simple_pow(1, INT64_MAX) == 1);
    assert(__simple_pow(-1, INT64_MAX) == -1);
    return 0;
}

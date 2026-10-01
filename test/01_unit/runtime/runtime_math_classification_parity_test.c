#include "runtime.h"

#include <assert.h>
#include <math.h>
#include <stdbool.h>

int main(void) {
    const double finite_values[] = {0.0, -0.0, 1.0, -3.5, 1.0e308, 0x1p-1074};
    for (unsigned i = 0; i < sizeof(finite_values) / sizeof(finite_values[0]); ++i) {
        const double value = finite_values[i];
        assert(!rt_math_is_nan(value));
        assert(!rt_math_is_inf(value));
        assert(rt_math_is_finite(value));
    }

    assert(rt_math_is_nan(NAN));
    assert(!rt_math_is_inf(NAN));
    assert(!rt_math_is_finite(NAN));

    assert(!rt_math_is_nan(INFINITY));
    assert(rt_math_is_inf(INFINITY));
    assert(rt_math_is_inf(-INFINITY));
    assert(!rt_math_is_finite(INFINITY));
    assert(!rt_math_is_finite(-INFINITY));
    return 0;
}

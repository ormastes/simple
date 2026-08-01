/* AC-1 demo plugin fixture.
 * WFFI calling convention: positional scalar arguments.
 * simple_demo_add returns a + b. */

#include <stdint.h>

int64_t simple_demo_add(int64_t a, int64_t b) {
    return a + b;
}

double simple_demo_add_scaled(double a, double b, double scale) {
    return (a + b) * scale;
}

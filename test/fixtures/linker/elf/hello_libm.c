/* Library-search fixture: a libm call (sqrt) + a libc call (printf), exit 42.
   Links only when the linker resolves `-lm` to the host libm.so GNU ld script
   (or libm.so.6) and libc.so.6 -- a bare object+libc link leaves `sqrt`
   undefined. Used by native_linking_internal_spec's NativeLinkConfig.libraries
   specs (lane F1). */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>

double v = 1764.0;

int main(void) {
    printf("sqrt=%d\n", (int) sqrt(v));
    exit(42);
}

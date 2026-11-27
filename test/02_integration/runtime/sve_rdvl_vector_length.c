/* SVE vector length is measured with `rdvl`, fail-closed off SVE hosts.
 *
 * Native (x86_64 / non-SVE) run: the query must return 0, never a guess.
 *   clang -I src/runtime test/02_integration/runtime/sve_rdvl_vector_length.c -o t && ./t
 * Cross-compile (no aarch64 host): proves the rdvl path assembles.
 *   clang --target=aarch64-linux-gnu -march=armv8-a+sve -I src/runtime -S -o - \
 *     test/02_integration/runtime/sve_rdvl_vector_length.c | grep rdvl
 * Not run on real SVE hardware.
 */
#include <stdio.h>
#include "rt_sve_vl.h"

int main(void) {
    int32_t bytes = rt_sve_vl_bytes_measured();
#if defined(__aarch64__) && defined(__linux__)
    /* On SVE hardware: 16..256 and a multiple of 16; on a non-SVE aarch64 host: 0. */
    if (bytes != 0 && (bytes < 16 || bytes > 256 || bytes % 16 != 0)) {
        printf("FAIL: rdvl returned invalid VL %d bytes\n", (int)bytes);
        return 1;
    }
#else
    if (bytes != 0) {
        printf("FAIL: non-SVE host reported VL %d bytes\n", (int)bytes);
        return 1;
    }
#endif
    printf("PASS: sve vl bytes=%d\n", (int)bytes);
    return 0;
}

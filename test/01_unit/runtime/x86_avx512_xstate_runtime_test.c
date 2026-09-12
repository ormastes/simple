#include "runtime_simd_dispatch.h"
#include "runtime.h"

#include <stdint.h>
#include <stdio.h>

static int expect_false(const char *name, int value) {
    if (!value) return 0;
    fprintf(stderr, "%s unexpectedly admitted AVX-512 OS state\n", name);
    return 1;
}

int main(void) {
    const uint32_t xsave_osxsave = (1U << 26) | (1U << 27);
    int failed = 0;

    if (!simd_x86_avx512_os_state_usable_from_raw(xsave_osxsave, UINT64_C(0xE6))) {
        fprintf(stderr, "complete XSAVE/OSXSAVE/XCR0 state was rejected\n");
        failed = 1;
    }
    failed |= expect_false("missing-xsave",
        simd_x86_avx512_os_state_usable_from_raw(1U << 27, UINT64_C(0xE6)));
    failed |= expect_false("missing-osxsave",
        simd_x86_avx512_os_state_usable_from_raw(1U << 26, UINT64_C(0xE6)));
    failed |= expect_false("missing-xmm",
        simd_x86_avx512_os_state_usable_from_raw(xsave_osxsave, UINT64_C(0xE4)));
    failed |= expect_false("missing-ymm",
        simd_x86_avx512_os_state_usable_from_raw(xsave_osxsave, UINT64_C(0xE2)));
    failed |= expect_false("missing-opmask",
        simd_x86_avx512_os_state_usable_from_raw(xsave_osxsave, UINT64_C(0xC6)));
    failed |= expect_false("missing-zmm-hi256",
        simd_x86_avx512_os_state_usable_from_raw(xsave_osxsave, UINT64_C(0xA6)));
    failed |= expect_false("missing-hi16-zmm",
        simd_x86_avx512_os_state_usable_from_raw(xsave_osxsave, UINT64_C(0x66)));
    if (failed) return 1;

    printf("x86-avx512-xstate-runtime: host-usable=%d\n",
        rt_x86_avx512_os_state_usable() ? 1 : 0);
    return 0;
}

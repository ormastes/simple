/* Host ISA readback parity: the runtime's public x86 feature predicates must
 * equal an independent CPUID/XGETBV decode on the machine running the test.
 * Bug codegen_isa_sffi_text_abi_misexpansion_2026_10_22 (2026-11-06 evidence).
 *
 * Build/run (x86 host, any GNU-compatible clang/gcc):
 *   cc -O2 -std=gnu11 -ffunction-sections -fdata-sections -Isrc/runtime \
 *      src/runtime/test/rt_host_isa_cpuid_parity_selfcheck.c \
 *      src/runtime/runtime_simd_dispatch.c -Wl,--gc-sections -o parity && ./parity
 * Windows (llvm-mingw clang): COFF lld reports undefined rt_array_* from
 * unrelated dispatch kernels before GC, so add -Wl,-Xlink=-force:unresolved
 * (none of those kernels is reachable from this test).
 * Non-x86 hosts print SKIP and exit 0 (no CPUID to compare against). */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

extern bool rt_simd_has_sse(void);
extern bool rt_simd_has_avx(void);
extern bool rt_simd_has_avx2(void);
extern bool rt_x86_avx512_os_state_usable(void);

#if (defined(__x86_64__) || defined(__i386__)) && (defined(__GNUC__) || defined(__clang__))
#include <cpuid.h>

static int check(const char *name, bool got, bool want) {
    printf("%-14s runtime=%d cpuid=%d\n", name, (int)got, (int)want);
    return got == want ? 0 : 1;
}

int main(void) {
    unsigned a = 0, b = 0, c = 0, d = 0;
    unsigned max_leaf = __get_cpuid_max(0, 0);
    if (max_leaf < 1) {
        puts("FAIL: CPUID leaf 1 unavailable");
        return 2;
    }
    __cpuid_count(1, 0, a, b, c, d);
    const bool osxsave = ((c >> 26) & 3U) == 3U;
    uint64_t xcr0 = 0;
    if (osxsave) {
        unsigned lo = 0, hi = 0;
        __asm__ volatile("xgetbv" : "=a"(lo), "=d"(hi) : "c"(0));
        xcr0 = ((uint64_t)hi << 32) | lo;
    }
    unsigned b7 = 0;
    if (max_leaf >= 7) {
        unsigned a7 = 0, c7 = 0, d7 = 0;
        __cpuid_count(7, 0, a7, b7, c7, d7);
    }
    const bool os_avx = osxsave && (xcr0 & 6U) == 6U;
    const bool want_sse = (d >> 25) & 1U;
    const bool want_avx = ((c >> 28) & 1U) && os_avx;
    const bool want_avx2 = want_avx && ((b7 >> 5) & 1U);
    const bool want_avx512_os = osxsave && (xcr0 & 0xE6U) == 0xE6U;
    printf("cpuid leaf1 ecx=0x%08x edx=0x%08x leaf7 ebx=0x%08x xcr0=0x%llx\n",
           c, d, b7, (unsigned long long)xcr0);
    int bad = 0;
    bad += check("sse", rt_simd_has_sse(), want_sse);
    bad += check("avx", rt_simd_has_avx(), want_avx);
    bad += check("avx2", rt_simd_has_avx2(), want_avx2);
    bad += check("avx512_os", rt_x86_avx512_os_state_usable(), want_avx512_os);
    if (bad) {
        printf("FAIL: %d host ISA readback(s) disagree with CPUID\n", bad);
        return 1;
    }
    puts("PASS: host ISA readback equals CPUID/XGETBV truth (4 predicates)");
    return 0;
}
#else
int main(void) {
    puts("SKIP: not an x86 GNU-compatible host; no CPUID truth to compare");
    return 0;
}
#endif

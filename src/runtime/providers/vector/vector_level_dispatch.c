/* Baseline-compiled level dispatcher for the levelled vector provider. It
 * owns simple_{bitmap,http}_kernel (what bitmap_provider.c calls) and forwards
 * to the highest admitted per-level kernel object. This TU must stay at the
 * architecture baseline: it only probes CPU/OS state and branches.
 *
 * Probe sources (no libc headers needed, so every target compiles):
 *   x86_64 any OS : CPUID + XGETBV (user-mode legal, incl. SimpleOS); macOS
 *                   enables AVX-512 state lazily, so L4 uses hw.optional sysctls
 *   aarch64       : Linux getauxval / FreeBSD elf_aux_info; macOS, Windows and
 *                   SimpleOS have mandatory NEON => L1 (SVE unprobed: scaffold)
 *   riscv64       : Linux getauxval / FreeBSD elf_aux_info 'V'; SimpleOS and
 *                   others => 0 until the kernel exports hwcaps (scaffold) */
#include "vector_level_private.h"
#include <stdatomic.h>

#if defined(__x86_64__) && (defined(__GNUC__) || defined(__clang__))
#include <cpuid.h>
#endif

#if (defined(__aarch64__) || defined(__riscv)) && defined(__linux__)
extern unsigned long getauxval(unsigned long type);
#if defined(__riscv)
extern int prctl(int option, ...);
#endif
static unsigned long hwcap(int second) { return getauxval(second ? 26 : 16); }
#define SIMPLE_VECTOR_HAVE_HWCAP 1
#elif (defined(__aarch64__) || defined(__riscv)) && defined(__FreeBSD__)
extern int elf_aux_info(int aux, void *buf, int buflen);
static unsigned long hwcap(int second) {
    unsigned long value = 0;
    return elf_aux_info(second ? 26 : 25, &value, (int)sizeof(value)) == 0 ? value : 0;
}
#define SIMPLE_VECTOR_HAVE_HWCAP 1
#endif

#if defined(__x86_64__) && defined(__APPLE__)
extern int sysctlbyname(const char *name, void *old, unsigned long *oldlen, void *nw, unsigned long nwlen);
static int darwin_flag(const char *name) {
    int value = 0;
    unsigned long size = sizeof(value);
    return sysctlbyname(name, &value, &size, 0, 0) == 0 && value != 0;
}
#endif

static int probe_level(void) {
#if defined(__x86_64__) && (defined(__GNUC__) || defined(__clang__))
    unsigned int a = 0, b = 0, c1 = 0, d = 0, b7 = 0, c7 = 0, ce = 0;
    if (!__get_cpuid(1, &a, &b, &c1, &d)) return 0;
    if (__get_cpuid_max(0, 0) >= 7) __cpuid_count(7, 0, a, b7, c7, d);
    if (__get_cpuid_max(0x80000000u, 0) >= 0x80000001u) __cpuid(0x80000001u, a, b, ce, d);
    int level = 1; /* SSE2 is architectural on x86-64. */
    const unsigned int v2_c1 = (1u << 0) | (1u << 9) | (1u << 13) | (1u << 19) | (1u << 20) | (1u << 23);
    if ((c1 & v2_c1) != v2_c1 || !(ce & 1u)) return level;
    level = 2;
    /* FMA MOVBE XSAVE OSXSAVE AVX F16C; OSXSAVE gates the xgetbv below. */
    const unsigned int v3_c1 = (1u << 12) | (1u << 22) | (1u << 26) | (1u << 27) | (1u << 28) | (1u << 29);
    const unsigned int v3_b7 = (1u << 3) | (1u << 5) | (1u << 8);
    if ((c1 & v3_c1) != v3_c1 || (b7 & v3_b7) != v3_b7 || !(ce & (1u << 5))) return level;
    unsigned int xlo = 0, xhi = 0;
    __asm__ volatile("xgetbv" : "=a"(xlo), "=d"(xhi) : "c"(0));
    const unsigned long long xcr0 = ((unsigned long long)xhi << 32) | xlo;
    if ((xcr0 & 0x6u) != 0x6u) return level; /* OS saves XMM+YMM */
    level = 3;
    const unsigned int v4_b7 = (1u << 16) | (1u << 17) | (1u << 28) | (1u << 30) | (1u << 31);
    if ((b7 & v4_b7) != v4_b7) return level;
#if defined(__APPLE__)
    if (!darwin_flag("hw.optional.avx512f") || !darwin_flag("hw.optional.avx512bw") ||
            !darwin_flag("hw.optional.avx512dq") || !darwin_flag("hw.optional.avx512vl") ||
            !darwin_flag("hw.optional.avx512cd")) return level;
#else
    if ((xcr0 & 0xe6u) != 0xe6u) return level; /* opmask + ZMM_Hi256 + Hi16_ZMM */
#endif
    return 4;
#elif defined(__aarch64__)
#if defined(SIMPLE_VECTOR_HAVE_HWCAP)
    const unsigned long h = hwcap(0), h2 = hwcap(1);
    if (!(h & (1ul << 1))) return 0;          /* HWCAP_ASIMD */
    if (!(h & (1ul << 22))) return 1;         /* HWCAP_SVE */
    return (h2 & (1ul << 1)) ? 3 : 2;         /* HWCAP2_SVE2 */
#elif defined(__APPLE__) || defined(_WIN32) || defined(__simpleos__)
    return 1;
#else
    return 0;
#endif
#elif defined(__riscv) && __riscv_xlen == 64 && defined(SIMPLE_VECTOR_HAVE_HWCAP)
    if (!(hwcap(0) & (1ul << ('V' - 'A')))) return 0;
#if defined(__linux__)
    /* Linux >= 6.5 may disable V per process: PR_RISCV_V_GET_CONTROL (70),
     * current-state field 1 = OFF. Older kernels (-1) predate the control. */
    const int control = prctl(70, 0, 0, 0, 0);
    if (control >= 0 && (control & 3) == 1) return 0;
#endif
    return 1;
#else
    return 0;
#endif
}

static atomic_int selected_level = -1;

int simple_vector_selected_level(void) {
    int level = atomic_load_explicit(&selected_level, memory_order_acquire);
    if (level >= 0) return level;
    level = probe_level();
#if defined(SIMPLE_VECTOR_FORCE_NO_AVX512) && defined(__x86_64__)
    if (level > 3) level = 3;
#endif
    if (level > SIMPLE_VECTOR_MAX_LEVEL) level = SIMPLE_VECTOR_MAX_LEVEL;
    atomic_store_explicit(&selected_level, level, memory_order_release);
    return level;
}

/* Only levels <= SIMPLE_VECTOR_MAX_LEVEL are referenced, so a capped DSO links
 * (and carries) no kernel object above its cap. */
#if defined(__x86_64__)
#define ARCH_LEVELS 4
#elif defined(__aarch64__)
#define ARCH_LEVELS 3
#elif defined(__riscv) && __riscv_xlen == 64
#define ARCH_LEVELS 1
#else
#define ARCH_LEVELS 0
#endif
#define HAS_LEVEL(n) (ARCH_LEVELS >= (n) && SIMPLE_VECTOR_MAX_LEVEL >= (n))
#if HAS_LEVEL(4)
#define CASE4(fn, ...) case 4: return fn##_l4(__VA_ARGS__);
#else
#define CASE4(fn, ...)
#endif
#if HAS_LEVEL(3)
#define CASE3(fn, ...) case 3: return fn##_l3(__VA_ARGS__);
#else
#define CASE3(fn, ...)
#endif
#if HAS_LEVEL(2)
#define CASE2(fn, ...) case 2: return fn##_l2(__VA_ARGS__);
#else
#define CASE2(fn, ...)
#endif
#if HAS_LEVEL(1)
#define CASE1(fn, ...) case 1: return fn##_l1(__VA_ARGS__);
#else
#define CASE1(fn, ...)
#endif
#define DISPATCH(fn, ...) switch (simple_vector_selected_level()) { \
    CASE4(fn, __VA_ARGS__) CASE3(fn, __VA_ARGS__) CASE2(fn, __VA_ARGS__) \
    CASE1(fn, __VA_ARGS__) default: return UINT64_MAX; }

uint64_t simple_bitmap_kernel(uint32_t op, const uint32_t *left,
        const uint32_t *right, uint32_t *output, size_t words) {
    (void)op; (void)left; (void)right; (void)output; (void)words;
    DISPATCH(simple_bitmap_kernel, op, left, right, output, words)
}

uint64_t simple_http_kernel(uint32_t op, const uint8_t *input, size_t bytes,
        uint8_t needle, int64_t *found) {
    (void)op; (void)input; (void)bytes; (void)needle;
    *found = -1;
    DISPATCH(simple_http_kernel, op, input, bytes, needle, found)
}

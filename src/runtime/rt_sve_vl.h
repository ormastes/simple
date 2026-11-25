/* SVE vector-length measurement for rt_sve_read_vl_bytes.
 *
 * The length is read from the running thread with `rdvl` (bytes), not from
 * the kernel default (/proc/sys/abi/sve_default_vector_length), which can
 * differ from the thread's actual VL after prctl(PR_SVE_SET_VL).
 *
 * Fail-closed: `rdvl` executes only after AT_HWCAP reports SVE, so a non-SVE
 * host returns 0 instead of trapping on SIGILL. Every other target returns 0.
 * `.arch_extension sve` lets the runtime assemble `rdvl` without being built
 * with +sve itself; the HWCAP gate is what keeps it safe.
 */
#ifndef RT_SVE_VL_H
#define RT_SVE_VL_H

#include <stdint.h>

#if defined(__aarch64__) && defined(__linux__)
unsigned long getauxval(unsigned long type); /* <sys/auxv.h>; declared to stay header-light */
#endif

static inline int32_t rt_sve_vl_bytes_measured(void) {
#if defined(__aarch64__) && defined(__linux__)
    uint64_t bytes = 0;
    if ((getauxval(16 /* AT_HWCAP */) & (1UL << 22 /* HWCAP_SVE */)) == 0) return 0;
    __asm__ volatile(".arch_extension sve\n\trdvl %0, #1" : "=r"(bytes));
    if (bytes < 16 || bytes > 256 || bytes % 16 != 0) return 0;
    return (int32_t)bytes;
#else
    return 0;
#endif
}

#endif

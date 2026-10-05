/* Compile baseline-only: optional instructions live in separate kernel TU. */
#include "bitmap_kernel_private.h"
#include "provider_identity.h"
#include <sys/auxv.h>
#include <string.h>
#include <stdatomic.h>
#if defined(__x86_64__) && (defined(__GNUC__) || defined(__clang__))
#include <cpuid.h>
#endif
#ifdef __aarch64__
#include <asm/hwcap.h>
#if defined(SIMPLE_VECTOR_REQUIRE_SVE) && defined(SIMPLE_VECTOR_REQUIRE_SVE2)
#error "select exactly one scalable-vector provider requirement"
#endif
#endif
#define EXPORT __attribute__((visibility("default")))
static atomic_uint_fast64_t vector_iterations;
#ifdef SIMPLE_VECTOR_TEST_OBSERVER
/* Test build only: a constructor reports loading to the harness, never a getter. */
extern void simple_vector_test_loaded(void);
__attribute__((constructor)) static void observed_load(void) { simple_vector_test_loaded(); }
#endif
static int available(void) {
#if defined(__x86_64__) && (defined(__GNUC__) || defined(__clang__))
#ifdef SIMPLE_VECTOR_FORCE_NO_AVX512
    return 0;
#else
    unsigned int eax=0,ebx=0,ecx=0,edx=0;
    if(__get_cpuid_max(0,0)<7 || !__get_cpuid(1,&eax,&ebx,&ecx,&edx)) return 0;
    const unsigned int xsave_osxsave_avx=(1u<<26)|(1u<<27)|(1u<<28);
    if((ecx&xsave_osxsave_avx)!=xsave_osxsave_avx) return 0;
    unsigned int xcr0_lo=0,xcr0_hi=0;
    __asm__ volatile("xgetbv" : "=a"(xcr0_lo), "=d"(xcr0_hi) : "c"(0));
    const uint64_t xcr0=((uint64_t)xcr0_hi<<32)|xcr0_lo;
    if((xcr0&UINT64_C(0xe6))!=UINT64_C(0xe6)) return 0;
    __cpuid_count(7,0,eax,ebx,ecx,edx);
    return (ebx&(1u<<16))!=0;
#endif
#elif defined(__aarch64__)
#if defined(SIMPLE_VECTOR_REQUIRE_SVE2)
    return (getauxval(AT_HWCAP)&HWCAP_SVE)!=0 &&
        (getauxval(AT_HWCAP2)&HWCAP2_SVE2)!=0;
#elif defined(SIMPLE_VECTOR_REQUIRE_SVE)
    return (getauxval(AT_HWCAP)&HWCAP_SVE)!=0;
#else
    return (getauxval(AT_HWCAP)&HWCAP_ASIMD)!=0;
#endif
#elif defined(__riscv)
    return (getauxval(AT_HWCAP)&(1UL<<('V'-'A')))!=0;
#else
    return 0;
#endif
}
/* Diagnostic counter observes executed vector loops; does not activate loader. */
EXPORT uint64_t simple_vector_executed_iterations_v1(void) {
    return atomic_load_explicit(&vector_iterations,memory_order_relaxed);
}
EXPORT int32_t simple_provider_query_v1(uint64_t req,uint64_t res) {
    const uint8_t *q=(const uint8_t *)(uintptr_t)req;
    uint8_t *r=(uint8_t *)(uintptr_t)res;
    if(!q||!r) return 3;
    uint32_t status=0;
    if(simple_vector_rd32(q)!=44) status=3;
    else if(simple_vector_rd64(q+4)!=SIMPLE_VECTOR_KERNELS_V1_INTERFACE) status=1;
    else if(simple_vector_rd32(q+12)!=1) status=2;
    else if(simple_vector_rd32(q+16)!=0) status=7;
    else if(simple_vector_rd64(q+20)!=1 || simple_vector_rd32(q+28) || simple_vector_rd32(q+32)) status=4;
    else if(simple_vector_rd64(q+36)&~UINT64_C(3)) status=5;
    memset(r,0,84); simple_vector_wr32(r,status); simple_vector_wr32(r+12,84);
    if(status) return (int32_t)status;
    static const uint8_t digest[32]=SIMPLE_VECTOR_ABI_DIGEST_BYTES;
    simple_vector_wr32(r+4,1);
    /* Distinct handles carry the granted opcode ceiling, no mutable query state. */
    simple_vector_wr64(r+16,UINT64_C(0x53494d4400000000)|simple_vector_rd64(q+36));
    simple_vector_wr64(r+32,SIMPLE_VECTOR_PROVIDER_ID);
    simple_vector_wr64(r+40,SIMPLE_VECTOR_IMPLEMENTATION_ID);
    memcpy(r+48,digest,32); return 0;
}
static int span(uint64_t p,uint64_t n) {
    if(!n) return p==0;
    return p && !(p&3) && n<=SIMPLE_VECTOR_MAX_SPAN_BYTES &&
        p<=SIMPLE_VECTOR_MAX_ADDRESS-n;
}
static int overlap(uint64_t a,uint64_t b,uint64_t n) {
    return n && a<b+n && b<a+n;
}
EXPORT int64_t simple_vector_apply_v1(int64_t handle,int64_t req,int64_t res) {
    if(req<=0||res<=0) return -1;
    const uint8_t *q=(const uint8_t *)(uintptr_t)req;
    uint8_t *r=(uint8_t *)(uintptr_t)res;
    uint32_t op=simple_vector_rd32(q+4),status=0;
    uint64_t a=simple_vector_rd64(q+8),n=simple_vector_rd64(q+16),
        b=simple_vector_rd64(q+24),bn=simple_vector_rd64(q+32),
        out=simple_vector_rd64(q+40),cap=simple_vector_rd64(q+48),written=0;
    if(simple_vector_rd32(q)!=64) status=SIMPLE_VECTOR_INVALID_REQUEST;
    else if(op!=1&&op!=2) status=SIMPLE_VECTOR_UNSUPPORTED_OPERATION;
    else if(((uint64_t)handle&~UINT64_C(3))!=UINT64_C(0x53494d4400000000)||
            !((uint64_t)handle&(UINT64_C(1)<<(op-1)))) status=SIMPLE_VECTOR_CAPABILITY_DENIED;
    else if(n%4||bn!=n||cap!=n||simple_vector_rd64(q+56)||
            !span(a,n)||!span(b,n)||!span(out,n)||overlap(out,a,n)||overlap(out,b,n))
        status=SIMPLE_VECTOR_RANGE_INVALID;
    else if(!available()) status=SIMPLE_VECTOR_FEATURE_UNAVAILABLE;
    else {
        uint64_t ran=simple_bitmap_kernel(op,(const uint32_t *)(uintptr_t)a,
            (const uint32_t *)(uintptr_t)b,(uint32_t *)(uintptr_t)out,(size_t)(n/4));
        if(ran==UINT64_MAX) status=SIMPLE_VECTOR_EXECUTION_FAILED;
        else { written=n; atomic_fetch_add_explicit(&vector_iterations,ran,memory_order_relaxed); }
    }
    memset(r,0,24); simple_vector_wr32(r,24); simple_vector_wr32(r+4,status);
    simple_vector_wr64(r+8,written); simple_vector_wr64(r+16,UINT64_MAX);
    return 0;
}

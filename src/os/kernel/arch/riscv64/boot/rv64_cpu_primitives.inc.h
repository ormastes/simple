/* rv64_cpu_primitives.inc.h — self-contained RISC-V S-mode primitives shared by
 * the kernel freestanding runtime and the examples boot runtime
 * (examples/09_embedded/simple_os/arch/riscv64/boot/rv64_kernel_primitives.c).
 * Requires spl_i64 / spl_u64 typedefs from the including TU. */

spl_i64 rt_riscv64_syscall(spl_u64 id, spl_u64 arg0, spl_u64 arg1,
                           spl_u64 arg2, spl_u64 arg3, spl_u64 arg4)
{
    register spl_u64 a0 __asm__("a0") = arg0;
    register spl_u64 a1 __asm__("a1") = arg1;
    register spl_u64 a2 __asm__("a2") = arg2;
    register spl_u64 a3 __asm__("a3") = arg3;
    register spl_u64 a4 __asm__("a4") = arg4;
    register spl_u64 a7 __asm__("a7") = id;
    __asm__ volatile("ecall"
                     : "+r"(a0)
                     : "r"(a1), "r"(a2), "r"(a3), "r"(a4), "r"(a7)
                     : "memory");
    return (spl_i64)a0;
}

void rt_riscv64_fence_i(void) { __asm__ volatile("fence.i" ::: "memory"); }

typedef struct RtRiscv64SbiRet {
    spl_i64 error;
    spl_i64 value;
} RtRiscv64SbiRet;

RtRiscv64SbiRet rt_riscv64_sbi_call(spl_u64 ext, spl_u64 fid,
                                     spl_u64 arg0, spl_u64 arg1,
                                     spl_u64 arg2, spl_u64 arg3,
                                     spl_u64 arg4, spl_u64 arg5)
{
    register spl_u64 a0 __asm__("a0") = arg0;
    register spl_u64 a1 __asm__("a1") = arg1;
    register spl_u64 a2 __asm__("a2") = arg2;
    register spl_u64 a3 __asm__("a3") = arg3;
    register spl_u64 a4 __asm__("a4") = arg4;
    register spl_u64 a5 __asm__("a5") = arg5;
    register spl_u64 a6 __asm__("a6") = fid;
    register spl_u64 a7 __asm__("a7") = ext;
    __asm__ volatile("ecall"
                     : "+r"(a0), "+r"(a1)
                     : "r"(a2), "r"(a3), "r"(a4), "r"(a5), "r"(a6), "r"(a7)
                     : "memory");
    RtRiscv64SbiRet result = {(spl_i64)a0, (spl_i64)a1};
    return result;
}


void *rt_memcpy(void *dst, const void *src, spl_i64 n) {
    unsigned char *d = (unsigned char *)dst;
    const unsigned char *s = (const unsigned char *)src;
    if (n <= 0) {
        return dst;
    }
    for (spl_i64 i = 0; i < n; i = i + 1) {
        d[i] = s[i];
    }
    return dst;
}

void *rt_memset(void *dst, signed char val, spl_i64 n) {
    unsigned char *d = (unsigned char *)dst;
    if (n <= 0) {
        return dst;
    }
    for (spl_i64 i = 0; i < n; i = i + 1) {
        d[i] = (unsigned char)val;
    }
    return dst;
}

void rt_load_barrier(void) {
    __atomic_thread_fence(__ATOMIC_ACQUIRE);
}
void rt_store_barrier(void) {
    __atomic_thread_fence(__ATOMIC_RELEASE);
}
/* unsafe_addr_of: identity cast, no allocator/heap dependency — mirrors the
 * hosted implementation exactly (src/runtime/runtime_native.c:4853,
 * `return (uint64_t)value;`). Surfaced as undefined once the rt_volatile
 * family / rt_load_barrier fixes above let the linker get further into this
 * closure. */
spl_u64 unsafe_addr_of(spl_i64 value) {
    return (spl_u64)value;
}

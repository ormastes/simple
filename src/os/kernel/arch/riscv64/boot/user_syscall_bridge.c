/* RV64 user-runtime syscall bridge.
 *
 * This is the userspace link provider for `os.userlib.syscall_raw`.  It is
 * deliberately separate from the kernel freestanding runtime because a user
 * payload must issue an ecall into the live supervisor trap path, while the
 * kernel image owns its own boot/runtime symbols.  Keep the register contract
 * byte-for-byte equivalent to the kernel bridge: syscall id in a7, arguments
 * in a0..a4, and the signed result returned in a0.
 */

typedef long long spl_i64;
typedef unsigned long long spl_u64;

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

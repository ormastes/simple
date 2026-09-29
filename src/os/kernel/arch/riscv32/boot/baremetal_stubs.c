/* RV32 direct-M-mode acquisition bridge.
 *
 * The native linker autodiscovers C runtime files from entry.parent()/boot,
 * and SIMPLE_BOOT_MINIMAL admits only baremetal_stubs.c. Reuse the shared
 * freestanding RISC-V runtime so build/os/simpleos_riscv32.elf links the
 * no-alloc boot support code instead of pulling the hosted allocator stack.
 *
 * This translation unit is deliberately only foreign-runtime include glue.
 * RV32 policy, linker-symbol access, and optional firmware selection live in
 * Pure Simple.  Keep this wrapper in the separate foreign ABI denominator
 * until native-build can name the shared runtime source directly.
 */
#include "../../riscv64/boot/freestanding_runtime.c"

#ifndef RV32_DIRECT_UART_BASE
#define RV32_DIRECT_UART_BASE 0x10000000U
#endif

void rt_riscv_uart_put(rv32_abi_u64 byte) {
    *(volatile rv32_abi_u8 *)RV32_DIRECT_UART_BASE = (rv32_abi_u8)byte;
}

/* The linker keeps this word outside the BSS-clear span.  Every hart checks
 * in with amoadd.w before hart 0 clears BSS. */
extern volatile unsigned int _smp_online_count;
rv32_abi_u64 rt_rv32_smp_online_count(void) {
    return (rv32_abi_u64)_smp_online_count;
}

long long rt_rv32_boot_optional_nvme_fw_selftest(void) __attribute__((weak));
long long rt_rv32_boot_optional_nvme_fw_selftest(void) {
    return 0;
}

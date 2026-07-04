/*
 * RV32 kernel-only native-build bridge.
 *
 * The native linker autodiscovers C runtime files from entry.parent()/boot,
 * and SIMPLE_BOOT_MINIMAL admits only baremetal_stubs.c. Reuse the shared
 * freestanding RISC-V runtime so build/os/simpleos_riscv32.elf links the
 * no-alloc boot support code instead of pulling the hosted allocator stack.
 */
#include "../../riscv64/boot/freestanding_runtime.c"

/* SMP: per-hart atomic check-in counter, storage defined by linker.ld's .smp
 * section (outside the BSS-clear range). Each hart amoadd's it in _start;
 * hart 0 reads it via this accessor to report how many harts came online.
 * rv32-only — lives here (after the shared include) so the rv64 lane, which
 * has no _smp_online_count symbol, is unaffected. */
extern volatile unsigned int _smp_online_count;
unsigned long long rt_rv32_smp_online_count(void) {
    return (unsigned long long)_smp_online_count;
}

long long rt_rv32_boot_optional_nvme_fw_selftest(void) __attribute__((weak));
long long rt_rv32_boot_optional_nvme_fw_selftest(void) {
    return 0;
}

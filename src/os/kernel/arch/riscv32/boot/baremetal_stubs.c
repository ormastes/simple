/*
 * RV32 kernel-only native-build bridge.
 *
 * The native linker autodiscovers C runtime files from entry.parent()/boot,
 * and SIMPLE_BOOT_MINIMAL admits only baremetal_stubs.c. Reuse the shared
 * freestanding RISC-V runtime so build/os/simpleos_riscv32.elf links the
 * no-alloc boot support code instead of pulling the hosted allocator stack.
 */
#include "../../riscv64/boot/freestanding_runtime.c"

/* The linker-owned SMP counter is read by the Pure-Simple RV32 provider.
 * This file retains only the shared freestanding runtime and the weak optional
 * firmware override ABI that cannot be expressed as an ordinary Simple call. */
long long rt_rv32_boot_optional_nvme_fw_selftest(void) __attribute__((weak));
long long rt_rv32_boot_optional_nvme_fw_selftest(void) {
    return 0;
}

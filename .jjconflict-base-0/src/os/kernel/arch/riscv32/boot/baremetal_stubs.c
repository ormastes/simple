/*
 * RV32 kernel-only native-build bridge.
 *
 * The native linker autodiscovers C runtime files from entry.parent()/boot,
 * and SIMPLE_BOOT_MINIMAL admits only baremetal_stubs.c. Reuse the shared
 * freestanding RISC-V runtime so build/os/simpleos_riscv32.elf links the
 * no-alloc boot support code instead of pulling the hosted allocator stack.
 */
#include "../../riscv64/boot/freestanding_runtime.c"

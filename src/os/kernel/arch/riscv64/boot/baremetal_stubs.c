/*
 * RV64 kernel-only native-build bridge.
 *
 * The native linker autodiscovers C runtime files from entry.parent()/boot,
 * and SIMPLE_BOOT_MINIMAL admits only baremetal_stubs.c. Keep the runtime
 * implementation in freestanding_runtime.c and expose it through this
 * conventional filename so build/os/simpleos_riscv64.elf links the no-alloc
 * boot support code.
 */
#include "freestanding_runtime.c"

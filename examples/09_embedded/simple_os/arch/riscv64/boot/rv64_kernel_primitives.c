/* Kernel RISC-V S-mode primitives (SBI/ecall/fence/mem/barriers) for the
 * examples boot runtime. Single source: src/os/kernel/arch/riscv64/boot/. */
typedef long long spl_i64;
typedef unsigned long long spl_u64;
#include "../../../../../../src/os/kernel/arch/riscv64/boot/rv64_cpu_primitives.inc.h"

    .include "src/lib/nogc_async_mut_noalloc/baremetal/riscv_common/semihost_trap.S"
    SIMPLEOS_RISCV_SEMIHOST_TRAP simpleos_rv32_semihost_call, simpleos_rv32_semihost_write0, simpleos_rv32_semihost_exit

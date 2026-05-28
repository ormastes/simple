    .include "src/lib/nogc_async_mut_noalloc/baremetal/riscv_common/semihost_trap.S"
    SIMPLEOS_RISCV_SEMIHOST_TRAP simpleos_rv64_semihost_call, simpleos_rv64_semihost_write0, simpleos_rv64_semihost_exit

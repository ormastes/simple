    .macro SIMPLEOS_ARM_SEMIHOST_CALL
    hlt #0xF000
    .endm

    .macro SIMPLEOS_ARM_SEMIHOST_RETURN
    ret
    .endm

    .macro SIMPLEOS_ARM_SEMIHOST_ARG_WRITE0
    mov x1, x0
    mov x0, #0x04
    .endm

    .macro SIMPLEOS_ARM_SEMIHOST_ARG_EXIT
    mov x1, x0
    mov x0, #0x18
    .endm

    .include "src/lib/nogc_async_mut_noalloc/baremetal/common/arm_semihost_trap.S"
    SIMPLEOS_ARM_SEMIHOST_TRAP simpleos_arm64_semihost_call, simpleos_arm64_semihost_write0, simpleos_arm64_semihost_exit

    .syntax unified
    .thumb

    .macro SIMPLEOS_ARM_SEMIHOST_CALL
    bkpt 0xAB
    .endm

    .macro SIMPLEOS_ARM_SEMIHOST_RETURN
    bx lr
    .endm

    .macro SIMPLEOS_ARM_SEMIHOST_ARG_WRITE0
    mov r1, r0
    movs r0, #0x04
    .endm

    .macro SIMPLEOS_ARM_SEMIHOST_ARG_EXIT
    mov r1, r0
    movs r0, #0x18
    .endm

    .include "src/lib/nogc_async_mut_noalloc/baremetal/common/arm_semihost_trap.S"
    SIMPLEOS_ARM_SEMIHOST_TRAP simpleos_arm_semihost_call, simpleos_arm_semihost_write0, simpleos_arm_semihost_exit

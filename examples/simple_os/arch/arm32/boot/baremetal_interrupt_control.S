    .syntax unified
    .arm

    .macro SIMPLEOS_ARM_DISABLE_INTERRUPTS
    cpsid if
    .endm

    .macro SIMPLEOS_ARM_ENABLE_INTERRUPTS
    cpsie if
    .endm

    .macro SIMPLEOS_ARM_WAIT_FOR_INTERRUPT
    wfe
    .endm

    .macro SIMPLEOS_ARM_RETURN
    bx lr
    .endm

    .include "examples/simple_os/arch/common/baremetal_arm_interrupt_control.S"
    SIMPLEOS_ARM_INTERRUPT_CONTROL simpleos_arm32_interrupt_disable, simpleos_arm32_interrupt_enable, simpleos_arm32_wait_for_interrupt

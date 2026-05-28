    .macro SIMPLEOS_ARM_DISABLE_INTERRUPTS
    msr daifset, #0xf
    .endm

    .macro SIMPLEOS_ARM_ENABLE_INTERRUPTS
    msr daifclr, #0xf
    .endm

    .macro SIMPLEOS_ARM_WAIT_FOR_INTERRUPT
    wfe
    .endm

    .macro SIMPLEOS_ARM_RETURN
    ret
    .endm

    .include "examples/simple_os/arch/common/baremetal_arm_interrupt_control.S"
    SIMPLEOS_ARM_INTERRUPT_CONTROL simpleos_arm64_interrupt_disable, simpleos_arm64_interrupt_enable, simpleos_arm64_wait_for_interrupt

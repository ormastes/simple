    .section .text
    .align 2

    .global simpleos_arm64_interrupt_disable
    .type simpleos_arm64_interrupt_disable, %function
simpleos_arm64_interrupt_disable:
    msr daifset, #0xf
    ret
    .size simpleos_arm64_interrupt_disable, . - simpleos_arm64_interrupt_disable

    .global simpleos_arm64_interrupt_enable
    .type simpleos_arm64_interrupt_enable, %function
simpleos_arm64_interrupt_enable:
    msr daifclr, #0xf
    ret
    .size simpleos_arm64_interrupt_enable, . - simpleos_arm64_interrupt_enable

    .global simpleos_arm64_wait_for_interrupt
    .type simpleos_arm64_wait_for_interrupt, %function
simpleos_arm64_wait_for_interrupt:
    wfe
    ret
    .size simpleos_arm64_wait_for_interrupt, . - simpleos_arm64_wait_for_interrupt

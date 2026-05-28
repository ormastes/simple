    .syntax unified
    .section .text
    .arm
    .align 2

    .global simpleos_arm32_interrupt_disable
    .type simpleos_arm32_interrupt_disable, %function
simpleos_arm32_interrupt_disable:
    cpsid if
    bx lr
    .size simpleos_arm32_interrupt_disable, . - simpleos_arm32_interrupt_disable

    .global simpleos_arm32_interrupt_enable
    .type simpleos_arm32_interrupt_enable, %function
simpleos_arm32_interrupt_enable:
    cpsie if
    bx lr
    .size simpleos_arm32_interrupt_enable, . - simpleos_arm32_interrupt_enable

    .global simpleos_arm32_wait_for_interrupt
    .type simpleos_arm32_wait_for_interrupt, %function
simpleos_arm32_wait_for_interrupt:
    wfe
    bx lr
    .size simpleos_arm32_wait_for_interrupt, . - simpleos_arm32_wait_for_interrupt

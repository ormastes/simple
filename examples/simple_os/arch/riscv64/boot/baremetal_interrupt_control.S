    .section .text
    .align 2

    .global simpleos_rv64_interrupt_disable
    .type simpleos_rv64_interrupt_disable, @function
simpleos_rv64_interrupt_disable:
    csrci mstatus, 0x8
    ret
    .size simpleos_rv64_interrupt_disable, . - simpleos_rv64_interrupt_disable

    .global simpleos_rv64_interrupt_enable
    .type simpleos_rv64_interrupt_enable, @function
simpleos_rv64_interrupt_enable:
    csrsi mstatus, 0x8
    ret
    .size simpleos_rv64_interrupt_enable, . - simpleos_rv64_interrupt_enable

    .global simpleos_rv64_wait_for_interrupt
    .type simpleos_rv64_wait_for_interrupt, @function
simpleos_rv64_wait_for_interrupt:
    wfi
    ret
    .size simpleos_rv64_wait_for_interrupt, . - simpleos_rv64_wait_for_interrupt

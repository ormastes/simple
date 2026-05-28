    .section .text
    .align 2

    .global simpleos_rv32_semihost_call
    .type simpleos_rv32_semihost_call, @function
simpleos_rv32_semihost_call:
    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop
    ret
    .size simpleos_rv32_semihost_call, . - simpleos_rv32_semihost_call

    .global simpleos_rv32_semihost_write0
    .type simpleos_rv32_semihost_write0, @function
simpleos_rv32_semihost_write0:
    mv a1, a0
    li a0, 0x04
    tail simpleos_rv32_semihost_call
    .size simpleos_rv32_semihost_write0, . - simpleos_rv32_semihost_write0

    .global simpleos_rv32_semihost_exit
    .type simpleos_rv32_semihost_exit, @function
simpleos_rv32_semihost_exit:
    mv a1, a0
    li a0, 0x18
    tail simpleos_rv32_semihost_call
    .size simpleos_rv32_semihost_exit, . - simpleos_rv32_semihost_exit

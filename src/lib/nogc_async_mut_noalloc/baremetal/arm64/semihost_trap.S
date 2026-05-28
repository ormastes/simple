    .section .text
    .align 2

    .global simpleos_arm64_semihost_call
    .type simpleos_arm64_semihost_call, %function
simpleos_arm64_semihost_call:
    hlt #0xF000
    ret
    .size simpleos_arm64_semihost_call, . - simpleos_arm64_semihost_call

    .global simpleos_arm64_semihost_write0
    .type simpleos_arm64_semihost_write0, %function
simpleos_arm64_semihost_write0:
    mov x1, x0
    mov x0, #0x04
    b simpleos_arm64_semihost_call
    .size simpleos_arm64_semihost_write0, . - simpleos_arm64_semihost_write0

    .global simpleos_arm64_semihost_exit
    .type simpleos_arm64_semihost_exit, %function
simpleos_arm64_semihost_exit:
    mov x1, x0
    mov x0, #0x18
    b simpleos_arm64_semihost_call
    .size simpleos_arm64_semihost_exit, . - simpleos_arm64_semihost_exit

    .syntax unified
    .section .text
    .thumb
    .align 2

    .global simpleos_arm_semihost_call
    .type simpleos_arm_semihost_call, %function
simpleos_arm_semihost_call:
    bkpt 0xAB
    bx lr
    .size simpleos_arm_semihost_call, . - simpleos_arm_semihost_call

    .global simpleos_arm_semihost_write0
    .type simpleos_arm_semihost_write0, %function
simpleos_arm_semihost_write0:
    mov r1, r0
    movs r0, #0x04
    b simpleos_arm_semihost_call
    .size simpleos_arm_semihost_write0, . - simpleos_arm_semihost_write0

    .global simpleos_arm_semihost_exit
    .type simpleos_arm_semihost_exit, %function
simpleos_arm_semihost_exit:
    mov r1, r0
    movs r0, #0x18
    b simpleos_arm_semihost_call
    .size simpleos_arm_semihost_exit, . - simpleos_arm_semihost_exit

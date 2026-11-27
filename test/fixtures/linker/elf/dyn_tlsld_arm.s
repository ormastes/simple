@ Local-dynamic TLS access (R_ARM_TLS_LDM32 + R_ARM_TLS_LDO32); clang does not
@ emit LDM from C for ARM, so it is written out. getld() returns lv3 (= 2).
    .syntax unified
    .thumb
    .text
    .globl getld
    .type getld,%function
    .thumb_func
getld:
    push {r4, lr}
    ldr r0, .Lldm
.Lpc0:
    add r0, pc
    bl __tls_get_addr
    ldr r1, .Lldo
    ldr r0, [r0, r1]
    pop {r4, pc}
    .p2align 2
.Lldm:
    .word lv3(tlsldm) + (. - .Lpc0 - 4)
.Lldo:
    .word lv3(tlsldo)
    .section .tdata,"awT",%progbits
    .p2align 2
lv3:
    .word 2
